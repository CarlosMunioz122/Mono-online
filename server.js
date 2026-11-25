'use strict';
const http=require('http'),fs=require('fs'),path=require('path');
const {WebSocketServer}=require('ws');
/* ===== MONO · lógica compartida (cliente local + servidor) ===== */
const TAU=Math.PI*2;
const clamp=(v,a,b)=>v<a?a:v>b?b:v;
const angd=(a,b)=>{let d=(a-b)%TAU;if(d>Math.PI)d-=TAU;if(d<-Math.PI)d+=TAU;return d};
const MAPS=[
  {id:0,n:'Backrooms',e:'🟨',cell:7,N:11,loops:.3,h:3.2},
  {id:1,n:'Minas',e:'⛏️',cell:5,N:15,loops:.07,h:2.8},
  {id:2,n:'Hospital',e:'🏥',cell:6,N:12,loops:.18,h:3}];
const RULES={match:210,ping:20,freeze:8,count:5,end:9,maxP:12,atkR:2.7,atkCd:1.1,botWalk:4.1,botRun:5.2};
function mulberry(a){return()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
function genMaze(mid,seed){
  const M=MAPS[mid],N=M.N,C=M.cell,r=mulberry(seed>>>0),op=new Uint8Array(N*N),vis=new Uint8Array(N*N);
  const D=[[0,-1,1,4],[1,0,2,8],[0,1,4,1],[-1,0,8,2]],st=[0];vis[0]=1;
  while(st.length){const c=st[st.length-1],x=c%N,y=c/N|0,nb=[];
    for(const d of D){const nx=x+d[0],ny=y+d[1];if(nx>=0&&ny>=0&&nx<N&&ny<N&&!vis[ny*N+nx])nb.push(d)}
    if(!nb.length){st.pop();continue}
    const d=nb[r()*nb.length|0],n=(y+d[1])*N+x+d[0];op[c]|=d[2];op[n]|=d[3];vis[n]=1;st.push(n)}
  for(let y=0;y<N;y++)for(let x=0;x<N;x++){
    if(x<N-1&&!(op[y*N+x]&2)&&r()<M.loops){op[y*N+x]|=2;op[y*N+x+1]|=8}
    if(y<N-1&&!(op[y*N+x]&4)&&r()<M.loops){op[y*N+x]|=4;op[(y+1)*N+x]|=1}}
  const T=.6,w=[];
  for(let y=0;y<=N;y++)for(let x=0;x<N;x++){const wall=y===0||y===N||!(op[y*N+x]&1);if(wall)w.push([(x+.5)*C,y*C,C+T,T])}
  for(let x=0;x<=N;x++)for(let y=0;y<N;y++){const wall=x===0||x===N||!(op[y*N+x]&8);if(wall)w.push([x*C,(y+.5)*C,T,C+T])}
  return{N,C,op,w,T,mid,h:M.h}
}
function bfs(mz,from){const N=mz.N,dist=new Int16Array(N*N).fill(-1),par=new Int16Array(N*N).fill(-1),q=[from];dist[from]=0;
  for(let i=0;i<q.length;i++){const c=q[i],o=mz.op[c];
    for(const [b,n] of [[o&1,c-N],[o&2,c+1],[o&4,c+N],[o&8,c-1]])if(b&&dist[n]<0){dist[n]=dist[c]+1;par[n]=c;q.push(n)}}
  return{dist,par}}
const cellOf=(mz,x,z)=>clamp(z/mz.C|0,0,mz.N-1)*mz.N+clamp(x/mz.C|0,0,mz.N-1);
const cellPos=(mz,c)=>[(c%mz.N+.5)*mz.C,((c/mz.N|0)+.5)*mz.C];
const r2=v=>Math.round(v*100)/100;
const cleanName=s=>String(s||'Mono').replace(/[^\p{L}\p{N} _.-]/gu,'').trim().slice(0,14)||'Mono';
const cleanSkin=s=>{s=s||{};const i=(v,m)=>Number.isInteger(v)&&v>=0&&v<m?v:0;return{f:i(s.f,8),h:i(s.h,7),g:i(s.g,4)}};
function createSim(code,send){
  const S={lobT:0,code,ph:'lobby',players:new Map(),ct:0,pt:0,pg:0,fz:0,et:0,mz:null,map:0,bot:null,killer:null,seed:0,dirty:true,acc:0};
  const P=()=>[...S.players.values()];
  const pickMax=a=>{const m=Math.max(...a),c=a.map((v,i)=>v===m?i:-1).filter(i=>i>=0);return c[Math.random()*c.length|0]};
  const info=()=>({t:'li',ph:S.ph,ps:P().map(p=>({id:p.id,nm:p.nm,sk:p.sk,rd:p.rd?1:0,vm:p.vm,vk:p.vk,k:S.killer===p.id?1:0})),
    vc:[0,1,2].map(i=>P().filter(p=>p.vm===i).length),kc:[0,1].map(i=>P().filter(p=>p.vk===i).length)});
  function startMsg(late){const sp={};for(const p of P())if(p.role)sp[p.id]=[r2(p.x),r2(p.z)];
    return{t:'start',map:S.map,seed:S.seed,kid:S.killer,bot:S.bot?[r2(S.bot.x),r2(S.bot.z)]:0,pt:S.pt,fz:S.fz,sp,late:late?1:0}}
  function join(id,nm,sk){
    if(S.players.size>=RULES.maxP)return false;
    const p={id,nm:cleanName(nm),sk:cleanSkin(sk),x:0,y:0,z:0,a:0,an:0,al:1,rd:0,vm:-1,vk:-1,cd:0,role:''};
    S.players.set(id,p);send(id,{t:'welcome',id,code:S.code});
    if(S.ph==='play'||S.ph==='end'){p.al=0;p.role='';send(id,startMsg(true))}
    S.dirty=true;return true}
  function leave(id){
    const p=S.players.get(id);if(!p)return;S.players.delete(id);S.dirty=true;
    if(S.ph==='play'&&S.killer===id){S.killer=null;S.bot={x:p.x,z:p.z,a:p.a,an:0,cd:2,tg:null,rt:0};send(null,{t:'kbot',bot:[r2(p.x),r2(p.z)]})}
    if(S.players.size===0&&S.ph!=='lobby'){S.ph='lobby';S.killer=null;S.bot=null}}
  function kill(v,kid){v.al=0;send(null,{t:'kill',id:v.id,k:kid,x:r2(v.x),y:r2(v.y),z:r2(v.z)})}
  function atk(p){
    if(S.ph!=='play'||p.id!==S.killer||S.fz>0||p.cd>0)return;p.cd=RULES.atkCd;send(null,{t:'atk',id:p.id});
    let best=null,bd=1e9;for(const v of P()){if(v.role!=='s'||!v.al)continue;const dx=v.x-p.x,dz=v.z-p.z,d=Math.hypot(dx,dz);
      if(d<=RULES.atkR&&Math.abs(angd(p.a,Math.atan2(dx,dz)))<1.15&&d<bd){bd=d;best=v}}
    if(best)kill(best,p.id)}
  function start(){
    const ps=P();if(!ps.length)return;
    const mc=[0,0,0],kc=[0,0];ps.forEach(p=>{if(p.vm>=0)mc[p.vm]++;if(p.vk>=0)kc[p.vk]++});
    S.map=pickMax(mc);let kt=pickMax(kc);if(ps.length<2)kt=1;
    S.seed=Math.random()*4294967296>>>0;S.mz=genMaze(S.map,S.seed);const mz=S.mz,n=mz.N*mz.N;
    const s0=Math.random()*n|0,bf=bfs(mz,s0);let kc0=s0,far=-1;for(let i=0;i<n;i++)if(bf.dist[i]>far){far=bf.dist[i];kc0=i}
    const near=[];for(let i=0;i<n;i++)if(bf.dist[i]>=0&&bf.dist[i]<=3)near.push(i);near.sort(()=>Math.random()-.5);
    S.killer=kt===0?ps[Math.random()*ps.length|0].id:null;let k=0;
    for(const p of ps){p.al=1;p.cd=0;p.rd=0;p.role=p.id===S.killer?'k':'s';p.an=0;
      const c=p.role==='k'?kc0:near[k++%near.length],pos=cellPos(mz,c);p.x=pos[0];p.z=pos[1];p.y=0}
    S.bot=null;if(!S.killer){const pos=cellPos(mz,kc0);S.bot={x:pos[0],z:pos[1],a:0,an:0,cd:2,tg:null,rt:0}}
    S.ph='play';S.pt=RULES.match;S.pg=RULES.ping;S.fz=RULES.freeze;S.dirty=true;send(null,startMsg(false))}
  function end(w){S.ph='end';S.et=RULES.end;S.dirty=true;send(null,{t:'end',w,kid:S.killer})}
  function toLobby(){S.ph='lobby';S.killer=null;S.bot=null;for(const p of P()){p.al=1;p.role='';p.rd=0;p.vm=-1;p.vk=-1;p.an=0}S.lobT=.6;S.dirty=true;send(null,{t:'lobby'})}
  function botTick(dt){
    const b=S.bot;if(!b||S.fz>0)return;b.cd-=dt;b.rt-=dt;
    const surv=P().filter(p=>p.role==='s'&&p.al);if(!surv.length){b.an=0;return}
    const mz=S.mz,bc=cellOf(mz,b.x,b.z),bf=bfs(mz,bc);
    if(b.rt<=0||!S.players.get(b.tg)||!S.players.get(b.tg).al){b.rt=.4;let bd=1e9;for(const p of surv){const d=bf.dist[cellOf(mz,p.x,p.z)];if(d<bd){bd=d;b.tg=p.id}}}
    const tp=S.players.get(b.tg);if(!tp)return;const tc=cellOf(mz,tp.x,tp.z);let tx,tz;
    if(bc===tc){tx=tp.x;tz=tp.z}else{let c=tc,g=0;while(bf.par[c]!==bc&&bf.par[c]>=0&&g++<400)c=bf.par[c];const q=cellPos(mz,c);tx=q[0];tz=q[1]}
    const dx=tx-b.x,dz=tz-b.z,d=Math.hypot(dx,dz),pd=Math.hypot(tp.x-b.x,tp.z-b.z),run=pd<14,sp=run?RULES.botRun:RULES.botWalk;
    if(d>.05){const s=Math.min(d,sp*dt);b.x+=dx/d*s;b.z+=dz/d*s;b.a=Math.atan2(dx,dz)}b.an=run?2:1;
    if(pd<1.9&&b.cd<=0){b.cd=RULES.atkCd+.4;b.a=Math.atan2(tp.x-b.x,tp.z-b.z);send(null,{t:'atk',id:'bot'});kill(tp,'bot')}}
  function playTick(dt){
    S.pt-=dt;if(S.fz>0)S.fz=Math.max(0,S.fz-dt);for(const p of S.players.values())if(p.cd>0)p.cd-=dt;
    S.pg-=dt;if(S.pg<=0){S.pg+=RULES.ping;send(null,{t:'rv',l:P().filter(p=>p.role==='s'&&p.al).map(p=>[p.id,r2(p.x),r2(p.z)])})}
    botTick(dt);
    const surv=P().filter(p=>p.role==='s');
    if(surv.length&&!surv.some(p=>p.al))end('k');
    else if(S.pt<=0)end('s');
    else if(!surv.length&&S.players.size)end('k')}
  function snap(){return{t:'s',ph:S.ph,ct:r2(S.ct),pt:r2(S.pt),pg:r2(S.pg),fz:r2(S.fz),
    ps:P().map(p=>[p.id,r2(p.x),r2(p.y),r2(p.z),r2(p.a),p.an,p.al]),b:S.bot?[r2(S.bot.x),r2(S.bot.z),r2(S.bot.a),S.bot.an]:0}}
  function msg(id,m){
    const p=S.players.get(id);if(!p||!m||typeof m!=='object')return;const num=v=>typeof v==='number'&&isFinite(v);
    switch(m.t){
      case'st':if(S.ph==='play'&&(!p.al||S.pt>RULES.match-.6))break;if(S.ph==='lobby'&&S.lobT>0)break;if(num(m.x)&&num(m.z)){p.x=clamp(m.x,-500,500);p.z=clamp(m.z,-500,500);p.y=num(m.y)?clamp(m.y,-5,20):0;p.a=num(m.a)?m.a:0;p.an=m.an===1||m.an===2?m.an:0}break;
      case'vote':if(S.ph!=='lobby'&&S.ph!=='count')break;if(Number.isInteger(m.m)&&m.m>=0&&m.m<3)p.vm=m.m;if(Number.isInteger(m.k)&&m.k>=0&&m.k<2)p.vk=m.k;S.dirty=true;break;
      case'ready':if(S.ph!=='lobby'&&S.ph!=='count')break;p.rd=m.v?1:0;S.dirty=true;break;
      case'skin':p.sk=cleanSkin(m.sk);S.dirty=true;break;
      case'name':p.nm=cleanName(m.nm);S.dirty=true;break;
      case'atk':atk(p);break;
      case'chat':{const s=String(m.m||'').replace(/[\u0000-\u001f]/g,'').slice(0,80).trim();if(s)send(null,{t:'chat',id,nm:p.nm,m:s});break}}}
  function tick(dt){
    if(S.lobT>0)S.lobT-=dt;
    if(S.ph==='lobby'||S.ph==='count'){const ps=P(),all=ps.length>0&&ps.every(p=>p.rd);
      if(all){if(S.ph==='lobby'){S.ph='count';S.ct=RULES.count;S.dirty=true}else{S.ct-=dt;if(S.ct<=0)start()}}
      else if(S.ph==='count'){S.ph='lobby';S.dirty=true}}
    else if(S.ph==='play')playTick(dt);
    else if(S.ph==='end'){S.et-=dt;if(S.et<=0)toLobby()}
    if(S.dirty){S.dirty=false;send(null,info())}
    S.acc+=dt;if(S.acc>=1/15){S.acc=0;if(S.players.size)send(null,snap())}}
  return{join,leave,msg,tick,S,size:()=>S.players.size}
}

const PORT=process.env.PORT||3000;
let html='';try{html=fs.readFileSync(path.join(__dirname,'index.html'),'utf8').replace('<!--SERVER-->','<script>window.MONO_SERVER=1</script>')}catch(e){html='<h1>Falta index.html</h1>'}
const srv=http.createServer((q,r)=>{
  if(q.url.startsWith('/healthz')){r.writeHead(200);return r.end('ok')}
  r.writeHead(200,{'content-type':'text/html; charset=utf-8','cache-control':'no-cache'});r.end(html)});
const wss=new WebSocketServer({server:srv,path:'/ws',maxPayload:4096});
const rooms=new Map();let nid=1;
function getRoom(code){let R=rooms.get(code);if(R)return R;
  R={code,socks:new Map()};
  R.sim=createSim(code,(to,m)=>{const s=JSON.stringify(m);if(to==null){for(const w of R.socks.values())if(w.readyState===1)w.send(s)}else{const w=R.socks.get(to);if(w&&w.readyState===1)w.send(s)}});
  rooms.set(code,R);return R}
wss.on('connection',ws=>{
  const id=nid++;let room=null;ws.isAlive=true;ws.on('pong',()=>ws.isAlive=true);
  ws.on('message',d=>{let m;try{m=JSON.parse(d)}catch(e){return}
    if(!room){if(m.t!=='join')return;const code=String(m.code||'').toUpperCase().replace(/[^A-Z0-9]/g,'').slice(0,10);if(code.length<2)return;
      const R=getRoom(code);R.socks.set(id,ws);
      if(!R.sim.join(id,m.nm,m.sk)){R.socks.delete(id);if(!R.socks.size)rooms.delete(code);ws.send(JSON.stringify({t:'err',m:'La sala está llena'}));return}
      room=R;return}
    room.sim.msg(id,m)});
  ws.on('close',()=>{if(!room)return;room.sim.leave(id);room.socks.delete(id);if(!room.socks.size)rooms.delete(room.code)})});
setInterval(()=>{for(const R of rooms.values())R.sim.tick(1/15)},1000/15);
setInterval(()=>{for(const w of wss.clients){if(!w.isAlive){w.terminate();continue}w.isAlive=false;try{w.ping()}catch(e){}}},25000);
srv.listen(PORT,()=>console.log('MONO en puerto '+PORT));
