#!/usr/bin/env node
/* KARN LAN server — accounts, Elo, friends, notifications, saved matches,
   admin tools and metrics. Zero dependencies.
   Run:  node server.js   (optional: --port 8081)
   All data is stored in the ./data folder next to this file.
   THE FIRST ACCOUNT CREATED BECOMES THE ADMIN ACCOUNT.                    */
'use strict';
const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto'),os=require('os');

const argi=process.argv.indexOf('--port');
const PORT=argi>-1?+process.argv[argi+1]:8081;
const DIR=__dirname;
const DATA=path.join(DIR,'data');
fs.mkdirSync(DATA,{recursive:true});
const DBU=path.join(DATA,'users.json');
const DBM=path.join(DATA,'matches.json');
const DBX=path.join(DATA,'metrics.json');
const GAME=path.join(DIR,'karn.html');
const PNAMES=['White','Black'];

/* ---------- storage ---------- */
function readJSON(f){try{return JSON.parse(fs.readFileSync(f,'utf8'));}catch(e){return null;}}
let users=readJSON(DBU);
if(!users){ /* migrate from the old single-file layout if present */
  users=readJSON(path.join(DIR,'karn-users.json'))||{};
}
let saved=readJSON(DBM)||{};      /* finished match records */
let metrics=readJSON(DBX)||{firstStart:Date.now(),registrations:0,logins:0,gamesFinished:0,eventsRelayed:0};
const DBS=path.join(DATA,'misc.json');
let misc=readJSON(DBS)||{feedback:[],recov:{},fseq:1};
misc.support=misc.support||[];misc.smtp=misc.smtp||null;misc.tickets=misc.tickets||[];
misc.balance=misc.balance||null;misc.balV=misc.balV||0;
misc.pages=misc.pages||{custom:[],extends:{}};
function sanitizePages(pg){
  const out={custom:[],extends:{}};
  if(!pg||typeof pg!=='object')return out;
  const clean=list=>(Array.isArray(list)?list:[]).slice(0,12)
    .map(b=>({title:String((b&&b.title)||'').slice(0,60),body:String((b&&b.body)||'').slice(0,5000)}));
  for(const p of(Array.isArray(pg.custom)?pg.custom:[]).slice(0,8)){
    const id=String((p&&p.id)||'').toLowerCase();
    if(!/^[a-z0-9]{2,12}$/.test(id)||out.custom.some(x=>x.id===id))continue;
    out.custom.push({id,title:String(p.title||id).slice(0,20),
      icon:String(p.icon||'📄').slice(0,4),
      vis:['all','users','staff','admin'].includes(p.vis)?p.vis:'all',
      blocks:clean(p.blocks)});
  }
  for(const k of['rules','play'])
    if(pg.extends&&pg.extends[k])out.extends[k]=clean(pg.extends[k]);
  return out;
}
const num=(v,lo,hi,dflt)=>{const n=Math.round(+v);return Number.isFinite(n)?Math.max(lo,Math.min(hi,n)):dflt;};
function sanitizeBalance(b){
  if(!b||typeof b!=='object')return null;
  const out={bases:{},guns:{},rules:{}};
  for(const k of['L','M','H']){
    const src=(b.bases||{})[k]||{};
    out.bases[k]={spd:num(src.spd,1,6,1),hp:num(src.hp,1,8,1),ap:num(src.ap,0,6,1)};
  }
  const guns=b.guns||{};
  let n=0;
  for(const id in guns){
    if(!/^[a-z0-9]{2,8}$/.test(id)||++n>12)continue;
    const g=guns[id]||{};
    out.guns[id]={name:String(g.name||id).slice(0,20),
      ap:num(g.ap,0,6,1),rng:num(g.rng,1,8,1),dmg:num(g.dmg,0,9,1),
      arc:g.arc?1:0};
    if(g.light)out.guns[id].light=1;
    if(g.heavy)out.guns[id].heavy=1;
    if(g.lvl)out.guns[id].lvl=2;
  }
  const r=b.rules||{};
  out.rules={actions:num(r.actions,1,6,3),perPiece:num(r.perPiece,1,6,2),
    armySize:num(r.armySize,4,10,8),maxPerType:num(r.maxPerType,1,10,4),
    snHeavyBonus:num(r.snHeavyBonus,0,3,1),dgAhead:num(r.dgAhead,1,9,4),
    eloK:num(r.eloK,8,64,32),drawRound:num(r.drawRound,50,500,150)};
  return out;
}
for(const tk of misc.tickets){  /* migrate one-shot tickets to threads + guest keys */
  if(!tk.messages)tk.messages=[{by:tk.from,text:tk.body||'',ts:tk.ts}];
  if(!tk.key)tk.key=crypto.randomBytes(16).toString('hex');
}
function ticketLink(tk,req){
  return(typeof IS_TLS!=='undefined'&&IS_TLS?'https':'http')+'://'+
    ((req&&req.headers.host)||'localhost:'+PORT)+'/?ticket='+tk.key;
}
let nseq=1;
/* per-account login lockout (in memory) + emailed one-time login links */
const lockouts={};
const loginKeys={};
function maybeMailLoginLink(u,req){
  const lo=lockouts[u];
  if(!lo)return false;
  if(lo.mailed)return true;
  const x=users[u];
  if(!x||!x.email||!misc.smtp||!misc.smtp.host)return false;
  const k=crypto.randomBytes(20).toString('hex');
  loginKeys[k]={user:u,exp:Date.now()+15*60e3};
  const link=(typeof IS_TLS!=='undefined'&&IS_TLS?'https':'http')+'://'+
    (req.headers.host||'localhost:'+PORT)+'/?loginkey='+k;
  sendUserMail(u,'[KARN] One-time login link','Locked out? Here is a direct way in',
    `Someone (hopefully you) tried to log in to "${u}" too many times, so the\n`+
    `account is temporarily locked.\n\n`+
    `If it was you, use this one-time link to log straight in — it works once\n`+
    `and expires in 15 minutes:\n\n`+
    `    ${link}\n\n`+
    `Logging in this way clears the lock immediately.\n`+
    `If this wasn't you, your password held firm — but consider changing it\n`+
    `once you're back in (or ask staff/admin to help via Support).`);
  lo.mailed=true;
  return true;
}
function maskEmail(e){const i=e.indexOf('@');return e[0]+'***'+(i>-1?e.slice(i):'');}
/* minimal SMTP-over-SSL client (port 465, AUTH LOGIN — e.g. Gmail app password) */
function sendMail(to,subject,text){
  return new Promise((resolve,reject)=>{
    const cfg=misc.smtp||{};
    if(!cfg.host||!cfg.user)return reject(new Error('Email service not configured'));
    let sock;
    try{
      const port=+cfg.port||465;
      sock=cfg.plain    /* plain TCP for local relays / testing only */
        ?require('net').connect({host:cfg.host,port})
        :require('tls').connect({host:cfg.host,port,servername:cfg.host});
    }catch(e){return reject(e);}
    const from=cfg.from||cfg.user;
    const b64=s=>Buffer.from(String(s)).toString('base64');
    const steps=[
      {expect:220,send:'EHLO karnserver'},
      {expect:250,send:'AUTH LOGIN'},
      {expect:334,send:b64(cfg.user)},
      {expect:334,send:b64(cfg.pass)},
      {expect:235,send:`MAIL FROM:<${from}>`},
      {expect:250,send:`RCPT TO:<${to}>`},
      {expect:250,send:'DATA'},
      {expect:354,send:[`From: KARN <${from}>`,`To: <${to}>`,`Subject: ${subject}`,
        'MIME-Version: 1.0','Content-Type: text/plain; charset=utf-8','',text,'.'].join('\r\n')},
      {expect:250,send:'QUIT'},
      {expect:221,send:null}
    ];
    let idx=0,buf='',done=false;
    const nice=e=>{
      const m=String(e&&e.message||e);
      if(/ENOTFOUND|EAI_AGAIN/.test(m))return new Error('SMTP host not found — it must be a mail server name like smtp.gmail.com (not an email address)');
      if(/ECONNREFUSED/.test(m))return new Error('The mail server refused the connection — check the host and port (465)');
      if(/timeout/i.test(m))return new Error('The mail server did not respond — check the host, and that port 465 (SSL) is right for your provider');
      if(/535|534/.test(m))return new Error('Login refused by the mail server — check the email and app password (Google needs 2-step verification + an app password, not your normal password)');
      return e;
    };
    const finish=err=>{if(done)return;done=true;try{sock.destroy();}catch(_){}err?reject(nice(err)):resolve(true);};
    sock.setTimeout(10000,()=>finish(new Error('SMTP timeout')));
    sock.on('error',e=>finish(e));
    sock.on('data',d=>{
      buf+=d.toString();
      if(!/\r?\n$/.test(buf))return;          /* wait for a complete line */
      const lines=buf.split(/\r?\n/);
      for(let i=lines.length-1;i>=0;i--){
        const L=lines[i];
        if(!L)continue;
        if(/^\d{3} /.test(L)){
          const codeN=+L.slice(0,3);buf='';
          const st=steps[idx];
          if(!st)return finish();
          if(codeN!==st.expect)return finish(new Error('SMTP '+codeN+': '+L.slice(4,120)));
          idx++;
          if(st.send!=null)sock.write(st.send+'\r\n');
          else finish();
        }
        break;
      }
    });
  });
}
const ADMIN_NAMES=['rubenhillier'];   /* these usernames are ALWAYS admins */
for(const u in users){ /* ensure new fields exist on old accounts — never deletes anything */
  const x=users[u];
  x.friends=x.friends||[];x.reqIn=x.reqIn||[];x.reqOut=x.reqOut||[];
  x.blocked=x.blocked||[];x.matches=x.matches||[];
  x.notifs=(x.notifs||[]).map(n=>n.type?n:{...n,type:'info',from:null,data:null});
  x.private=!!x.private;x.admin=!!x.admin;x.staff=!!x.staff;
  x.banned=x.banned||null;x.flagged=x.flagged||null;
  x.emailPrefs=x.emailPrefs||{friendReq:true};
  if(ADMIN_NAMES.includes(u.toLowerCase())&&!x.admin){
    x.admin=true;
    console.log('granted admin to existing account:',u);
  }
}
if(Object.keys(users).length)setTimeout(()=>save(DBU,users),400); /* persist any admin grants */
const savers={};
function save(file,obj){
  if(savers[file])return;
  savers[file]=setTimeout(()=>{delete savers[file];
    try{fs.writeFileSync(file,JSON.stringify(obj,null,1));}catch(e){console.error('save failed:',e.message);}
  },250);
}
const saveU=()=>save(DBU,users),saveM=()=>save(DBM,saved),saveX=()=>save(DBX,metrics),saveS=()=>save(DBS,misc);

/* ============ ENCRYPTED CREDENTIAL VAULT (admin-only) ============
   Stores business email logins encrypted with AES-256-GCM. The key is
   derived from a master passphrase via scrypt and is NEVER written to disk;
   it lives only in memory for the duration of an unlocked admin session.
   The passphrase itself is never stored — losing it means the data is
   unrecoverable, which is the point.                                       */
const DBV=path.join(DATA,'vault.json');
let vaultFile=readJSON(DBV);          /* {salt, iv, tag, ct} or null */
const vaultKeys={};                   /* token -> derived key (Buffer)     */
function deriveVaultKey(pass,salt){return crypto.scryptSync(pass,salt,32,{N:16384,r:8,p:1});}
function vaultDecrypt(key){
  const iv=Buffer.from(vaultFile.iv,'hex'),tag=Buffer.from(vaultFile.tag,'hex');
  const d=crypto.createDecipheriv('aes-256-gcm',key,iv);
  d.setAuthTag(tag);
  const pt=Buffer.concat([d.update(Buffer.from(vaultFile.ct,'hex')),d.final()]);
  return JSON.parse(pt.toString('utf8'));
}
function vaultEncrypt(key,entries){
  const iv=crypto.randomBytes(12);
  const c=crypto.createCipheriv('aes-256-gcm',key,iv);
  const ct=Buffer.concat([c.update(Buffer.from(JSON.stringify(entries),'utf8')),c.final()]);
  vaultFile={v:1,salt:vaultFile.salt,iv:iv.toString('hex'),tag:c.getAuthTag().toString('hex'),ct:ct.toString('hex')};
  /* write synchronously — credentials must never be lost to a debounce window */
  fs.writeFileSync(DBV,JSON.stringify(vaultFile));
}
function vaultRedact(entries){
  return entries.map(e=>({id:e.id,label:e.label,email:e.email,notes:e.notes,updated:e.updated,hasPass:!!e.pass}));
}
function notifyAdmins(text){
  for(const u in users)if(users[u].admin)addNotif(u,{type:'info',text});
}
/* ---- outbound user email (professional template + delivery log) ---- */
const mailLog=[];
function mailTemplate(title,name,body,footer){
  return['KARN — BATTLEFIELD COMMAND','═'.repeat(46),'',title.toUpperCase(),'',
    `Hi ${name},`,'',body,'','─'.repeat(46),
    footer||'This is an automated message from your KARN game server.',
    'Please do not reply directly to this email.'].join('\n');
}
function sendUserMail(u,subject,title,body,footer){
  const x=users[u];
  if(!x||!x.email||!misc.smtp||!misc.smtp.host)return;
  sendMail(x.email,subject,mailTemplate(title,u,body,footer))
    .then(()=>{mailLog.unshift({to:maskEmail(x.email),subject,ok:true,ts:Date.now()});
      if(mailLog.length>25)mailLog.length=25;
      console.log('mail sent:',subject,'->',maskEmail(x.email));})
    .catch(e=>{mailLog.unshift({to:maskEmail(x.email),subject,ok:false,err:e.message,ts:Date.now()});
      if(mailLog.length>25)mailLog.length=25;
      console.error('mail failed:',subject,'->',u,':',e.message);});
}
function renameUser(old,neu){
  users[neu]=users[old];delete users[old];
  for(const u in users){const x=users[u];
    for(const k of['friends','reqIn','reqOut','blocked'])x[k]=x[k].map(n=>n===old?neu:n);
  }
  for(const t in sessions)if(sessions[t].user===old)sessions[t].user=neu;
  for(const id in saved){if(saved[id].host===old)saved[id].host=neu;if(saved[id].guest===old)saved[id].guest=neu;}
  for(const id in matches){if(matches[id].host===old)matches[id].host=neu;if(matches[id].guest===old)matches[id].guest=neu;}
  for(const e of queue)if(e.user===old)e.user=neu;
  for(const id in challenges){if(challenges[id].from===old)challenges[id].from=neu;if(challenges[id].to===old)challenges[id].to=neu;}
  for(const f of misc.feedback)if(f.from===old)f.from=neu;
  for(const c in misc.recov)if(misc.recov[c].user===old)misc.recov[c].user=neu;
  if(ADMIN_NAMES.includes(neu.toLowerCase()))users[neu].admin=true;
  saveU();saveM();saveS();
}

const sessions={};   /* token -> {user,exp} */
const matches={};    /* live matches        */
const challenges={}; /* pending challenges  */
const queue=[];      /* matchmaking queue: {user,elo,mode,ts,alive} */
let mseq=Date.now()%100000,cseq=1;

/* ---------- matchmaking ----------
   Pair players of similar Elo (within 150). After 10 seconds in the queue,
   pair with the closest-rated player available, however far apart.        */
function dequeue(u){const i=queue.findIndex(e=>e.user===u);if(i>-1)queue.splice(i,1);}
function createQueueMatch(a,b,mode){
  dequeue(a.user);dequeue(b.user);
  for(const e of[a,b]){const cur=activeMatchOf(e.user);if(cur&&cur.status==='open')delete matches[cur.id];}
  const white=Math.random()<0.5?a:b,black=white===a?b:a;
  const id=String(mseq++);
  matches[id]={id,host:white.user,guest:black.user,mode,status:'active',mid:randomMid(),
    events:[],result:null,started:Date.now(),last:Date.now()};
  console.log('matchmade',id,':',white.user,'('+white.elo+') vs',black.user,'('+black.elo+')','['+mode+']');
}
setInterval(function matchmake(){
  const now=Date.now();
  /* drop entries whose owner stopped polling (left/closed the page) */
  for(let i=queue.length-1;i>=0;i--)
    if(now-queue[i].alive>8000||!users[queue[i].user])queue.splice(i,1);
  for(const mode of['quick','setup']){
    let go=true;
    while(go){
      go=false;
      const q=queue.filter(e=>e.mode===mode);
      if(q.length<2)break;
      q.sort((a,b)=>a.ts-b.ts);           /* longest waiting first */
      const a=q[0],waited=now-a.ts;
      const cands=q.slice(1).filter(b=>!isBlocked(a.user,b.user));
      if(!cands.length)break;
      cands.sort((x,y)=>Math.abs(x.elo-a.elo)-Math.abs(y.elo-a.elo));
      const best=cands[0];
      if(Math.abs(best.elo-a.elo)<=150||waited>=10000){
        createQueueMatch(a,best,mode);
        go=true;
      }
    }
  }
},1000);
const SESS_TTL=7*24*3600e3;          /* sessions idle-expire after 7 days */

/* ---------- security: rate limiting ---------- */
const RATES={};
function rate(key,limit,win){
  const now=Date.now();
  let r=RATES[key];
  if(!r||now>r.reset)r=RATES[key]={n:0,reset:now+win};
  r.n++;
  return r.n<=limit;
}
setInterval(()=>{const now=Date.now();for(const k in RATES)if(RATES[k].reset<now)delete RATES[k];},60e3);
setInterval(()=>{ /* expire idle sessions, stale challenges + login links */
  const now=Date.now();
  for(const t in sessions)if(sessions[t].exp<now)delete sessions[t];
  for(const id in challenges)if(now-challenges[id].ts>5*60e3)delete challenges[id];
  for(const k in loginKeys)if(loginKeys[k].exp<now)delete loginKeys[k];
},60e3);

/* ---------- helpers ---------- */
function hashPass(pw,salt){salt=salt||crypto.randomBytes(12).toString('hex');
  return{salt,hash:crypto.scryptSync(pw,salt,32).toString('hex')};}
function newToken(){return crypto.randomBytes(24).toString('hex');}
function online(u){const now=Date.now();return Object.values(sessions).some(s=>s.user===u&&s.exp>now);}
function pub(u){const x=users[u];if(!x)return{user:u,elo:'?',deleted:true};
  return{user:u,elo:x.elo,wins:x.wins,losses:x.losses,draws:x.draws,games:x.games,
    created:x.created,private:x.private,online:online(u)};}
function addNotif(u,n){
  const x=users[u];if(!x)return;
  if(typeof n==='string')n={type:'info',text:n};
  x.notifs.unshift({id:nseq++,ts:Date.now(),read:false,type:n.type||'info',
    text:n.text,from:n.from||null,data:n.data||null});
  if(x.notifs.length>60)x.notifs.length=60;
  saveU();
}
function isBlocked(a,b){
  return(users[a]&&users[a].blocked.includes(b))||(users[b]&&users[b].blocked.includes(a));
}
function unfriend(a,b){
  for(const[p,q]of[[a,b],[b,a]]){
    const x=users[p];if(!x)continue;
    x.friends=x.friends.filter(n=>n!==q);
    x.reqIn=x.reqIn.filter(n=>n!==q);
    x.reqOut=x.reqOut.filter(n=>n!==q);
  }
}
function applyElo(aName,bName,scoreA){
  const A=users[aName],B=users[bName];
  const K=(misc.balance&&misc.balance.rules&&misc.balance.rules.eloK)||32;
  const Ea=1/(1+Math.pow(10,(B.elo-A.elo)/400));
  const dA=Math.round(K*(scoreA-Ea)),dB=-dA;
  A.elo+=dA;B.elo+=dB;A.games++;B.games++;
  if(scoreA===1){A.wins++;B.losses++;}
  else if(scoreA===0){A.losses++;B.wins++;}
  else{A.draws++;B.draws++;}
  saveU();
  return{[aName]:dA,[bName]:dB};
}
function randomMid(){
  const cols=[];
  while(cols.length<3){const c=Math.floor(Math.random()*8);if(!cols.includes(c))cols.push(c);}
  return{cols:cols.sort((a,b)=>a-b),flip:Math.random()<0.5};
}
function matchInfo(m,forUser){
  return{id:m.id,mode:m.mode,status:m.status,mid:m.mid,
    players:[pub(m.host),m.guest?pub(m.guest):null],
    you:forUser===m.host?0:forUser===m.guest?1:null,
    result:m.result||null,evCount:m.events.length};
}
function activeMatchOf(u){
  for(const id in matches){const m=matches[id];
    if((m.host===u||m.guest===u)&&m.status!=='done')return m;}
  return null;
}
function matchSummary(rec,viewer){
  return{id:rec.id,host:rec.host,guest:rec.guest,mode:rec.mode,
    winner:rec.result?rec.result.winner:null,resigned:rec.result?rec.result.resigned:null,
    ended:rec.ended,events:rec.events.length};
}
function finalizeMatch(m,winner,resignedSide){
  const score=winner==='draw'?0.5:(winner===0?1:0);
  const delta=applyElo(m.host,m.guest,score);
  m.result={winner,resigned:resignedSide??null,delta,
    elo:{[m.host]:users[m.host].elo,[m.guest]:users[m.guest].elo}};
  m.status='done';m.last=Date.now();
  /* save the record */
  saved[m.id]={id:m.id,host:m.host,guest:m.guest,mode:m.mode,mid:m.mid,
    events:m.events,result:{winner,resigned:resignedSide??null,delta},
    started:m.started,ended:Date.now()};
  for(const[u,side]of[[m.host,0],[m.guest,1]]){
    users[u].matches.unshift(m.id);
    if(users[u].matches.length>50)users[u].matches.length=50;
    const opp=side===0?m.guest:m.host,d=delta[u];
    addNotif(u,{type:'result',from:opp,data:{win:winner==='draw'?'draw':winner===side,matchId:m.id},
      text:winner==='draw'
        ?`Draw against ${opp} (${d>=0?'+':''}${d} Elo)`
        :winner===side
          ?`You defeated ${opp}${resignedSide!=null&&resignedSide!==side?' — they resigned':''} (+${d} Elo → ${users[u].elo})`
          :`You lost to ${opp}${resignedSide===side?' — you resigned':''} (${d} Elo → ${users[u].elo})`});
  }
  metrics.gamesFinished++;saveX();saveM();saveU();
  console.log('match',m.id,'result:',winner==='draw'?'draw':PNAMES[winner]);
}
setInterval(()=>{
  const now=Date.now();
  for(const id in matches){const m=matches[id];
    if(m.status==='open'&&now-m.last>10*60e3)delete matches[id];
    else if(m.status==='active'&&now-m.last>45*60e3)delete matches[id];
    else if(m.status==='done'&&now-m.last>15*60e3)delete matches[id];}
},60e3);

/* ---------- http plumbing ---------- */
const SEC_HEADERS={'X-Content-Type-Options':'nosniff','X-Frame-Options':'DENY','Referrer-Policy':'no-referrer'};
function json(res,code,obj){
  res.writeHead(code,{'Content-Type':'application/json',
    'Access-Control-Allow-Origin':'*',
    'Access-Control-Allow-Headers':'Content-Type, X-Token',
    'Access-Control-Allow-Methods':'GET, POST, OPTIONS',...SEC_HEADERS});
  res.end(JSON.stringify(obj));
}
function bad(res,msg,code){json(res,code||400,{error:msg});}
function readBody(req){
  return new Promise((resolve,reject)=>{
    let b='';
    req.on('data',c=>{b+=c;if(b.length>1e6)req.destroy();});
    req.on('end',()=>{try{resolve(b?JSON.parse(b):{});}catch(e){reject(e);}});
    req.on('error',reject);
  });
}
function findUser(name){
  const k=String(name||'').trim().toLowerCase();
  return Object.keys(users).find(n=>n.toLowerCase()===k)||null;
}

const TRUST_PROXY=process.argv.includes('--trust-proxy');
const handler=async(req,res)=>{
try{
  const url=new URL(req.url,'http://x');
  const p=url.pathname;
  if(req.method==='OPTIONS')return json(res,200,{});
  const ip=(TRUST_PROXY&&String(req.headers['x-forwarded-for']||'').split(',')[0].trim())
    ||req.socket.remoteAddress||'?';
  if(!rate(ip+':api',150,5000))return bad(res,'Too many requests — slow down',429);
  if(req.method==='GET'&&(p==='/'||p==='/karn.html')){
    let html;
    try{html=fs.readFileSync(GAME);}catch(e){return bad(res,'karn.html not found next to server.js',500);}
    res.writeHead(200,{'Content-Type':'text/html; charset=utf-8',...SEC_HEADERS,
      'Content-Security-Policy':"default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; frame-ancestors 'none'"});
    return res.end(html);
  }
  if(!p.startsWith('/api/')){res.writeHead(404,SEC_HEADERS);return res.end('not found');}
  const body=req.method==='POST'?await readBody(req):{};
  const token=req.headers['x-token']||'';
  let me=null;
  const sess=sessions[token];
  if(sess){
    if(sess.exp<Date.now())delete sessions[token];
    else{sess.exp=Date.now()+SESS_TTL;me=sess.user;}
  }

  /* ================= accounts ================= */
  if(p==='/api/register'&&req.method==='POST'){
    if(!rate(ip+':auth',25,5*60e3))return bad(res,'Too many attempts — try again in a few minutes',429);
    const u=String(body.user||'').trim(),pw=String(body.pass||'').slice(0,200);
    if(!/^[A-Za-z0-9_]{2,16}$/.test(u))return bad(res,'Username: 2-16 letters, numbers or _');
    if(pw.length<6)return bad(res,'Password must be at least 6 characters');
    if(findUser(u))return bad(res,'That username is taken');
    if(Object.keys(users).length>=2000)return bad(res,'Server is full');
    const first=Object.keys(users).length===0||ADMIN_NAMES.includes(u.toLowerCase());
    const{salt,hash}=hashPass(pw);
    users[u]={salt,hash,elo:1000,wins:0,losses:0,draws:0,games:0,created:Date.now(),
      admin:first,staff:false,private:false,banned:null,flagged:null,email:null,
      emailPrefs:{friendReq:true},
      friends:[],reqIn:[],reqOut:[],blocked:[],notifs:[],matches:[]};
    if(first)addNotif(u,{type:'info',text:'You are the ADMIN of this server — the Admin page is in your side menu.'});
    metrics.registrations++;saveX();saveU();
    const t=newToken();sessions[t]={user:u,exp:Date.now()+SESS_TTL};
    console.log('new account:',u,first?'(ADMIN)':'');
    return json(res,200,{token:t,profile:pub(u)});
  }
  if(p==='/api/login'&&req.method==='POST'){
    if(!rate(ip+':auth',25,5*60e3))return bad(res,'Too many attempts — try again in a few minutes',429);
    const u=findUser(body.user);
    if(!u){crypto.scryptSync('x','00'.repeat(12),32);return bad(res,'Wrong username or password',401);}
    const lo=lockouts[u];
    if(lo&&lo.until>Date.now()){
      const mailed=maybeMailLoginLink(u,req);
      return bad(res,mailed
        ?'Account temporarily locked — we emailed you a one-time login link (also check spam). Or wait 10 minutes.'
        :'Account temporarily locked after failed attempts — wait 10 minutes or use Support',429);
    }
    const x=users[u];
    const h=crypto.scryptSync(String(body.pass||'').slice(0,200),x.salt,32).toString('hex');
    const ok=h.length===x.hash.length&&crypto.timingSafeEqual(Buffer.from(h),Buffer.from(x.hash));
    if(!ok){
      const l=lockouts[u]=lockouts[u]||{n:0,until:0};
      l.n++;
      if(l.n>=8){
        l.until=Date.now()+10*60e3;l.n=0;l.mailed=false;
        const mailed=maybeMailLoginLink(u,req);
        return bad(res,mailed
          ?'Too many attempts — the account is locked for 10 minutes. We emailed you a one-time login link.'
          :'Too many attempts — the account is locked for 10 minutes. Use Support if you forgot your password.',429);
      }
      return bad(res,'Wrong username or password',401);
    }
    delete lockouts[u];
    if(x.banned)return bad(res,'This account has been banned'+(x.banned.reason?': '+x.banned.reason:''),403);
    const t=newToken();sessions[t]={user:u,exp:Date.now()+SESS_TTL};
    metrics.logins++;saveX();
    return json(res,200,{token:t,profile:pub(u)});
  }
  /* ----- current game balance (public — clients apply it at boot) ----- */
  if(p==='/api/balance'&&req.method==='GET')
    return json(res,200,{balance:misc.balance,v:misc.balV});
  if(p==='/api/pages'&&req.method==='GET')
    return json(res,200,{pages:misc.pages,v:misc.balV});

  /* ----- one-time login link (from lockout email) ----- */
  if(p==='/api/loginkey'&&req.method==='POST'){
    if(!rate(ip+':auth',25,5*60e3))return bad(res,'Too many attempts',429);
    const e=loginKeys[String(body.key||'')];
    if(!e||e.exp<Date.now()||!users[e.user])return bad(res,'Invalid or expired login link');
    delete loginKeys[String(body.key)];
    if(users[e.user].banned)return bad(res,'This account has been banned',403);
    delete lockouts[e.user];                 /* the link clears the lock */
    const t=newToken();sessions[t]={user:e.user,exp:Date.now()+SESS_TTL};
    metrics.logins++;saveX();
    console.log('one-time login link used by',e.user);
    return json(res,200,{token:t,profile:pub(e.user)});
  }

  /* ----- support: opens a real ticket (no login; never reveals if an account exists) ----- */
  if(p==='/api/support/request'&&req.method==='POST'){
    if(!rate(ip+':auth',25,5*60e3))return bad(res,'Too many attempts',429);
    const t=findUser(body.user);
    if(!t)return json(res,200,{ok:1,emailed:false});
    const msg=String(body.message||'').trim().slice(0,1000)||'Account help requested (no details given).';
    /* reuse a recent open support ticket instead of spamming new ones */
    let tk=misc.tickets.find(x=>x.to===t&&x.from==='support'&&x.status==='open'&&Date.now()-x.ts<3600e3);
    if(tk){
      if(tk.messages.length<50)tk.messages.push({by:t,text:msg,ts:Date.now()});
    }else{
      tk={id:misc.fseq++,to:t,from:'support',subject:'Support request from '+t,
        ts:Date.now(),status:'open',key:crypto.randomBytes(16).toString('hex'),
        messages:[{by:t,text:msg,ts:Date.now()}]};
      misc.tickets.unshift(tk);
      if(misc.tickets.length>200)misc.tickets.length=200;
    }
    if(!misc.support.some(s2=>s2.user===t&&!s2.done&&Date.now()-s2.ts<3600e3)){
      misc.support.unshift({id:misc.fseq++,user:t,ts:Date.now(),done:false});
      if(misc.support.length>100)misc.support.length=100;
    }
    saveS();
    notifyAdmins(`🛟 Support ticket #${tk.id} from ${t}: "${msg.slice(0,60)}${msg.length>60?'…':''}"`);
    const em=users[t].email;
    if(em&&misc.smtp&&misc.smtp.host){
      const code=crypto.randomBytes(4).toString('hex').toUpperCase();
      misc.recov[code]={user:t,by:'auto-email',exp:Date.now()+30*60e3};saveS();
      try{
        await sendMail(em,`[KARN Support] Ticket #${tk.id} — we're on it`,
`Hi ${t},

We received your support request and opened ticket #${tk.id}.

Your message:
${msg.split('\n').map(l=>'  '+l).join('\n')}

Follow the conversation and reply here — NO LOGIN NEEDED (works even if
you're locked out or suspended):

    ${ticketLink(tk,req)}

If this is about a lost password, you can also use this one-time recovery
code (30 minutes, single use) via "Account recovery" on the login screen:

    ${code}

The staff team will get back to you on the ticket.`);
        console.log('support ticket #'+tk.id,'emailed to',maskEmail(em));
        return json(res,200,{ok:1,emailed:true,hint:maskEmail(em),ticket:tk.id});
      }catch(e){
        delete misc.recov[code];saveS();
        console.error('support email failed:',e.message);
      }
    }
    return json(res,200,{ok:1,emailed:false,ticket:tk.id});
  }
  /* ----- guest ticket access via emailed link (no login) ----- */
  if(p==='/api/tickets/guest'&&req.method==='POST'){
    if(!rate(ip+':guest',60,5*60e3))return bad(res,'Too many attempts',429);
    const tk=misc.tickets.find(x=>x.key===String(body.key||''));
    if(!tk)return bad(res,'Invalid or expired ticket link',404);
    return json(res,200,{ticket:tk});
  }
  if(p==='/api/tickets/guest/reply'&&req.method==='POST'){
    if(!rate(ip+':guest',60,5*60e3))return bad(res,'Too many attempts',429);
    const tk=misc.tickets.find(x=>x.key===String(body.key||''));
    if(!tk)return bad(res,'Invalid or expired ticket link',404);
    if(tk.status!=='open')return bad(res,'This ticket is closed');
    const text=String(body.text||'').trim().slice(0,1000);
    if(text.length<2)return bad(res,'Write a message first');
    if(tk.messages.length>=50)return bad(res,'Ticket thread is full');
    tk.messages.push({by:tk.to,text,ts:Date.now()});
    saveS();
    if(users[tk.from])
      addNotif(tk.from,{type:'ticket',from:tk.to,data:{tid:tk.id},
        text:`${tk.to} replied to ticket #${tk.id} ("${tk.subject}")`});
    else notifyAdmins(`${tk.to} replied to ticket #${tk.id} ("${tk.subject}")`);
    return json(res,200,{ok:1,ticket:tk});
  }

  /* ----- account recovery (no login required; uses the auth rate bucket) ----- */
  if(p==='/api/recover/check'&&req.method==='POST'){
    if(!rate(ip+':auth',25,5*60e3))return bad(res,'Too many attempts',429);
    const rc=misc.recov[String(body.code||'').trim().toUpperCase()];
    if(!rc||rc.exp<Date.now()||!users[rc.user])return bad(res,'Invalid or expired recovery code');
    return json(res,200,{user:rc.user});
  }
  if(p==='/api/recover/complete'&&req.method==='POST'){
    if(!rate(ip+':auth',25,5*60e3))return bad(res,'Too many attempts',429);
    const codeK=String(body.code||'').trim().toUpperCase();
    const rc=misc.recov[codeK];
    if(!rc||rc.exp<Date.now()||!users[rc.user])return bad(res,'Invalid or expired recovery code');
    const pw=String(body.pass||'').slice(0,200);
    if(pw.length<6)return bad(res,'Password must be at least 6 characters');
    let uname=rc.user;
    const nn=String(body.newUser||'').trim();
    if(nn&&nn!==rc.user){
      if(!/^[A-Za-z0-9_]{2,16}$/.test(nn))return bad(res,'Username: 2-16 letters, numbers or _');
      if(findUser(nn))return bad(res,'That username is taken');
      renameUser(rc.user,nn);uname=nn;
    }
    const{salt,hash}=hashPass(pw);
    users[uname].salt=salt;users[uname].hash=hash;
    delete misc.recov[codeK];
    saveU();saveS();
    notifyAdmins(`Account recovery completed for ${uname}`);
    const t=newToken();sessions[t]={user:uname,exp:Date.now()+SESS_TTL};
    console.log('account recovered:',uname);
    return json(res,200,{token:t,profile:pub(uname)});
  }
  if(!me||!users[me])return bad(res,'Not logged in',401);
  const M=users[me];
  if(M.banned){delete sessions[token];return bad(res,'This account has been banned',403);}
  const STAFF=M.admin||M.staff;
  if(p==='/api/logout'){delete sessions[token];delete vaultKeys[token];dequeue(me);return json(res,200,{ok:1});}
  if(p==='/api/me')return json(res,200,{profile:pub(me)});
  if(p==='/api/profile'&&req.method==='POST'){
    if(typeof body.private==='boolean'){M.private=body.private;saveU();}
    if(body.email!==undefined){
      const em=String(body.email||'').trim().slice(0,254);
      if(em&&!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(em))return bad(res,'That does not look like an email address');
      M.email=em||null;saveU();
    }
    if(typeof body.emailFriendReq==='boolean'){M.emailPrefs.friendReq=body.emailFriendReq;saveU();}
    return json(res,200,{ok:1,private:M.private,email:M.email||'',emailPrefs:M.emailPrefs});
  }

  /* ================= lobby ================= */
  if(p==='/api/lobby'){
    /* privacy: only the TOP 10 are visible — nobody can scout the full player list */
    const players=Object.keys(users).filter(u=>!users[u].banned).map(pub).sort((a,b)=>b.elo-a.elo).slice(0,10);
    const open=Object.values(matches).filter(m=>m.status==='open'&&!isBlocked(m.host,me))
      .map(m=>({id:m.id,host:m.host,hostElo:users[m.host].elo,mode:m.mode}));
    const mine=activeMatchOf(me);
    const qe=queue.find(e=>e.user===me);
    if(qe)qe.alive=Date.now();          /* heartbeat while queued */
    return json(res,200,{players,open,match:mine?matchInfo(mine,me):null,
      queue:{waiting:qe?Date.now()-qe.ts:null,mode:qe?qe.mode:null,size:queue.length},
      me:{...pub(me),admin:M.admin,staff:M.staff,privateFlag:M.private,email:M.email||'',
        emailFriendReq:M.emailPrefs.friendReq!==false,
        unread:M.notifs.filter(n=>!n.read).length,reqIn:M.reqIn.length,balV:misc.balV,
        latest:M.notifs.slice(0,6),
        chIn:Object.values(challenges).filter(c=>c.to===me).map(c=>c.id)}});
  }
  /* ----- matchmaking queue ----- */
  if(p==='/api/queue'&&req.method==='POST'){
    const cur=activeMatchOf(me);
    if(cur&&cur.status==='active')return bad(res,'You are already in a match');
    if(cur)delete matches[cur.id];
    dequeue(me);
    queue.push({user:me,elo:users[me].elo,mode:body.mode==='setup'?'setup':'quick',
      ts:Date.now(),alive:Date.now()});
    return json(res,200,{ok:1});
  }
  if(p==='/api/queue/cancel'&&req.method==='POST'){dequeue(me);return json(res,200,{ok:1});}
  /* ----- challenges ----- */
  if(p==='/api/challenge'&&req.method==='POST'){
    const t=findUser(body.user);
    if(!t||t===me)return bad(res,'No such player');
    if(!online(t))return bad(res,'That player is offline');
    if(isBlocked(me,t))return bad(res,'Cannot challenge this player');
    if(Object.values(challenges).some(c=>c.from===me&&c.to===t))return bad(res,'Challenge already pending');
    if(Object.values(challenges).filter(c=>c.from===me).length>=5)return bad(res,'Too many pending challenges');
    const id='c'+(cseq++);
    const mode=body.mode==='setup'?'setup':'quick';
    challenges[id]={id,from:me,to:t,mode,ts:Date.now()};
    addNotif(t,{type:'challenge',from:me,data:{cid:id,mode},
      text:`${me} (${users[me].elo}) challenged you to a ${mode==='setup'?'full-setup':'quick'} match`});
    return json(res,200,{ok:1,cid:id});
  }
  if(p==='/api/challenge/accept'&&req.method==='POST'){
    const c=challenges[String(body.cid)];
    if(!c||c.to!==me)return bad(res,'Challenge expired');
    if(!users[c.from])return bad(res,'Challenger is gone');
    const myCur=activeMatchOf(me),theirCur=activeMatchOf(c.from);
    if(myCur&&myCur.status==='active')return bad(res,'You are already in a match');
    if(theirCur&&theirCur.status==='active')return bad(res,'Challenger is busy in another match');
    if(myCur)delete matches[myCur.id];
    if(theirCur)delete matches[theirCur.id];
    dequeue(me);dequeue(c.from);
    delete challenges[c.id];
    const id=String(mseq++);
    matches[id]={id,host:c.from,guest:me,mode:c.mode,status:'active',mid:randomMid(),
      events:[],result:null,started:Date.now(),last:Date.now()};
    addNotif(c.from,{type:'info',text:`${me} accepted your challenge — to battle!`});
    console.log('challenge match',id,':',c.from,'vs',me);
    return json(res,200,matchInfo(matches[id],me));
  }
  if(p==='/api/challenge/decline'&&req.method==='POST'){
    const c=challenges[String(body.cid)];
    if(c&&c.to===me){
      delete challenges[c.id];
      addNotif(c.from,{type:'info',text:`${me} declined your challenge`});
    }
    return json(res,200,{ok:1});
  }
  if(p==='/api/host'&&req.method==='POST'){
    const cur=activeMatchOf(me);
    if(cur&&cur.status==='active')return bad(res,'You are already in a match');
    if(cur)delete matches[cur.id];
    const id=String(mseq++);
    matches[id]={id,host:me,guest:null,mode:body.mode==='setup'?'setup':'quick',
      status:'open',mid:randomMid(),events:[],result:null,started:Date.now(),last:Date.now()};
    return json(res,200,{id});
  }
  if(p==='/api/host/cancel'&&req.method==='POST'){
    const cur=activeMatchOf(me);
    if(cur&&cur.status==='open')delete matches[cur.id];
    return json(res,200,{ok:1});
  }
  if(p==='/api/join'&&req.method==='POST'){
    const m=matches[String(body.id)];
    if(!m||m.status!=='open')return bad(res,'Match no longer available');
    if(m.host===me)return bad(res,'You cannot join your own match');
    if(isBlocked(m.host,me))return bad(res,'Match no longer available');
    const cur=activeMatchOf(me);
    if(cur&&cur.status==='active')return bad(res,'You are already in a match');
    m.guest=me;m.status='active';m.started=Date.now();m.last=Date.now();
    console.log('match',m.id,':',m.host,'vs',m.guest,'('+m.mode+')');
    return json(res,200,matchInfo(m,me));
  }

  /* ================= notifications ================= */
  if(p==='/api/notifs'&&req.method==='GET')
    return json(res,200,{notifs:M.notifs,reqIn:M.reqIn,
      chIn:Object.values(challenges).filter(c=>c.to===me).map(c=>c.id)});
  if(p==='/api/notifs/read'&&req.method==='POST'){
    M.notifs.forEach(n=>n.read=true);saveU();
    return json(res,200,{ok:1});
  }

  /* ================= friends & blocking ================= */
  if(p==='/api/friends'&&req.method==='GET'){
    return json(res,200,{
      friends:M.friends.filter(u=>users[u]).map(pub),
      reqIn:M.reqIn.filter(u=>users[u]),
      reqOut:M.reqOut.filter(u=>users[u]),
      blocked:M.blocked.filter(u=>users[u])});
  }
  if(p==='/api/friends/request'&&req.method==='POST'){
    const t=findUser(body.user);
    if(!t)return bad(res,'No such player');
    if(t===me)return bad(res,"That's you, commander");
    if(M.friends.includes(t))return bad(res,'Already friends');
    if(M.blocked.includes(t))return bad(res,'You have blocked this player');
    if(isBlocked(me,t))return bad(res,'Cannot send a request to this player');
    if(M.reqOut.includes(t))return bad(res,'Request already sent');
    if(M.reqIn.includes(t)){ /* they already asked us — instant friendship */
      unfriend(me,t);
      M.friends.push(t);users[t].friends.push(me);
      addNotif(t,{type:'friendok',from:me,text:`${me} accepted your friend request`});
      saveU();return json(res,200,{ok:1,accepted:true});
    }
    M.reqOut.push(t);users[t].reqIn.push(me);
    addNotif(t,{type:'friendreq',from:me,text:`${me} sent you a friend request`});
    if(users[t].emailPrefs.friendReq!==false)
      sendUserMail(t,`[KARN] ${me} sent you a friend request`,'New friend request',
        `${me} (Elo ${users[me].elo}) wants to be your friend on KARN.\n\n`+
        `Log in and open your Notifications to accept or decline.`,
        'You can turn off friend-request emails on your Profile page.');
    saveU();return json(res,200,{ok:1});
  }
  if(p==='/api/friends/accept'&&req.method==='POST'){
    const t=findUser(body.user);
    if(!t||!M.reqIn.includes(t))return bad(res,'No request from that player');
    unfriend(me,t);
    M.friends.push(t);users[t].friends.push(me);
    addNotif(t,{type:'friendok',from:me,text:`${me} accepted your friend request`});
    saveU();return json(res,200,{ok:1});
  }
  if(p==='/api/friends/decline'&&req.method==='POST'){
    const t=findUser(body.user);
    if(t){M.reqIn=M.reqIn.filter(n=>n!==t);if(users[t])users[t].reqOut=users[t].reqOut.filter(n=>n!==me);saveU();}
    return json(res,200,{ok:1});
  }
  if(p==='/api/friends/remove'&&req.method==='POST'){
    const t=findUser(body.user);
    if(t){unfriend(me,t);saveU();}
    return json(res,200,{ok:1});
  }
  if(p==='/api/friends/block'&&req.method==='POST'){
    const t=findUser(body.user);
    if(!t||t===me)return bad(res,'No such player');
    unfriend(me,t);
    if(!M.blocked.includes(t))M.blocked.push(t);
    saveU();return json(res,200,{ok:1});
  }
  if(p==='/api/friends/unblock'&&req.method==='POST'){
    const t=findUser(body.user);
    if(t){M.blocked=M.blocked.filter(n=>n!==t);saveU();}
    return json(res,200,{ok:1});
  }

  /* ================= feedback (any user) ================= */
  if(p==='/api/feedback'&&req.method==='POST'){
    const text=String(body.text||'').trim().slice(0,1000);
    if(text.length<3)return bad(res,'Feedback is empty');
    misc.feedback.unshift({id:misc.fseq++,from:me,text,ts:Date.now()});
    if(misc.feedback.length>200)misc.feedback.length=200;
    saveS();
    notifyAdmins(`📬 New feedback from ${me}: "${text.slice(0,60)}${text.length>60?'…':''}"`);
    return json(res,200,{ok:1});
  }

  /* ================= staff tools ================= */
  if(p.startsWith('/api/staff/')){
    if(!STAFF)return bad(res,'Staff only',403);
    const t=findUser(body.user);
    if(p==='/api/staff/recovery'&&req.method==='POST'){
      if(!t)return bad(res,'No such player');
      if(users[t].admin&&!M.admin)return bad(res,'Staff cannot reset an admin account');
      const code=crypto.randomBytes(4).toString('hex').toUpperCase();
      misc.recov[code]={user:t,by:me,exp:Date.now()+30*60e3};
      saveS();
      notifyAdmins(`🔑 ${me} created a recovery code for ${t}`);
      console.log('recovery code for',t,'created by',me);
      return json(res,200,{code,user:t,expMins:30});
    }
    if(p==='/api/staff/setPass'&&req.method==='POST'){
      if(!t)return bad(res,'No such player');
      if((users[t].admin||users[t].staff)&&!M.admin)return bad(res,'Staff cannot change staff or admin passwords');
      if(String(body.pass||'').length<6)return bad(res,'Password must be at least 6 characters');
      const{salt,hash}=hashPass(String(body.pass).slice(0,200));
      users[t].salt=salt;users[t].hash=hash;
      addNotif(t,{type:'info',text:'Your password was changed by a staff member'});
      saveU();
      return json(res,200,{ok:1});
    }
    if(p==='/api/staff/tag'&&req.method==='POST'){
      if(!t)return bad(res,'No such player');
      users[t].flagged={by:me,note:String(body.note||'').slice(0,200),ts:Date.now()};
      saveU();
      notifyAdmins(`🏷 ${me} tagged ${t} for review${body.note?' — "'+String(body.note).slice(0,80)+'"':''}`);
      return json(res,200,{ok:1});
    }
    /* ---- ticket system ---- */
    if(p==='/api/staff/ticket'&&req.method==='POST'){
      if(!t)return bad(res,'No such player');
      const subject=String(body.subject||'').trim().slice(0,120);
      const msg=String(body.message||'').trim().slice(0,2000);
      if(!subject||msg.length<3)return bad(res,'A ticket needs a subject and a message');
      const tk={id:misc.fseq++,to:t,from:me,subject,body:msg,ts:Date.now(),status:'open',
        key:crypto.randomBytes(16).toString('hex'),
        messages:[{by:me,text:msg,ts:Date.now()}]};
      misc.tickets.unshift(tk);
      if(misc.tickets.length>200)misc.tickets.length=200;
      saveS();
      addNotif(t,{type:'ticket',from:me,data:{tid:tk.id},
        text:`Ticket #${tk.id} — ${subject}`});
      sendUserMail(t,`[KARN Support] Ticket #${tk.id} — ${subject}`,
        `Support ticket #${tk.id}`,
        `A member of the KARN staff team has opened a ticket regarding your account.\n\n`+
        `  Subject:  ${subject}\n`+
        `  Opened:   ${new Date(tk.ts).toUTCString()}\n`+
        `  Handled by: ${me}${M.admin?' (Administrator)':' (Staff)'}\n\n`+
        `Message:\n\n${msg.split('\n').map(l=>'  '+l).join('\n')}\n\n`+
        `Read the conversation and reply here — no login needed:\n\n    ${ticketLink(tk,req)}\n\n`+
        `You can also open it from your KARN notifications.`,
        'Questions? Use the Feedback button in the game — it goes straight to the admin.');
      console.log('ticket #'+tk.id,'to',t,'from',me);
      return json(res,200,{ok:1,id:tk.id});
    }
    if(p==='/api/staff/tickets'&&req.method==='GET')
      return json(res,200,{tickets:misc.tickets.slice(0,15)});
    if(p==='/api/staff/ticket/close'&&req.method==='POST'){
      const tk=misc.tickets.find(x=>x.id===+body.id);
      if(tk&&tk.status!=='closed'){
        tk.status='closed';tk.closedBy=me;saveS();
        addNotif(tk.to,{type:'ticket',from:me,data:{tid:tk.id},
          text:`Ticket #${tk.id} ("${tk.subject}") was closed by ${me}`});
      }
      return json(res,200,{ok:1});
    }
    if(p==='/api/staff/ticket/reopen'&&req.method==='POST'){
      const tk=misc.tickets.find(x=>x.id===+body.id);
      if(tk&&tk.status==='closed'){
        tk.status='open';saveS();
        addNotif(tk.to,{type:'ticket',from:me,data:{tid:tk.id},
          text:`Ticket #${tk.id} ("${tk.subject}") was reopened by ${me}`});
      }
      return json(res,200,{ok:1});
    }
    return bad(res,'Unknown staff endpoint',404);
  }
  /* users can read tickets addressed to them (staff can read any) */
  if(p==='/api/ticket'&&req.method==='GET'){
    const tk=misc.tickets.find(x=>x.id===+url.searchParams.get('id'));
    if(!tk)return bad(res,'Ticket not found',404);
    if(tk.to!==me&&tk.from!==me&&!STAFF)return bad(res,'Not your ticket',403);
    return json(res,200,{ticket:tk,canReply:tk.status==='open',isStaff:STAFF});
  }
  /* both sides of a ticket can carry the conversation forward */
  if(p==='/api/ticket/reply'&&req.method==='POST'){
    const tk=misc.tickets.find(x=>x.id===+body.id);
    if(!tk)return bad(res,'Ticket not found',404);
    if(tk.to!==me&&tk.from!==me&&!STAFF)return bad(res,'Not your ticket',403);
    if(tk.status!=='open')return bad(res,'This ticket is closed — a staff member can reopen it');
    const text=String(body.text||'').trim().slice(0,1000);
    if(text.length<2)return bad(res,'Write a message first');
    if(!tk.messages)tk.messages=[{by:tk.from,text:tk.body||'',ts:tk.ts}]; /* safety migration */
    if(tk.messages.length>=50)return bad(res,'Ticket thread is full');
    tk.messages.push({by:me,text,ts:Date.now()});
    saveS();
    if(me===tk.to){
      /* player replied -> tell the staff member (or admins if they're gone) */
      if(users[tk.from])
        addNotif(tk.from,{type:'ticket',from:me,data:{tid:tk.id},
          text:`${me} replied to ticket #${tk.id} ("${tk.subject}")`});
      else notifyAdmins(`${me} replied to ticket #${tk.id} ("${tk.subject}")`);
    }else{
      /* staff replied -> tell (and email) the player */
      addNotif(tk.to,{type:'ticket',from:me,data:{tid:tk.id},
        text:`${me} replied to ticket #${tk.id} ("${tk.subject}")`});
      sendUserMail(tk.to,`[KARN Support] Re: Ticket #${tk.id} — ${tk.subject}`,
        `New reply on ticket #${tk.id}`,
        `${me} has replied to your support ticket.\n\n`+
        `  Ticket:   #${tk.id} — ${tk.subject}\n`+
        `  Replied:  ${new Date().toUTCString()}\n\n`+
        `Message:\n\n${text.split('\n').map(l=>'  '+l).join('\n')}\n\n`+
        `Read the conversation and reply here — no login needed:\n\n    ${ticketLink(tk,req)}\n\n`+
        `Or open it from your KARN notifications.`,
        'You can reply from the ticket in the game or via the link above.');
    }
    return json(res,200,{ok:1,ticket:tk});
  }

  /* ================= profiles & match records ================= */
  if(p==='/api/user'&&req.method==='GET'){
    const t=findUser(url.searchParams.get('name'));
    if(!t)return bad(res,'No such player',404);
    const X=users[t];
    const allowed=t===me||M.admin||!X.private;
    return json(res,200,{profile:pub(t),
      isFriend:M.friends.includes(t),reqOut:M.reqOut.includes(t),reqIn:M.reqIn.includes(t),
      iBlocked:M.blocked.includes(t),
      matches:allowed?X.matches.filter(id=>saved[id]).map(id=>matchSummary(saved[id],me)):null});
  }
  if(p==='/api/matchrec'&&req.method==='GET'){
    const rec=saved[String(url.searchParams.get('id'))];
    if(!rec)return bad(res,'Match not found',404);
    const involved=rec.host===me||rec.guest===me;
    const anyPublic=(users[rec.host]&&!users[rec.host].private)||(users[rec.guest]&&!users[rec.guest].private);
    if(!involved&&!M.admin&&!anyPublic)return bad(res,'This match is private',403);
    return json(res,200,{rec});
  }

  /* ================= admin ================= */
  if(p.startsWith('/api/admin/')){
    if(!M.admin)return bad(res,'Admin only',403);
    if(p==='/api/admin/metrics'&&req.method==='GET'){
      const players=Object.keys(users).map(pub).sort((a,b)=>b.elo-a.elo);
      return json(res,200,{metrics:{
        uptimeMs:Date.now()-BOOT,serverStart:BOOT,firstStart:metrics.firstStart,
        totalUsers:Object.keys(users).length,
        onlineNow:new Set(Object.values(sessions).filter(s=>s.exp>Date.now()).map(s=>s.user)).size,
        registrations:metrics.registrations,logins:metrics.logins,
        gamesFinished:metrics.gamesFinished,eventsRelayed:metrics.eventsRelayed,
        savedMatches:Object.keys(saved).length,
        openMatches:Object.values(matches).filter(m=>m.status==='open').length,
        activeMatches:Object.values(matches).filter(m=>m.status==='active').length,
        feedbackCount:misc.feedback.length,
        smtp:misc.smtp?{host:misc.smtp.host,user:misc.smtp.user,from:misc.smtp.from||misc.smtp.user}:null,
        mailLog:mailLog.slice(0,10)},
        users:players.map(pl=>({...pl,admin:users[pl.user].admin,staff:users[pl.user].staff,
          banned:users[pl.user].banned||null,flagged:users[pl.user].flagged||null})),
        recent:Object.values(saved).sort((a,b)=>b.ended-a.ended).slice(0,15).map(r=>matchSummary(r)),
        support:misc.support.filter(s=>!s.done).slice(0,20)
          .map(s=>({...s,emailLinked:!!(users[s.user]&&users[s.user].email)}))});
    }
    if(p==='/api/admin/smtp'&&req.method==='POST'){
      let host=String(body.host||'').trim();
      const smtpUser=String(body.user||'').trim();
      if(!host&&!smtpUser){misc.smtp=null;saveS();return json(res,200,{ok:1,configured:false});}
      if(host.includes('@'))
        return bad(res,'The SMTP host must be a server name, not an email address. For Gmail and Google Workspace domains use smtp.gmail.com — or just leave the host blank and I will use it automatically.');
      if(!smtpUser||!smtpUser.includes('@'))
        return bad(res,'Enter the full email address you are sending from');
      if(!host)host='smtp.gmail.com';   /* Google-managed mail (gmail + custom Google domains) */
      misc.smtp={host,port:+body.port||465,user:smtpUser,plain:!!body.plain,
        pass:body.pass?String(body.pass).replace(/\s+/g,''):(misc.smtp?misc.smtp.pass:''),
        from:String(body.from||'').trim()||smtpUser};
      if(!misc.smtp.pass)return bad(res,'Enter the app password');
      saveS();
      console.log('email service linked:',misc.smtp.user,'via',misc.smtp.host);
      return json(res,200,{ok:1,configured:true,host});
    }
    if(p==='/api/admin/smtpTest'&&req.method==='POST'){
      const to=String(body.to||'').trim();
      if(!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(to))return bad(res,'Enter a valid email address to send the test to');
      try{await sendMail(to,'KARN email service test','Your KARN server can send email. Recovery codes will work.');}
      catch(e){return bad(res,'Test failed: '+e.message);}
      return json(res,200,{ok:1});
    }
    if(p==='/api/admin/emailCode'&&req.method==='POST'){
      const t=findUser(body.user);
      if(!t)return bad(res,'No such player');
      const em=users[t].email;
      if(!em)return bad(res,'That player has no recovery email linked');
      const code=crypto.randomBytes(4).toString('hex').toUpperCase();
      misc.recov[code]={user:t,by:me,exp:Date.now()+30*60e3};saveS();
      try{
        await sendMail(em,'KARN account recovery code',
          `Hi ${t},\n\nAn admin sent you a recovery code:\n\n    ${code}\n\nUse "Account recovery" on the login screen. Expires in 30 minutes.`);
      }catch(e){delete misc.recov[code];saveS();return bad(res,'Email failed: '+e.message);}
      for(const s2 of misc.support)if(s2.user===t)s2.done=true;
      saveS();
      return json(res,200,{ok:1,hint:maskEmail(em)});
    }
    if(p==='/api/admin/balance'&&req.method==='POST'){
      misc.balance=sanitizeBalance(body.balance);
      misc.balV++;saveS();
      console.log('game balance updated by',me,misc.balance?'(custom)':'(defaults)');
      return json(res,200,{ok:1,balance:misc.balance,v:misc.balV});
    }
    if(p==='/api/admin/pages'&&req.method==='POST'){
      misc.pages=sanitizePages(body.pages);
      misc.balV++;saveS();
      console.log('site pages updated by',me,'-',misc.pages.custom.length,'custom tab(s)');
      return json(res,200,{ok:1,pages:misc.pages,v:misc.balV});
    }
    if(p==='/api/admin/balance/reset'&&req.method==='POST'){
      misc.balance=null;misc.balV++;saveS();
      console.log('game balance reset to defaults by',me);
      return json(res,200,{ok:1,v:misc.balV});
    }
    if(p==='/api/admin/support/resolve'&&req.method==='POST'){
      for(const s2 of misc.support)if(s2.id===+body.id)s2.done=true;
      saveS();
      return json(res,200,{ok:1});
    }

    /* ---- encrypted credential vault (admin only) ---- */
    if(p==='/api/admin/vault/status'&&req.method==='GET')
      return json(res,200,{exists:!!vaultFile,unlocked:!!vaultKeys[token]});
    if(p==='/api/admin/vault/setup'&&req.method==='POST'){
      /* create the vault with a fresh master passphrase (only if none exists) */
      if(vaultFile)return bad(res,'Vault already exists — unlock it instead');
      const pass=String(body.pass||'');
      if(pass.length<8)return bad(res,'Master passphrase must be at least 8 characters');
      const salt=crypto.randomBytes(16);
      vaultFile={v:1,salt:salt.toString('hex'),iv:'',tag:'',ct:''};
      const key=deriveVaultKey(pass,salt);
      vaultEncrypt(key,[]);
      vaultKeys[token]=key;
      console.log('credential vault created by',me);
      return json(res,200,{ok:1,unlocked:true});
    }
    if(p==='/api/admin/vault/unlock'&&req.method==='POST'){
      if(!vaultFile)return bad(res,'No vault yet — set one up first');
      if(!rate(ip+':vault',10,5*60e3))return bad(res,'Too many attempts — wait a few minutes',429);
      const key=deriveVaultKey(String(body.pass||''),Buffer.from(vaultFile.salt,'hex'));
      try{vaultDecrypt(key);}catch(e){return bad(res,'Wrong master passphrase',401);}
      vaultKeys[token]=key;
      return json(res,200,{ok:1,unlocked:true});
    }
    if(p==='/api/admin/vault/lock'&&req.method==='POST'){delete vaultKeys[token];return json(res,200,{ok:1});}
    /* everything below requires an unlocked key held in memory for this session */
    if(p.startsWith('/api/admin/vault/')){
      const key=vaultKeys[token];
      if(!key)return bad(res,'Vault is locked',403);
      let entries;
      try{entries=vaultDecrypt(key);}catch(e){delete vaultKeys[token];return bad(res,'Vault is locked',403);}
      if(p==='/api/admin/vault/list')                 /* redacted: no passwords */
        return json(res,200,{entries:vaultRedact(entries)});
      if(p==='/api/admin/vault/reveal'&&req.method==='POST'){
        const e=entries.find(x=>x.id===String(body.id));
        if(!e)return bad(res,'Not found');
        return json(res,200,{pass:e.pass||''});
      }
      if(p==='/api/admin/vault/save'&&req.method==='POST'){
        const label=String(body.label||'').trim().slice(0,80);
        const email=String(body.email||'').trim().slice(0,254);
        const pass=body.pass!=null?String(body.pass).slice(0,256):null;
        const notes=String(body.notes||'').slice(0,500);
        if(!label&&!email)return bad(res,'Give the entry a label or email');
        if(body.id){
          const e=entries.find(x=>x.id===String(body.id));
          if(!e)return bad(res,'Not found');
          e.label=label;e.email=email;e.notes=notes;e.updated=Date.now();
          if(pass!=null&&pass!=='')e.pass=pass;         /* blank = keep existing */
        }else{
          entries.push({id:crypto.randomBytes(6).toString('hex'),label,email,
            pass:pass||'',notes,updated:Date.now()});
        }
        vaultEncrypt(key,entries);
        return json(res,200,{ok:1,entries:vaultRedact(entries)});
      }
      if(p==='/api/admin/vault/delete'&&req.method==='POST'){
        entries=entries.filter(x=>x.id!==String(body.id));
        vaultEncrypt(key,entries);
        return json(res,200,{ok:1,entries:vaultRedact(entries)});
      }
      return bad(res,'Unknown vault endpoint',404);
    }
    if(p==='/api/admin/feedback'&&req.method==='GET')return json(res,200,{feedback:misc.feedback});
    if(p==='/api/admin/feedback/delete'&&req.method==='POST'){
      misc.feedback=misc.feedback.filter(f=>f.id!==+body.id);saveS();
      return json(res,200,{ok:1});
    }
    if(p==='/api/admin/setStaff'&&req.method==='POST'){
      const t=findUser(body.user);
      if(!t)return bad(res,'No such player');
      if(users[t].admin)return bad(res,'Admins already have full powers');
      users[t].staff=!!body.staff;saveU();
      addNotif(t,{type:'info',text:body.staff
        ?'🧰 You have been made STAFF — the Staff page is now in your side menu'
        :'Your staff role was removed'});
      return json(res,200,{ok:1});
    }
    if(p==='/api/admin/ban'&&req.method==='POST'){
      const t=findUser(body.user);
      if(!t)return bad(res,'No such player');
      if(users[t].admin)return bad(res,'Cannot ban an admin');
      users[t].banned={by:me,reason:String(body.reason||'').slice(0,140),ts:Date.now()};
      sendUserMail(t,'[KARN] Your account has been suspended','Account suspended',
        `Your KARN account "${t}" has been suspended by the server administrator.\n\n`+
        (body.reason?`Reason given:\n    ${String(body.reason).slice(0,140)}\n\n`:'')+
        `You will not be able to log in while the suspension is active.\n`+
        `If you believe this is a mistake, contact the server administrator.`);
      for(const tk in sessions)if(sessions[tk].user===t)delete sessions[tk];
      dequeue(t);
      const cur=activeMatchOf(t);
      if(cur&&cur.status==='open')delete matches[cur.id];
      for(const id in challenges)if(challenges[id].from===t||challenges[id].to===t)delete challenges[id];
      saveU();console.log('BAN',t,'by',me,body.reason?('('+body.reason+')'):'');
      return json(res,200,{ok:1});
    }
    if(p==='/api/admin/unban'&&req.method==='POST'){
      const t=findUser(body.user);
      if(!t)return bad(res,'No such player');
      users[t].banned=null;saveU();
      return json(res,200,{ok:1});
    }
    if(p==='/api/admin/untag'&&req.method==='POST'){
      const t=findUser(body.user);
      if(t){users[t].flagged=null;saveU();}
      return json(res,200,{ok:1});
    }
    if(p==='/api/admin/edit'&&req.method==='POST'){
      const t=findUser(body.user);
      if(!t)return bad(res,'No such player');
      if(users[t].admin&&t!==me)return bad(res,'Cannot edit another admin');
      if(body.elo!=null&&body.elo!==''){
        const e=Math.round(+body.elo);
        if(!(e>=100&&e<=3500))return bad(res,'Elo must be 100-3500');
        users[t].elo=e;
      }
      let name=t;
      const nn=String(body.newName||'').trim();
      if(nn&&nn!==t){
        if(!/^[A-Za-z0-9_]{2,16}$/.test(nn))return bad(res,'Username: 2-16 letters, numbers or _');
        if(findUser(nn))return bad(res,'That username is taken');
        renameUser(t,nn);name=nn;
        addNotif(name,{type:'info',text:'An admin changed your username to '+name});
      }
      saveU();
      return json(res,200,{ok:1,user:name});
    }
    if(p==='/api/admin/deleteUser'&&req.method==='POST'){
      const t=findUser(body.user);
      if(!t)return bad(res,'No such player');
      if(users[t].admin)return bad(res,'Cannot delete an admin account');
      delete users[t];
      for(const tk in sessions)if(sessions[tk].user===t)delete sessions[tk];
      for(const id in challenges)if(challenges[id].from===t||challenges[id].to===t)delete challenges[id];
      for(const u in users){const x=users[u];
        x.friends=x.friends.filter(n=>n!==t);x.reqIn=x.reqIn.filter(n=>n!==t);
        x.reqOut=x.reqOut.filter(n=>n!==t);x.blocked=x.blocked.filter(n=>n!==t);}
      saveU();console.log('admin',me,'deleted user',t);
      return json(res,200,{ok:1});
    }
    if(p==='/api/admin/setPass'&&req.method==='POST'){
      const t=findUser(body.user);
      if(!t)return bad(res,'No such player');
      if(String(body.pass||'').length<4)return bad(res,'Password must be at least 4 characters');
      const{salt,hash}=hashPass(String(body.pass));
      users[t].salt=salt;users[t].hash=hash;
      addNotif(t,{type:'info',text:'An admin changed your password'});
      saveU();console.log('admin',me,'changed password of',t);
      return json(res,200,{ok:1});
    }
    if(p==='/api/admin/deleteMatch'&&req.method==='POST'){
      const id=String(body.id);
      if(saved[id]){delete saved[id];
        for(const u in users)users[u].matches=users[u].matches.filter(x=>x!==id);
        saveM();saveU();}
      return json(res,200,{ok:1});
    }
  }

  /* ================= live match relay ================= */
  const mm=p.match(/^\/api\/match\/(\w+)(?:\/(\w+))?$/);
  if(mm){
    const m=matches[mm[1]];
    if(!m)return bad(res,'Match not found',404);
    if(m.host!==me&&m.guest!==me)return bad(res,'Not your match',403);
    const side=m.host===me?0:1;
    const sub=mm[2]||'';
    if(!sub&&req.method==='GET'){
      const since=+(url.searchParams.get('since')||0);
      m.last=Date.now();
      return json(res,200,{...matchInfo(m,me),events:m.events.slice(since)});
    }
    if(sub==='event'&&req.method==='POST'){
      if(m.status!=='active')return bad(res,'Match is not active');
      if(m.events.length>=4000)return bad(res,'Match event limit reached');
      const ev={n:m.events.length+1,by:side,type:String(body.type||'').slice(0,20),data:body.data??null};
      m.events.push(ev);m.last=Date.now();
      metrics.eventsRelayed++;
      return json(res,200,{n:ev.n});
    }
    if(sub==='result'&&req.method==='POST'){
      if(m.status==='done')return json(res,200,{result:m.result});
      const w=body.winner;
      if(w!==0&&w!==1&&w!=='draw')return bad(res,'Bad winner');
      finalizeMatch(m,w,null);
      return json(res,200,{result:m.result});
    }
    if(sub==='resign'&&req.method==='POST'){
      if(m.status==='done')return json(res,200,{result:m.result});
      finalizeMatch(m,1-side,side);
      return json(res,200,{result:m.result});
    }
    if(sub==='abort'&&req.method==='POST'){
      /* cancelling during setup: no Elo change, no record */
      if(m.status!=='active')return json(res,200,{ok:1});
      if(m.events.some(e=>e.type==='action'))return bad(res,'The battle has started — resign instead');
      const other=side===0?m.guest:m.host;
      delete matches[m.id];
      addNotif(other,{type:'info',text:`${me} cancelled the match during setup`});
      console.log('match',m.id,'aborted by',me);
      return json(res,200,{ok:1,aborted:true});
    }
  }
  return bad(res,'Unknown endpoint',404);
}catch(e){
  console.error(e);
  try{bad(res,'Server error',500);}catch(_){}
}
};
/* HTTPS if a certificate is provided:  node server.js --cert cert.pem --key key.pem */
const ci=process.argv.indexOf('--cert'),ki=process.argv.indexOf('--key');
const IS_TLS=ci>-1&&ki>-1;
if(IS_TLS)SEC_HEADERS['Strict-Transport-Security']='max-age=31536000';
const server=IS_TLS
  ?require('https').createServer({cert:fs.readFileSync(process.argv[ci+1]),key:fs.readFileSync(process.argv[ki+1])},handler)
  :http.createServer(handler);
const BOOT=Date.now();
server.listen(PORT,'0.0.0.0',()=>{
  console.log('');
  console.log('  ██╗  KARN battle server running');
  console.log('');
  console.log('  On this computer:  http://localhost:'+PORT+'/');
  const nets=os.networkInterfaces();
  for(const name in nets)for(const ni of nets[name]){
    if(ni.family==='IPv4'&&!ni.internal)
      console.log('  On your network:   http://'+ni.address+':'+PORT+'/   <- give this to friends');
  }
  console.log('');
  console.log('  Data is stored in the ./data folder. First account created = ADMIN.');
  console.log('  Press Ctrl+C to stop.');
});
