
(()=>{'use strict';
const $=s=>document.querySelector(s);
const clamp=(x,a,b)=>Math.min(b,Math.max(a,x));
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const rng=a=>()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296};

/* ================= state ================= */
const KEY='latent.v4';
const S=Object.assign({dev:1,fx:1,brd:0,fmt:0,cat:'all',lens:1,film:0,ev:0,date:true,len:24,frame:0,shots:0,opened:false,burnNext:0},(()=>{try{return JSON.parse(localStorage.getItem(KEY)||'{}')}catch(e){return{}}})());
const save=()=>{try{localStorage.setItem(KEY,JSON.stringify(S))}catch(e){}};
let armed=true,busy=false,live=false,dirty=true,backOpen=false,labOpen=false,rewinding=false,sheetOn=false,SC=1,SH=812;
const FOFF=24; /* the frame sits this far above screen centre, leaving room for the lens strip */
let FA=2/3,LAND=false,SW=390,DEV=false; /* 35mm frame: w/h (portrait <1, landscape >1) */
const faOf=(i,l)=>l?1/FORMATS[i].asp:FORMATS[i].asp;
const wearOf=n=>1-Math.exp(-n/90);
const BURN=[0,.3,.65,1];

/* ================= data ================= */
const LENSES=[
 {mm:28, name:'DS-WIDE 1:3.5', zoom:1.22,k:.20, vig:.55,ca:.40,soft:.35,swirl:0, glow:.10},
 {mm:55, name:'DS-SOL 1:1.8',  zoom:1.60,k:.02, vig:.38,ca:.15,soft:.20,swirl:0, glow:.15},
 {mm:58, name:'ROSSA-ZAR 1:2',     zoom:1.70,k:0,   vig:.50,ca:.20,soft:.95,swirl:1, glow:.25},
 {mm:85, name:'SOFT-DS 1:2.8',    zoom:2.10,k:-.03,vig:.30,ca:.10,soft:.25,swirl:0, glow:.95},
 {mm:135,name:'TELE-DS 1:3.5',    zoom:2.60,k:-.05,vig:.25,ca:.25,soft:.10,swirl:0, glow:.10},
];
const FB={contrast:1,lift:.02,sat:1,sh:[0,0,0],hi:[0,0,0],grain:.05,gres:900,hal:.2,glow:.12,roll:1.3,fog:0,fogC:[.03,.03,.03],mono:0,mw:[.34,.5,.16],leak:.02,dust:.03,dark:0,halo:[1,.4,.2],gn:[1,1,1],gm:[1,1,1],vigx:0};
const mk=(name,iso,type,cat,c,ink,o)=>Object.assign({name,iso,type,cat,c,ink},FB,o);
const FILMS=[
 mk('CPM35',200,'90s compact, honey','colour','#d99a3a','#2a1a04',{preset:'CPM35'}),
 mk('FXN-R',400,'japanese film','colour','#3f8a6a','#eafff2',{preset:'FXN_R'}),
 mk('CCD-04',100,'early digicam','colour','#5a5ac8','#eeeeff',{preset:'CCD_2004'}),
 mk('800T',800,'night cine, red halation','cine','#2a76a0','#fff3e2',{preset:'CINESTILL_800T'}),
 mk('DAY',200,'your scans, daylight','mine','#e0a37c','#2a1408',{preset:'MINE_DAY'}),
 mk('NIGHT',800,'your scans, stage light','mine','#7a2bc4','#f4e8ff',{preset:'MINE_NIGHT'}),
 mk('MONO',400,'contrast b&w','mine','#d4d2cc','#121212',{preset:'MINE_BW'}),
];
if(S.fv!==3){S.film=0;S.cat='all';S.fv=3}
const FORMATS=[
 {n:'FULL',s:'36\u00d724',asp:2/3,crop:1},
 {n:'CROP',s:'APS-C \u00d71.5',asp:2/3,crop:1.5},
 {n:'HALF',s:'18\u00d724',asp:3/4,crop:1},
 {n:'6\u00d77',s:'4:5',asp:4/5,crop:1},
 {n:'SQUARE',s:'6\u00d76',asp:1,crop:1},
];

/* ================= sound engine v2: modal / contact synthesis =================
   A click is not a beep: it is a tiny impact (a 1–2 ms noise transient) exciting a few damped resonances
   (metal rings high and long, plastic low and dull, the camera body adds a short room). Every play is
   slightly randomised, so ten shots never sound like one sample. Your own recordings override any sound. */
let AC,NB,MASTER;
const rnd=a=>(Math.random()*2-1)*a, J=(x,p=.03)=>x*(1+rnd(p));
function ac(){try{if(!AC){AC=new(window.AudioContext||window.webkitAudioContext)();const sr=AC.sampleRate;NB=AC.createBuffer(1,sr,sr);const d=NB.getChannelData(0);for(let i=0;i<sr;i++)d[i]=Math.random()*2-1;
  MASTER=AC.createGain();MASTER.gain.value=.55;const hp=AC.createBiquadFilter();hp.type='highpass';hp.frequency.value=70;
  const comp=AC.createDynamicsCompressor();comp.threshold.value=-12;comp.ratio.value=3;comp.attack.value=.001;comp.release.value=.08;
  const conv=AC.createConvolver(),L=Math.floor(sr*.16),ir=AC.createBuffer(1,L,sr),o=ir.getChannelData(0);
  for(let i=0;i<L;i++){const t=i/sr;o[i]=(Math.random()*2-1)*Math.exp(-t/.024)*Math.min(1,i/30)}
  for(const[tm,g]of[[.0023,.5],[.0051,.35],[.0089,.25]]){const k=Math.floor(tm*sr);o[k]+=g;o[k+1]-=g*.6}
  const wet=AC.createGain();wet.gain.value=.2;MASTER.connect(hp);MASTER.connect(conv);conv.connect(wet);wet.connect(hp);hp.connect(comp);comp.connect(AC.destination)}
  if(AC.state==='suspended')AC.resume()}catch(e){}return AC}
const T0=()=>AC.currentTime;
/* noise band: friction, swish of a curtain, rustle */
function nz(t,o){o=Object.assign({f:3000,q:1,type:'bandpass',dur:.01,g:.3,att:.0008,f2:0},o);
  const s=AC.createBufferSource();s.buffer=NB;s.loop=true;const b=AC.createBiquadFilter();b.type=o.type;const T=T0()+Math.max(0,t);b.frequency.setValueAtTime(o.f,T);if(o.f2)b.frequency.exponentialRampToValueAtTime(o.f2,T+o.dur);b.Q.value=o.q;
  const v=AC.createGain();v.gain.setValueAtTime(0,T);v.gain.linearRampToValueAtTime(o.g,T+o.att);v.gain.exponentialRampToValueAtTime(.0001,T+o.dur);
  s.connect(b);b.connect(v);v.connect(MASTER);s.start(T,Math.random());s.stop(T+o.dur+.03)}
const tick=(t,f,g,d=.003)=>nz(t,{f,q:.7,type:'highpass',dur:d,g,att:.0002});
/* damped sinusoid: one resonance of a struck object */
function ping(t,f,dec,g,f2){if(f>AC.sampleRate*.45)return;const T=T0()+Math.max(0,t),o=AC.createOscillator(),v=AC.createGain();o.frequency.setValueAtTime(f,T);if(f2)o.frequency.exponentialRampToValueAtTime(f2,T+dec*2);
  v.gain.setValueAtTime(0,T);v.gain.linearRampToValueAtTime(g,T+.0004);v.gain.setTargetAtTime(0,T+.0004,dec);o.connect(v);v.connect(MASTER);o.start(T);o.stop(T+dec*8+.02)}
/* low body thump */
const thud=(t,f,g,dec)=>ping(t,f,dec,g,f*.55);
/* metal ring: inharmonic partials, high ones die first */
function metal(t,f,g,dec){f=J(f,.04);[[1,1,1],[2.76,.55,.7],[5.4,.32,.45],[8.93,.18,.3]].forEach(([r,gg,dd])=>ping(t,f*r,dec*dd,g*gg))}
/* plastic knock: lower, duller, shorter */
function plast(t,f,g,dec){f=J(f,.05);[[1,1,1],[1.93,.5,.6],[3.1,.25,.35]].forEach(([r,gg,dd])=>ping(t,f*r,dec*dd,g*gg))}
/* the basic contact click every mechanism is made of */
function click(t,v=1,pitch=1){tick(t,J(5200,.1),.3*v,.0025);metal(t,2500*pitch,.2*v,.011);thud(t,J(200,.1),.22*v,.016)}
/* motor: two detuned saws through a lowpass, pitch wobble and gear grit */
function motor(t,dur,f0,f1,g,cut=1300){const T=T0()+t,lp=AC.createBiquadFilter(),v=AC.createGain(),lf=AC.createOscillator(),lg=AC.createGain();
  lp.type='lowpass';lp.frequency.value=cut;lp.Q.value=2.5;v.gain.setValueAtTime(0,T);v.gain.linearRampToValueAtTime(g,T+.05);v.gain.setValueAtTime(g,T+dur-.06);v.gain.linearRampToValueAtTime(0,T+dur);
  lf.frequency.value=6+Math.random()*3;lg.gain.value=f0*.02;lf.connect(lg);
  [1,1.007].forEach(m=>{const o=AC.createOscillator();o.type='sawtooth';o.frequency.setValueAtTime(f0*m,T);o.frequency.linearRampToValueAtTime(f1*m,T+dur);lg.connect(o.frequency);o.connect(lp)});
  lp.connect(v);v.connect(MASTER);lf.start(T);lf.stop(T+dur+.05);
  nz(t,{f:cut*1.2,q:.7,dur:dur,g:g*.55,att:.05});}
/* run a motor to its stop: spin-down + clunk */
const stopClunk=(t,v=1)=>{thud(t,J(150,.05),.5*v,.05);metal(t,1800,.25*v,.02);tick(t,3500,.25*v,.003)};

const SND={
shutter:[
 {id:'slr',name:'SLR · cloth',d:'Spotmatic: зеркало ударяет вверх, шторки пробегают, зеркало падает с дребезгом',fn:()=>{
   tick(0,6500,.18,.002);metal(0,3200,.1,.006);                                     // aperture stop-down
   thud(.014,J(165,.06),.95,.05);ping(.014,J(420,.05),.03,.35);nz(.014,{f:1800,q:.7,dur:.02,g:.4});tick(.014,3500,.5);   // mirror slap
   nz(.044,{f:5200,q:1.1,dur:.006,g:.34});tick(.044,6500,.25);                       // 1st curtain
   nz(.053,{f:4300,q:1,dur:.008,g:.3});metal(.057,2800,.18,.012);thud(.057,J(140,.05),.28,.02);   // 2nd curtain stops
   thud(.105,J(135,.05),.6,.045);tick(.105,2800,.3);nz(.105,{f:1400,q:.8,dur:.03,g:.3});            // mirror returns
   thud(.123,J(150,.1),.22,.03);tick(.123,3300,.14);thud(.134,J(150,.1),.1,.02)}},          // bounce
 {id:'leaf',name:'Compact · leaf',d:'Мыльница: тихий «тск» — два лепестка, никакого зеркала',fn:()=>{
   nz(0,{f:4200,q:1.6,dur:.016,g:.2,f2:2600});metal(0,3600,.14,.007);thud(0,J(280,.08),.18,.018);
   nz(.021,{f:3300,q:1.4,dur:.014,g:.15});tick(.021,4800,.1,.003);thud(.022,J(250,.08),.1,.012)}},
 {id:'rf',name:'Rangefinder',d:'Далномер: мягкий шторочный «шлёп», без зеркала',fn:()=>{
   nz(0,{f:2400,q:.8,dur:.016,g:.25});thud(.002,J(300,.06),.22,.03);
   nz(.017,{f:3000,q:.9,dur:.012,g:.18});tick(.02,4000,.1,.003);metal(.02,2100,.08,.01)}},
 {id:'mf',name:'Medium format',d:'Тяжёлое зеркало: «ка-ДУНК», потом глубокий возврат',fn:()=>{
   thud(0,J(92,.04),1,.12);thud(0,J(210,.05),.6,.07);ping(0,J(310,.04),.06,.32);nz(0,{f:900,q:.6,dur:.06,g:.5});tick(0,3000,.5);
   tick(.075,3200,.55);metal(.075,1700,.35,.03);thud(.075,J(118,.05),.5,.05);nz(.075,{f:2500,q:.7,dur:.02,g:.3});
   thud(.23,J(88,.04),.85,.11);nz(.23,{f:700,q:.6,dur:.06,g:.4});tick(.23,2200,.3);thud(.262,J(105,.08),.3,.05);tick(.262,2600,.12)}},
 {id:'motor',name:'Motor drive',d:'SLR с мотором: щелчок, затем быстрое «ззт» взвода',fn:()=>{
   SND.shutter[0].fn();motor(.15,.17,95,210,.11,1500);stopClunk(.33,.7)}},
 {id:'slow',name:'Slow · 1/4 s',d:'Длинная выдержка: открытие, пауза, закрытие',fn:()=>{
   tick(0,6500,.18,.002);thud(.014,J(165,.06),.95,.05);ping(.014,J(420,.05),.03,.35);nz(.014,{f:1800,q:.7,dur:.02,g:.4});tick(.014,3500,.5);
   nz(.044,{f:5200,q:1.1,dur:.006,g:.34});tick(.044,6500,.25);
   nz(.3,{f:4300,q:1,dur:.008,g:.3});metal(.304,2800,.18,.012);thud(.304,J(140,.05),.28,.02);
   thud(.35,J(135,.05),.6,.045);tick(.35,2800,.3);nz(.35,{f:1400,q:.8,dur:.03,g:.3})}},
 {id:'af',name:'Compact · AF',d:'Писк подтверждения, моторчик фокуса, лепестки',fn:()=>{
   ping(0,2700,.03,.1);ping(.1,3200,.04,.1);motor(.2,.12,200,330,.05,2200);SND.shutter[1].fn.call(null)}},
],
advance:[
 {id:'ratchet',name:'Lever · ratchet',d:'Взвод в 7 зубов с трением и замком в конце',fn:()=>{
   nz(0,{f:1300,q:.5,dur:.26,g:.07,att:.06});
   for(let i=0;i<7;i++){const t=i*(.04-i*.0016)+rnd(.002);click(t,.55+i*.07,1+i*.04)}
   stopClunk(.275,1.1);thud(.285,J(240,.05),.3,.03);nz(.285,{f:1600,q:.8,dur:.03,g:.3})}},
 {id:'short',name:'Lever · short',d:'Короткий ход: три зуба и жёсткий упор',fn:()=>{
   nz(0,{f:1500,q:.5,dur:.12,g:.06,att:.03});[0,.04,.075].forEach((t,i)=>click(t,.7+i*.15,1.05));stopClunk(.125,1)}},
 {id:'wheel',name:'Thumbwheel',d:'Колёсико: частая мелкая трещотка и мягкий стоп',fn:()=>{
   for(let i=0;i<10;i++)click(i*.028+rnd(.002),.4,1.4+rnd(.05));stopClunk(.3,.55)}},
 {id:'winder',name:'Motor winder',d:'Автовзвод SLR: низкий «ззззт», остановка с ударом',fn:()=>{
   click(0,.6);motor(.02,.3,62,150,.14,1100);stopClunk(.32,1)}},
 {id:'autowind',name:'Compact · auto',d:'Автовзвод мыльницы: тонкий моторчик и мелкий «чик» на конце',fn:()=>{
   motor(0,.38,240,420,.07,2800);for(let i=0;i<5;i++)tick(.06+i*.065,4200,.06,.002);click(.4,.8,1.6)}},
 {id:'stuck',name:'End of roll',d:'Конец плёнки: упор, пружина дрожит',fn:()=>{
   click(0,.6);click(.035,.8);click(.065,1);thud(.1,J(105,.04),.8,.06);metal(.1,1300,.35,.03);tick(.1,3000,.4,.003);ping(.12,J(1800,.03),.05,.08)}},
],
rewind:[
 {id:'crank',name:'Crank',d:'Откидная ручка: неровные щелчки руки и шелест плёнки',fn:()=>{
   nz(0,{f:1600,q:.5,dur:1.5,g:.04,att:.3});let t=0;for(let i=0;i<14;i++){click(t,.45+rnd(.1),1.1);t+=.1+rnd(.012)}}},
 {id:'knob',name:'Knob spin',d:'Головка: шорох катушки и частые зубцы',fn:()=>{
   nz(0,{f:1200,q:.5,dur:1.3,g:.05,att:.25});let t=0;for(let i=0;i<22;i++){click(t,.3+rnd(.05),1.5);t+=.062-i*.0013}}},
 {id:'rmotor',name:'Motor rewind',d:'Мотор перемотки: нарастающий вой, затем стоп',fn:()=>{
   click(0,.7);motor(.03,1.05,150,520,.1,2400);stopClunk(1.1,.9)}},
 {id:'rcompact',name:'Compact · rewind',d:'Мыльница: тонкий моторчик и «пшик» крышки',fn:()=>{
   motor(0,1,310,540,.065,3200);stopClunk(1.02,.5);nz(1.05,{f:3000,q:.6,dur:.05,g:.08})}},
],
back:[
 {id:'popup',name:'Pop-up latch',d:'Защёлка, пружина «боинг», крышка отскакивает и стукает',fn:()=>{
   click(0,1.1,.9);ping(.004,J(2300,.03),.07,.1,1800);ping(.006,J(3100,.03),.05,.06,2400);
   thud(.045,J(125,.05),.55,.06);plast(.045,880,.25,.03);nz(.045,{f:1200,q:.7,dur:.03,g:.2});thud(.1,J(145,.08),.22,.04);tick(.1,2600,.1)}},
 {id:'slide',name:'Slide latch',d:'Ползунок скользит, щёлкает, стенка отходит',fn:()=>{
   nz(0,{f:2200,q:.7,dur:.05,g:.13,f2:1100});click(.052,1,1.05);thud(.075,J(170,.05),.3,.04);plast(.075,700,.12,.02)}},
 {id:'door',name:'Door close',d:'Захлопнул заднюю стенку: глухой «бум» и замок',fn:()=>{
   thud(0,J(118,.05),.75,.06);plast(0,1100,.3,.022);nz(0,{f:1300,q:.7,dur:.025,g:.28});click(.046,1.2,.95);thud(.05,J(240,.05),.25,.03)}},
 {id:'cart',name:'Cartridge in',d:'Кассета в камеру: скрежет пластика и посадка',fn:()=>{
   nz(0,{f:2600,q:.5,dur:.04,g:.12,f2:1200});plast(.042,720,.4,.026);click(.046,.7,.85);thud(.048,J(200,.05),.3,.03)}},
],
switch:[
 {id:'toggle',name:'Toggle click',d:'Металлический тумблер: скольжение, «клик», микро-дребезг',fn:()=>{
   nz(0,{f:2200,q:.9,dur:.012,g:.1});click(.012,1.1,1.1);click(.02,.3,1.3)}},
 {id:'slider',name:'Slide detent',d:'Ползунок: шорох и щелчок фиксатора',fn:()=>{
   nz(0,{f:1800,q:.7,dur:.05,g:.1,f2:1000});click(.05,.8,1.2)}},
 {id:'rocker',name:'Rocker',d:'Пластиковая качалка: глухой «так»',fn:()=>{
   plast(0,520,.45,.02);thud(0,J(230,.06),.35,.025);tick(0,2300,.2,.003)}},
 {id:'flag',name:'Flag flip',d:'Флажок: «ф-ляп» и упор',fn:()=>{
   nz(0,{f:1400,q:.5,dur:.04,g:.1,f2:700});thud(.04,J(180,.06),.3,.03);plast(.04,620,.2,.02)}},
],
detent:[
 {id:'soft',name:'Soft click',d:'Резиновое кольцо: мягкий зубец',fn:()=>{plast(0,1900,.2,.008);thud(0,J(210,.08),.2,.016);tick(0,3200,.14,.003)}},
 {id:'crisp',name:'Crisp',d:'Кольцо объектива: сухой точный щелчок',fn:()=>click(0,.75,1.15)},
 {id:'roller',name:'Roller',d:'Шарик в пазу: «тук-к» с отскоком',fn:()=>{thud(0,J(270,.06),.32,.02);tick(.003,3500,.25,.003);ping(.003,J(2100,.05),.008,.12);thud(.014,J(250,.08),.1,.012)}},
 {id:'bayonet',name:'Bayonet lock',d:'Объектив встал на байонет: «клак-к»',fn:()=>{
   metal(0,1900,.45,.025);thud(0,J(190,.05),.55,.04);tick(0,4500,.4,.003);tick(.03,4000,.22,.003);metal(.03,2600,.14,.012)}},
 {id:'endstop',name:'End stop',d:'Упор шкалы ±2 EV: ручка дальше не идёт',fn:()=>{thud(0,J(140,.05),.55,.045);metal(0,1500,.3,.02);tick(0,3000,.3,.003)}}
],
misc:[
 {id:'timer',name:'Self-timer',d:'Автоспуск: тик-так анкера и срабатывание',fn:()=>{
   for(let i=0;i<14;i++){const t=i*.07;tick(t,4200,.16,.002);metal(t,i%2?3000:2400,.07,.006);thud(t,i%2?280:230,.08,.01)}
   nz(.98,{f:2500,q:.6,dur:.05,g:.12});setTimeout(()=>SND.shutter[0].fn(),1000)}},
 {id:'flash',name:'Flash charge',d:'Заряд вспышки: нарастающий писк',fn:()=>{
   const T=T0(),o=AC.createOscillator(),v=AC.createGain();o.frequency.setValueAtTime(1800,T);o.frequency.exponentialRampToValueAtTime(6200,T+1.1);v.gain.setValueAtTime(0,T);v.gain.linearRampToValueAtTime(.05,T+.1);v.gain.linearRampToValueAtTime(.03,T+1.1);v.gain.linearRampToValueAtTime(0,T+1.15);o.connect(v);v.connect(MASTER);o.start(T);o.stop(T+1.2);tick(1.1,5200,.2,.003)}},
 {id:'beep',name:'Compact beep',d:'Два коротких писка',fn:()=>{ping(0,2650,.02,.1);ping(.002,2650,.04,.0);ping(.11,3150,.03,.1)}},
 {id:'cap',name:'Lens cap',d:'Крышка объектива: шорох и «пок»',fn:()=>{nz(0,{f:3000,q:.6,dur:.04,g:.1});plast(.04,420,.38,.03);thud(.04,J(170,.06),.25,.03)}},
]};
for(const g in SND)for(const s of SND[g])s.g=g;

/* ---------- your own recordings (override any synth sound) ---------- */
const RAW={},BUFS={};let sdb=null;
const sopen=()=>new Promise(r=>{try{const q=indexedDB.open('latent-sfx',1);q.onupgradeneeded=()=>q.result.createObjectStore('k');q.onsuccess=()=>r(q.result);q.onerror=()=>r(null)}catch(e){r(null)}});
const sgetAll=()=>new Promise(r=>{if(!sdb)return r({});const out={},c=sdb.transaction('k').objectStore('k').openCursor();c.onsuccess=()=>{const x=c.result;if(x){out[x.key]=x.value;x.continue()}else r(out)};c.onerror=()=>r({})});
const sput=(k,v)=>new Promise(r=>{if(!sdb)return r();const t=sdb.transaction('k','readwrite');v===null?t.objectStore('k').delete(k):t.objectStore('k').put(v,k);t.oncomplete=r;t.onerror=r});
function bufOf(k){if(BUFS[k])return BUFS[k];const r=RAW[k];if(!r||!AC)return null;const b=AC.createBuffer(1,r.data.length,r.rate);b.copyToChannel(r.data,0);return BUFS[k]=b}
function playBuf(b){const s=AC.createBufferSource(),g=AC.createGain();s.buffer=b;g.gain.value=1;s.playbackRate.value=1+rnd(.012);s.connect(g);g.connect(MASTER);s.start()}
const play=s=>{if(!ac())return;try{const k=s.g+':'+s.id,b=bufOf(k);if(b)playBuf(b);else s.fn()}catch(e){console.error(e)}};
function trim(ch,rate){let pk=0;for(let i=0;i<ch.length;i++)pk=Math.max(pk,Math.abs(ch[i]));if(pk<.005)return null;
  const th=pk*.08;let a=0;while(a<ch.length&&Math.abs(ch[a])<th)a++;a=Math.max(0,a-Math.floor(rate*.006));
  let b=ch.length-1;while(b>a&&Math.abs(ch[b])<pk*.02)b--;b=Math.min(ch.length,b+Math.floor(rate*.05),a+Math.floor(rate*3));
  const out=new Float32Array(b-a),k=.92/pk,f=Math.floor(rate*.03);for(let i=0;i<out.length;i++){let v=ch[a+i]*k;const r=out.length-i;if(r<f)v*=r/f;out[i]=v}return out}
let recNow=null;
async function recToggle(key,btn,label){ac();
  if(recNow){const r=recNow;recNow=null;r.stop();return}
  let stream;try{stream=await navigator.mediaDevices.getUserMedia({audio:{echoCancellation:false,noiseSuppression:false,autoGainControl:false}})}catch(e){alert('Нужен доступ к микрофону');return}
  const mr=new MediaRecorder(stream),ch=[];mr.ondataavailable=e=>ch.push(e.data);btn.classList.add('live');btn.textContent='■';
  const done=new Promise(r=>mr.onstop=r);mr.start();recNow={stop:()=>mr.stop()};const to=setTimeout(()=>{if(recNow){recNow=null;mr.stop()}},4000);
  await done;clearTimeout(to);stream.getTracks().forEach(t=>t.stop());btn.classList.remove('live');
  try{const ab=await new Blob(ch).arrayBuffer(),buf=await AC.decodeAudioData(ab),data=trim(buf.getChannelData(0),buf.sampleRate);
    if(!data){btn.textContent='●';alert('Слишком тихо — запиши ближе к камере');return}
    RAW[key]={data,rate:buf.sampleRate};delete BUFS[key];await sput(key,RAW[key]);label()}catch(e){btn.textContent='●';alert('Не удалось записать')}}
const b64=u8=>{let s='';for(let i=0;i<u8.length;i+=8192)s+=String.fromCharCode.apply(null,u8.subarray(i,i+8192));return btoa(s)};
async function exportSamples(){const o={};for(const k in RAW){const f=RAW[k].data,i=new Int16Array(f.length);for(let j=0;j<f.length;j++)i[j]=Math.max(-1,Math.min(1,f[j]))*32767;o[k]={rate:RAW[k].rate,pcm:b64(new Uint8Array(i.buffer))}}
  const file=new File([JSON.stringify(o)],'darkslide-sounds.json',{type:'application/json'});
  if(navigator.canShare&&navigator.canShare({files:[file]})){try{await navigator.share({files:[file]});return}catch(e){if(e.name==='AbortError')return}}
  const u=URL.createObjectURL(file),a=document.createElement('a');a.href=u;a.download=file.name;document.body.appendChild(a);a.click();a.remove()}
async function importSamples(f){let o=JSON.parse(await f.text());
  if(o.clips){const m=o.map||{};o=o.clips;const dec=v=>{const bin=atob(v.pcm),u=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)u[i]=bin.charCodeAt(i);const i16=new Int16Array(u.buffer),d=new Float32Array(i16.length);for(let j=0;j<d.length;j++)d[j]=i16[j]/32767;return{data:d,rate:v.rate}};
    for(const k in o){RAW[k]=dec(o[k]);RAW[k].at=o[k].at;await sput(k,RAW[k])}for(const slot in m){if(RAW[m[slot]]){RAW[slot]={data:RAW[m[slot]].data,rate:RAW[m[slot]].rate};delete BUFS[slot];await sput(slot,RAW[slot])}}return}
  for(const k in o){const bin=atob(o[k].pcm),u=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)u[i]=bin.charCodeAt(i);const i16=new Int16Array(u.buffer),d=new Float32Array(i16.length);for(let j=0;j<d.length;j++)d[j]=i16[j]/32767;RAW[k]={data:d,rate:o[k].rate};delete BUFS[k];await sput(k,RAW[k])}}


/* what each control plays: your picks from PARTS (a REAL sample from the pack overrides the synth) */
const CFG={shutter:'shutter:rf',advance:'advance:stuck',counter:'detent:bayonet',flag:'switch:toggle',rewind:'rewind:rmotor',back:'back:cart',backClose:'back:door',exp:'detent:soft',expStop:'detent:endstop',lens:'detent:crisp',film:'misc:cap'};
const findS=k=>{const[g,i]=k.split(':');return SND[g].find(x=>x.id===i)};
const snd=r=>{if(!ac())return;const x=findS(CFG[r]);if(x)play(x)};
const tickS=()=>{if(AC)click(0,.25,1.3)};

/* ================= helpers ================= */
let tt;function toast(s){const t=$('#toast');t.textContent=s;t.style.opacity=1;clearTimeout(tt);tt=setTimeout(()=>t.style.opacity=0,2400)}
const ang=(e,c)=>Math.atan2(e.clientY-c.y,e.clientX-c.x)*180/Math.PI;
const wrap=d=>{while(d>180)d-=360;while(d<-180)d+=360;return d};
const centerOf=el=>{const r=el.getBoundingClientRect();return{x:r.left+r.width/2,y:r.top+r.height/2}};
function dragRot(hit,centerEl,o){let id=null,c,prev,rot,moved=0;
  hit.addEventListener('pointerdown',e=>{ac();id=e.pointerId;try{hit.setPointerCapture(id)}catch(_){}c=centerOf(centerEl);prev=ang(e,c);rot=o.get();moved=0;e.preventDefault()});
  hit.addEventListener('pointermove',e=>{if(e.pointerId!==id)return;const a=ang(e,c);const d=wrap(a-prev);prev=a;moved+=Math.abs(d);rot=clamp(rot+d,o.min,o.max);o.set(rot)});
  const end=e=>{if(e.pointerId!==id)return;id=null;o.end&&o.end(moved,rot)};
  hit.addEventListener('pointerup',end);hit.addEventListener('pointercancel',end)}
async function saveBlobs(blobs,names){const files=blobs.map((b,i)=>new File([b],names[i],{type:'image/jpeg'}));
  if(navigator.canShare&&navigator.canShare({files})){try{await navigator.share({files});return}catch(e){if(e&&e.name==='AbortError')return}}
  for(let i=0;i<blobs.length;i++){const u=URL.createObjectURL(blobs[i]),a=document.createElement('a');a.href=u;a.download=names[i];document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),4000);await sleep(250)}
  toast('Saved')}

/* ================= IndexedDB: the roll in the camera + the last developed roll ================= */
let db=null;const mem={raw:[],dev:[]};
function idb(){return new Promise(res=>{try{const r=indexedDB.open('latent',2);r.onupgradeneeded=()=>{const d=r.result,h=d.objectStoreNames;if(!h.contains('raw'))d.createObjectStore('raw',{keyPath:'i'});if(!h.contains('dev'))d.createObjectStore('dev',{keyPath:'i'});if(!h.contains('tank'))d.createObjectStore('tank',{keyPath:'id'})};r.onsuccess=()=>res(r.result);r.onerror=()=>res(null);r.onblocked=()=>res(null)}catch(e){res(null)}})}
const tx=(st,mode,fn)=>new Promise(res=>{if(!db)return res(null);try{const t=db.transaction(st,mode),r=fn(t.objectStore(st));t.oncomplete=()=>res(r&&r.result!==undefined?r.result:true);t.onerror=t.onabort=()=>res(null)}catch(e){res(null)}});
const put=(st,v)=>db?tx(st,'readwrite',s=>s.put(v)):(mem[st][v.i]=v,Promise.resolve(true));
const all=st=>db?tx(st,'readonly',s=>s.getAll()).then(r=>r||[]):Promise.resolve(mem[st].filter(Boolean));
const memTank=[];
const tall=()=>db?tx('tank','readonly',s=>s.getAll()).then(r=>r||[]):Promise.resolve(memTank.slice());
const tput=v=>db?tx('tank','readwrite',s=>s.put(v)):(memTank.push(v),Promise.resolve(true));
const tdel=id=>db?tx('tank','readwrite',s=>s.delete(id)):(memTank.splice(memTank.findIndex(r=>r.id===id),1),Promise.resolve(true));
const clr=st=>db?tx(st,'readwrite',s=>s.clear()):(mem[st].length=0,Promise.resolve(true));



const cv=$('#gl');
let ENG;try{ENG=new PixiEngine(cv)}catch(e){$('#nogl').style.display='flex';throw e}
const freeRT=()=>{};

/* ---- source: live camera, imported photo, or the built-in demo scene (mirrored beyond its edges, under the dimmed margin) ---- */
let SRC={w:1536,h:1024},SCENE={el:null,w:0,h:0},cover=[1,1];
function uploadSrc(el,w,h){ENG.setSource(el);SRC.w=w;SRC.h=h;const sa=w/h;cover=sa>FA?[FA/sa,1]:[1,sa/FA]}
function setScene(el,w,h){SCENE={el,w,h};uploadSrc(el,w,h);dirty=true}

/* ---- film date stamp: 7-segment LED glyphs are drawn by the overlay shader (pass 5) ---- */
function makeStamp(){}

/* ---- parameters: one object describes a frame (also what is stored with each exposure) ---- */
const seedOf=(frame,film)=>(frame*.618034+film*.2718+.123)%1;
const FXK=[.7,1.2,1.8];
const fi=fp=>{if(fp.fn){const i=FILMS.findIndex(f=>f.name===fp.fn);if(i>=0)return i}return FILMS[fp.film]?fp.film:0};
function previewFp(){return{fn:FILMS[S.film].name,fx:S.fx,brd:S.brd,fmt:S.fmt,land:LAND?1:0,film:S.film,lens:S.lens,ev:S.ev,seed:seedOf(S.frame,S.film),burn:BURN[S.burnNext],w:wearOf(S.shots),stamp:S.date,ts:Date.now()}}


function params(fp){const F=FILMS[fi(fp)],PS=PRESETS[F.preset],L=LENSES[fp.lens],FM=FORMATS[fp.fmt||0],w=fp.w,aN=.35,E=clamp(fp.ev,-3,3),k=FXK[fp.fx==null?1:fp.fx]/1.2;
  const f=frameBox(),view=DEV?[1,1]:[SW/f.w,SH/f.h],sc=Math.max(cv.width,cv.height)/1000,fW=cv.width/view[0],fH=cv.height/view[1];
  const lensKv=Math.sqrt(Math.max(0,1/Math.sqrt(1-clamp(L.vig*(1-.7*aN)*.7,0,.8))-1));
  const lerp=(base,v)=>base+(v-base)*k;
  const P=Object.assign(JSON.parse(JSON.stringify(PS)),{
    distortion:L.k+PS.distortion,zoom:L.zoom*FM.crop,aberration:(PS.aberration+L.ca*.004)*(1+.8*w)*(.5+.5*k),
    softness:clamp(PS.softness*.6+L.soft*(1-.85*aN)*.5,0,1),exposure:PS.exposure+E,
    contrast:lerp(1,PS.contrast),saturation:PS.mono?1:lerp(1,PS.saturation),fade:PS.fade*k,
    shadowTone:PS.shadowTone.map(v=>v*k),highlightTone:PS.highlightTone.map(v=>v*k),lutMix:0,
    bloom:(PS.bloom+L.glow*.35+.25*w)*k,halation:PS.halation*k*(1+.5*w),
    grain:PS.grain*k*(1+.2*w),grainSize:PS.grainSize*Math.max(fW,fH)/(1000*sc),
    vignette:(PS.vignette*k+lensKv*.6)*(1+.4*w),leak:(PS.leak+.1+1.3*w*w)*k,dust:(PS.dust+.3*w)*k,
    stamp:!!fp.stamp,stampYear:null});
  const R=rng(Math.floor(fp.seed*1e6)+11),a=Math.floor(R()*4)*Math.PI/2+(R()-.5)*.5,mir=R()<.5?-1:1,c=Math.cos(a),sn=Math.sin(a);
  const St={seed:fp.seed*97+1,frameA:FA,view,shift:(!DEV&&!LAND&&view[1]>1.001)?FOFF/SH:0,burn:fp.burn||0,dim:!DEV,
    leakSeed:fp.seed*50,shotSeed:fp.seed*50+7,leakM:[c,sn,-sn*mir,c*mir],leakGain:1,flash:0,dev:1,stamp:stampLayout(P,new Date(fp.ts||Date.now()))};
  return{P,S:St}}
function renderFilm(fp,n){const{P,S:St}=params(fp);ENG.render(P,St,cv.width,cv.height)}

/* ---- demo scene (used until the camera is allowed, or when there is none) ---- */
function demoScene(){const W=1536,H=1024,c=document.createElement('canvas');c.width=W;c.height=H;const x=c.getContext('2d'),R=rng(5);
  let g=x.createLinearGradient(0,0,0,H*.66);g.addColorStop(0,'#27406b');g.addColorStop(.35,'#6d7fa8');g.addColorStop(.62,'#e9a27a');g.addColorStop(.86,'#ffd7a0');g.addColorStop(1,'#fff0c9');x.fillStyle=g;x.fillRect(0,0,W,H*.7);
  const sx=W*.55,sy=H*.5;g=x.createRadialGradient(sx,sy,0,sx,sy,H*.45);g.addColorStop(0,'rgba(255,252,236,1)');g.addColorStop(.05,'rgba(255,244,210,.96)');g.addColorStop(.17,'rgba(255,190,120,.45)');g.addColorStop(1,'rgba(255,150,90,0)');x.fillStyle=g;x.fillRect(0,0,W,H*.72);
  for(let i=0;i<26;i++){const cx=R()*W,cy=H*(.1+R()*.36),rw=140+R()*320,rh=9+R()*22;const gg=x.createRadialGradient(cx,cy,0,cx,cy,rw);gg.addColorStop(0,'rgba(255,'+(190+R()*50|0)+','+(150+R()*60|0)+','+(.2+R()*.2)+')');gg.addColorStop(1,'rgba(255,200,160,0)');
    x.save();x.translate(cx,cy);x.scale(1,rh/rw);x.translate(-cx,-cy);x.fillStyle=gg;x.beginPath();x.arc(cx,cy,rw,0,7);x.fill();x.restore()}
  const ridge=(base,amp,col,seed)=>{const r=rng(seed),ph=[r()*6,r()*6,r()*6];x.fillStyle=col;x.beginPath();x.moveTo(0,H);for(let px=0;px<=W;px+=6){x.lineTo(px,base-amp*(.5*Math.sin(px/260+ph[0])+.3*Math.sin(px/97+ph[1])+.2*Math.sin(px/41+ph[2])+.6))}x.lineTo(W,H);x.fill()};
  ridge(H*.57,75,'#c08f90',11);ridge(H*.61,62,'#8f6d80',12);ridge(H*.65,46,'#5e4d68',13);
  const ly=H*.665;g=x.createLinearGradient(0,ly,0,H);g.addColorStop(0,'#e7b78f');g.addColorStop(.28,'#8e89a4');g.addColorStop(1,'#1b2640');x.fillStyle=g;x.fillRect(0,ly,W,H-ly);
  for(let i=0;i<130;i++){const yy=ly+6+i*2.5*(1+i/95),wv=(26+i*2.3)*(.4+R()*.9);x.fillStyle='rgba(255,'+(210+R()*40|0)+','+(150+R()*50|0)+','+(.55*(1-i/140))+')';x.fillRect(sx-wv/2+(R()-.5)*34,yy,wv,1.5+i/42)}
  const pine=(px,py,h,col)=>{x.fillStyle=col;for(let k=0;k<7;k++){const w=h*.32*(1-k/8.5)+h*.04,yy=py-h+k*h*.13;x.beginPath();x.moveTo(px,yy-h*.1);x.lineTo(px-w,yy+h*.2);x.lineTo(px+w,yy+h*.2);x.fill()}x.fillRect(px-h*.025,py-h*.2,h*.05,h*.25)};
  for(let i=0;i<8;i++)pine(300+i*52+R()*30,H*.86+R()*40,240+R()*200,'#0f1620');
  x.fillStyle='#0b1018';x.beginPath();x.moveTo(0,H);x.lineTo(0,H*.9);x.quadraticCurveTo(W*.3,H*.86,W*.5,H*.94);x.lineTo(W*.55,H);x.fill();
  const lamp=(lx,ly2,s)=>{const gg=x.createRadialGradient(lx,ly2,0,lx,ly2,s*9);gg.addColorStop(0,'rgba(255,255,235,1)');gg.addColorStop(.12,'rgba(255,225,160,.9)');gg.addColorStop(.4,'rgba(255,170,80,.25)');gg.addColorStop(1,'rgba(255,140,60,0)');x.fillStyle=gg;x.fillRect(lx-s*9,ly2-s*9,s*18,s*18);x.fillStyle='#0c0709';x.fillRect(lx-s/2,ly2,s,s*14)};
  lamp(W*.62,H*.8,6);lamp(W*.8,H*.72,4);
  return c}

/* ================= wear: black paint chips off to brass, on the controls themselves ================= */
const wc=$('#wear'),wx=wc.getContext('2d');let WM=null;
const RR={rew:'#rew',lev:'#lev',latch:'#latch',drum:'.drum',chip:'#chip',evs:'#evs',lens:'#lring',pad:'#shutter'};
function genWear(){const R=rng(20261112),m=[];
  const add=(ref,n,kind,o)=>{for(let i=0;i<n;i++)m.push(Object.assign({k:kind,t:R(),ref,u:R(),v:R()<.5?0:1,r:1.6+R()*3.2,al:.5+.45*R()},o||{}))};
  add('rew',10,'chip');add('lev',14,'chip');add('latch',8,'chip');add('drum',8,'chip');add('chip',8,'chip');add('evs',10,'chip');add('lens',26,'chip');add('pad',22,'scuff',{r:3+R()*5});
  for(let i=0;i<8;i++)m.push({k:'scr',t:R(),ref:['rew','lev','lens','evs'][i%4],u:R(),v:R(),len:8+R()*16,ang:R()*6.283});
  for(let i=0;i<48;i++)m.push({k:'dust',t:R(),ref:'glass',u:R(),v:R(),r:.5+R()*1.4,al:.28+.4*R(),d:R()<.45});
  for(let i=0;i<9;i++)m.push({k:'hair',t:R(),ref:'glass',u:R(),v:R(),len:10+R()*40,ang:R()*6.283});
  return m}
function posOf(m){if(m.ref==='glass'){const f=frameBox();return{x:(SW-f.w)/2+10+m.u*(f.w-20),y:f.y-f.h/2+10+m.v*(f.h-20)}}
  const el=$(RR[m.ref]);if(!el)return null;
  if(m.ref==='pad'){const r0=el.getBoundingClientRect(),st0=$('#stage').getBoundingClientRect(),cx=(r0.left-st0.left+r0.width/2)/SC,cy=(r0.top-st0.top+r0.height/2)/SC,a=m.u*6.283,rr=(m.v?.36:.22)*r0.width/SC;return{x:cx+Math.cos(a)*rr,y:cy+Math.sin(a)*rr}}const st=$('#stage').getBoundingClientRect(),r=el.getBoundingClientRect();
  const L=(r.left-st.left)/SC,T=(r.top-st.top)/SC,W=r.width/SC,H=r.height/SC;return{x:L+m.u*W,y:T+(m.v?H-1.5:1.5)}}
function wearDraw(){if(!WM)WM=genWear();const w=wearOf(S.shots);wx.setTransform(2,0,0,2,0,0);wx.clearRect(0,0,SW,SH);
  const k=m=>clamp((w-m.t)*5,0,1);
  for(const m of WM){const f=k(m);if(f<=0)continue;const p=posOf(m);if(!p)continue;
    if(m.k==='chip'){const a=m.al*f,g=wx.createRadialGradient(p.x,p.y,0,p.x,p.y,m.r);g.addColorStop(0,'rgba(196,148,74,'+a+')');g.addColorStop(.6,'rgba(160,116,56,'+a*.8+')');g.addColorStop(1,'rgba(160,116,56,0)');wx.fillStyle=g;wx.beginPath();wx.arc(p.x,p.y,m.r,0,7);wx.fill()}
    else if(m.k==='scuff'){const a=m.al*f*.5,g=wx.createRadialGradient(p.x,p.y,0,p.x,p.y,m.r);g.addColorStop(0,'rgba(150,150,145,'+a+')');g.addColorStop(1,'rgba(150,150,145,0)');wx.fillStyle=g;wx.beginPath();wx.arc(p.x,p.y,m.r,0,7);wx.fill()}
    else if(m.k==='scr'){wx.strokeStyle='rgba(205,170,110,'+.55*f+')';wx.lineWidth=.6;wx.beginPath();wx.moveTo(p.x,p.y);wx.lineTo(p.x+Math.cos(m.ang)*m.len,p.y+Math.sin(m.ang)*m.len);wx.stroke()}
    else if(m.k==='dust'){wx.fillStyle=m.d?'rgba(0,0,0,'+m.al*f+')':'rgba(255,255,255,'+m.al*f*.7+')';wx.beginPath();wx.arc(p.x,p.y,m.r,0,7);wx.fill()}
    else if(m.k==='hair'){wx.strokeStyle='rgba(0,0,0,'+.35*f+')';wx.lineWidth=.7;wx.beginPath();wx.moveTo(p.x,p.y);wx.quadraticCurveTo(p.x+Math.cos(m.ang)*m.len*.5+6,p.y+Math.sin(m.ang)*m.len*.5-5,p.x+Math.cos(m.ang)*m.len,p.y+Math.sin(m.ang)*m.len);wx.stroke()}}}

/* ================= UI ================= */
const vfw=$('#vfw');
const evTxt=v=>(v>0?'+':v<0?'\u2212':'')+Math.abs(v).toFixed(1);
function recalcCover(){const sa=SRC.w/SRC.h;cover=sa>FA?[FA/sa,1]:[1,sa/FA]}
function frameBox(){if(!LAND)return{w:390,h:390/FA,y:SH/2-FOFF};let h=SH,w=h*FA;if(w>SW){w=SW;h=w/FA}return{w,h,y:SH/2}}
function layoutFrame(){const f=frameBox(),v=$('#vfo');v.style.width=f.w+'px';v.style.height=f.h+'px';v.style.left=((SW-f.w)/2)+'px';v.style.marginTop=(-f.h/2-(LAND?0:FOFF))+'px';
  $('#toast').style.top=(LAND?104:f.y-f.h/2+14)+'px'}
function setFormat(i){S.fmt=i;FA=faOf(i,LAND);recalcCover();layoutFrame();makeStamp(Date.now());wearDraw();dirty=true}
/* frame counter: a mechanical drum */
const d1=$('#d1'),d2=$('#d2');
d1.innerHTML=['0','1','2','3','E'].map(c=>'<b>'+c+'</b>').join('');d2.innerHTML=['0','1','2','3','4','5','6','7','8','9','N'].map(c=>'<b>'+c+'</b>').join('');
function setDrum(n,anim){const end=n>=S.len,a=end?4:Math.floor(n/10),b=end?10:n%10;d1.style.transition=d2.style.transition=anim?'transform .38s cubic-bezier(.25,1.3,.4,1)':'none';d1.style.transform='translateY('+(-a*54)+'px)';d2.style.transform='translateY('+(-b*54)+'px)'}
/* horizontal slide: drag to the end, springs back; tap = full stroke */
function hdrag(slot,knob,cfg){let id=null,x0,p0,moved=0,p=cfg.rest();
  const pos=v=>{p=clamp(v,0,cfg.travel);knob.style.left=(3+p)+'px'};
  const anim=(v,ms)=>{knob.style.transition='left '+ms+'ms cubic-bezier(.3,1.25,.5,1)';knob.style.left=(3+v)+'px';p=v};
  const inst=v=>{knob.style.transition='none';pos(v)};
  slot.addEventListener('pointerdown',e=>{ac();e.preventDefault();id=e.pointerId;try{slot.setPointerCapture(id)}catch(_){}x0=e.clientX;p0=p;moved=0;knob.style.transition='none'});
  slot.addEventListener('pointermove',e=>{if(e.pointerId!==id)return;const dx=(e.clientX-x0)/SC;moved=Math.max(moved,Math.abs(dx));const b=p;pos(p0+dx);cfg.onMove&&cfg.onMove(p,b)});
  const end=e=>{if(e.pointerId!==id)return;id=null;if(moved<5)cfg.onDone(anim,true);else if(p>=cfg.travel*.85)cfg.onDone(anim,false);else anim(cfg.rest(),220)};
  slot.addEventListener('pointerup',end);slot.addEventListener('pointercancel',end);
  return{anim,inst,rest:ms=>ms?anim(cfg.rest(),ms):inst(cfg.rest())}}
const LEV=hdrag($('#lev'),$('#lev i'),{travel:66,rest:()=>armed?0:14,
  onMove:(p,b)=>{if(Math.floor(p/16)!==Math.floor(b/16))tickS()},
  onDone:an=>{if(armed){an(0,200);toast('Ready \u2014 take the picture');return}armed=true;$('#lev').classList.remove('led','hint');snd('advance');an(66,70);setTimeout(()=>an(0,260),110)}});
function levRest(instant){$('#lev').classList.toggle('led',!armed);LEV.rest(instant?0:240)}
function levHint(){const l=$('#lev');l.classList.remove('hint');void l.offsetWidth;l.classList.add('hint')}
const REW=hdrag($('#rew'),$('#rew i'),{travel:54,rest:()=>0,
  onDone:async an=>{if(S.frame===0){toast('Nothing to rewind');an(0,260);return}if(backOpen){toast('Close the back first');an(0,260);return}an(54,80);await doRewind();an(0,300)}});
/* back latch: pull up to open the back (light gets in), tap to close */
const latch=$('#latch');let lt2=null;
latch.addEventListener('pointerdown',e=>{ac();e.preventDefault();try{latch.setPointerCapture(e.pointerId)}catch(_){}lt2={y:e.clientY,done:false}});
latch.addEventListener('pointermove',e=>{if(!lt2||lt2.done)return;if((lt2.y-e.clientY)/SC>10){lt2.done=true;openBack()}});
latch.addEventListener('pointerup',()=>{if(!lt2)return;const t=!lt2.done;lt2=null;if(t){backOpen?closeBack():toast('Pull the latch up to open the back')}});
latch.addEventListener('pointercancel',()=>{lt2=null});
const DEVMS=[0,600000,3600000,21600000],DN=['INSTANT','10 MIN','1 HOUR','6 HOURS'];
const TK=[];
const mmss=ms=>{const m=Math.ceil(ms/60000);return m>=60?Math.floor(m/60)+'h '+String(m%60).padStart(2,'0')+'m':m+' min'};
async function doRewind(){if(rewinding)return;rewinding=true;snd('rewind');toast('Rewinding');await sleep(1350);rewinding=false;await finishRoll()}
async function finishRoll(){const raws=(await all('raw')).sort((a,b)=>a.i-b.i);if(!raws.length){S.frame=0;sync(true);return}
  const d=DEVMS[S.dev==null?1:S.dev];if(!d){await developRoll(raws);return}
  const id=Date.now(),rec={id,ready:id+d,opened:S.opened,film:FILMS[fi(raws[0].p)].name,items:raws};
  await tput(rec);await clr('raw');TK.push({id,ready:rec.ready,n:raws.length,film:rec.film});
  S.frame=0;S.opened=false;S.burnNext=0;armed=true;levRest();sync(true);tankTick();
  toast('In the tank \u00b7 ready in '+mmss(d))}
async function developTank(id){const rec=(await tall()).find(r=>r.id===id);if(!rec){toast('Roll not found');return}
  await developRoll(rec.items.sort((a,b)=>a.i-b.i),{id,opened:rec.opened})}
function tankTick(){const el=$('#tank'),now=Date.now();if(!TK.length){el.style.display='none';return}el.style.display='block';
  const rd=TK.filter(t=>t.ready<=now);
  if(rd.length){el.className='rdy';el.textContent='\u25cf '+rd.length+(rd.length>1?' ROLLS':' ROLL')+' READY'}
  else{el.className='';const nx=Math.min(...TK.map(t=>t.ready));el.textContent='\u25d4 DEVELOPING \u00b7 '+mmss(nx-now)}}
$('#tank').addEventListener('pointerdown',e=>{ac();e.preventDefault();const now=Date.now(),rd=TK.find(t=>t.ready<=now);
  if(rd){if(!labOpen&&!busy)developTank(rd.id)}else if(TK.length)toast('Still in the tank \u00b7 '+mmss(Math.min(...TK.map(t=>t.ready))-now))});
setInterval(tankTick,15000);
function openBack(){if(backOpen||rewinding)return;backOpen=true;snd('back');latch.classList.add('open');
  vfw.classList.remove('lk');void vfw.offsetWidth;vfw.classList.add('lk');
  if(S.frame>0){S.opened=true;S.burnNext=3;toast('Light hit the film')}else toast('Back open');sync(true)}
function closeBack(){if(!backOpen)return;backOpen=false;snd('backClose');latch.classList.remove('open');toast('Back closed')}
/* exposure: vertical slide, +2 at the top */
const evs=$('#evs'),evk=$('#evs i');
for(let i=0;i<13;i++){const t=document.createElement('div');t.className='tk'+(i===6?' z':'');t.style.top=(14+i*(104/12))+'px';evs.appendChild(t)}
const evPos=()=>{evk.style.top=(5+(2-S.ev)/4*104)+'px'};
let evd=false;
function evMove(e){const r=evs.getBoundingClientRect(),f=clamp((e.clientY-r.top)/r.height,0,1);const v=Math.round((2-4*clamp((f-14/130)/(104/130),0,1))*3)/3;
  if(v!==S.ev){S.ev=v;snd(Math.abs(v)>=2?'expStop':'exp');sync(true);toast('EXP '+evTxt(v))}}
evs.addEventListener('pointerdown',e=>{ac();e.preventDefault();try{evs.setPointerCapture(e.pointerId)}catch(_){}evd=true;evMove(e)});
evs.addEventListener('pointermove',e=>{if(evd)evMove(e)});
['pointerup','pointercancel'].forEach(n=>evs.addEventListener(n,()=>{evd=false}));
/* lens strip */
let ls=null;const lt=$('#ltrack');
LENSES.forEach((L,i)=>{const sEl=document.createElement('div');sEl.className='ln';sEl.style.left=(i*72-36)+'px';sEl.innerHTML=L.mm+'<small>mm</small>';lt.appendChild(sEl)});
function setLP(px,anim){lt.style.transition=anim?'transform .18s cubic-bezier(.3,1.3,.5,1)':'none';lt.style.transform='translateX('+(-px).toFixed(1)+'px)';lt._p=px}
const lr=$('#lring');
lr.addEventListener('pointerdown',e=>{ac();e.preventDefault();try{lr.setPointerCapture(e.pointerId)}catch(_){}ls={x:e.clientX,p:lt._p||0}});
lr.addEventListener('pointermove',e=>{if(!ls)return;const p=clamp(ls.p-(e.clientX-ls.x)/SC,0,288);setLP(p,false);const i=Math.round(p/72);if(i!==S.lens){S.lens=i;snd('lens');sync(true)}});
const lend=()=>{if(!ls)return;ls=null;setLP(S.lens*72,true);const FM=FORMATS[S.fmt];toast(LENSES[S.lens].mm+'mm'+(FM.crop>1?' \u2192 '+Math.round(LENSES[S.lens].mm*FM.crop)+' eq':'')+' \u00b7 '+LENSES[S.lens].name)};
lr.addEventListener('pointerup',lend);lr.addEventListener('pointercancel',lend);
let firstSync=true;
const SPD=[30,60,125,250,500,1000],AP=['2.8','1.8','1.4','2.0'];let tkLen=0;
function hud(){const tk=$('#ticks');if(tkLen!==S.len){tkLen=S.len;tk.className=S.len>24?'dense':'';tk.innerHTML='<i></i>'.repeat(S.len)}
  [...tk.children].forEach((e,i)=>{e.className=i<S.frame?'on':i===S.frame?'cur':''});
  $('#ledS').textContent='1/'+SPD[clamp(2-Math.round(S.ev),0,5)];$('#ledA').textContent='F'+AP[S.lens];$('#ledE').textContent='EV '+evTxt(S.ev);$('#ledN').textContent=String(Math.min(S.frame+1,S.len)).padStart(2,'0')}
function sync(skip){const F=FILMS[S.film],FM=FORMATS[S.fmt];hud();
  if(!skip&&!ls)setLP(S.lens*72,true);
  setDrum(S.frame,!firstSync);firstSync=false;$('#cntMax').textContent=FM.n+' \u00b7 '+S.len;
  $('#chip i').style.background=F.c;$('#chipN').textContent=F.name;$('#chipI').textContent=F.iso;
  document.querySelectorAll('.carton').forEach(el=>el.classList.toggle('on',+el.dataset.i===S.film));
  document.querySelectorAll('#seg b').forEach(b=>b.classList.toggle('on',+b.dataset.n===S.len));
  document.querySelectorAll('#xseg b').forEach(b=>b.classList.toggle('on',+b.dataset.i===S.fx));document.querySelectorAll('#bseg b').forEach(b=>b.classList.toggle('on',+b.dataset.i===S.brd));document.querySelectorAll('#dseg b').forEach(b=>b.classList.toggle('on',+b.dataset.i===(S.dev==null?1:S.dev)));
  document.querySelectorAll('#fseg b').forEach(b=>b.classList.toggle('on',+b.dataset.i===S.fmt));
  $('#seg').classList.toggle('lock',S.frame>0);
  $('#swDate').classList.toggle('off',!S.date);evPos();
  dirty=true;save()}
/* long-press the drum: new / used / worn body */
let cp=null,cpLong=false;const cnt=$('#counter');
cnt.addEventListener('pointerdown',e=>{ac();e.preventDefault();cpLong=false;cp=setTimeout(()=>{cpLong=true;S.shots=S.shots<20?55:S.shots<120?170:0;snd('flag');wearDraw();sync(true);const w=wearOf(S.shots);toast((w<.15?'Mint':w<.6?'Used':'Worn')+' body \u00b7 '+S.shots+' shots')},700)});
cnt.addEventListener('pointerup',()=>{clearTimeout(cp);if(!cpLong)toast(FILMS[S.film].name+' '+FILMS[S.film].iso+' \u00b7 '+S.frame+' of '+S.len)});
cnt.addEventListener('pointercancel',()=>clearTimeout(cp));

/* ---- film sheet: stock, frame, roll length, date back, photo, sound pack ---- */
function sheet(on){sheetOn=on;$('#sheet').classList.toggle('on',on);$('#sheetBg').classList.toggle('on',on)}
function changeFilm(i){i=(i+FILMS.length)%FILMS.length;if(i===S.film)return;
  if(S.frame>0){toast('Film in the camera \u00b7 rewind first');return}
  S.film=i;S.burnNext=0;armed=true;levRest();snd('film');sync(true)}
const CATS=[['all','All'],['mine','Mine'],['colour','Colour'],['cine','Cine']];
const fg=$('#fgrid'),tabs=$('#ftabs');
CATS.forEach(([k,n])=>{const b=document.createElement('b');b.textContent=n;b.dataset.k=k;b.addEventListener('click',()=>{ac();S.cat=k;drawFilms();snd('flag');save()});tabs.appendChild(b)});
function drawFilms(){fg.innerHTML='';const cat=S.cat||'all';document.querySelectorAll('#ftabs b').forEach(b=>b.classList.toggle('on',b.dataset.k===cat));
  FILMS.forEach((f,i)=>{if(cat!=='all'&&f.cat!==cat)return;const d=document.createElement('div');d.className='carton'+(i===S.film?' on':'');d.dataset.i=i;
    d.innerHTML='<div class="cb" style="background:'+f.c+';color:'+f.ink+'">'+f.name+'</div><div class="ci">'+f.iso+'</div><div class="ct">'+f.type+'</div>';
    d.addEventListener('click',()=>{ac();changeFilm(i)});fg.appendChild(d)})}
document.querySelectorAll('#seg b').forEach(b=>b.addEventListener('click',()=>{ac();if(S.frame>0){toast('Roll in the camera \u00b7 rewind first');return}S.len=+b.dataset.n;snd('flag');sync(true)}));
const XN=['SOFT','FULL','WILD'],BN=['NONE','INSTANT','35MM','SCAN'];
[['#xseg',XN,'fx'],['#bseg',BN,'brd'],['#dseg',DN,'dev']].forEach(([id,names,key])=>{const el=$(id);names.forEach((n,i)=>{const b=document.createElement('b');b.dataset.i=i;b.textContent=n;b.addEventListener('click',()=>{ac();S[key]=i;snd('flag');sync(true);toast(n)});el.appendChild(b)})});
const fsg=$('#fseg');FORMATS.forEach((f,i)=>{const b=document.createElement('b');b.dataset.i=i;b.innerHTML=f.n+'<small>'+f.s+'</small>';b.addEventListener('click',()=>{ac();if(i===S.fmt)return;setFormat(i);snd('flag');sync(true);toast(f.n+' \u00b7 '+f.s)});fsg.appendChild(b)});
$('#chip').addEventListener('pointerdown',e=>{ac();e.preventDefault();try{$('#chip').setPointerCapture(e.pointerId)}catch(_){}});
$('#chip').addEventListener('pointerup',()=>{if(!longChip){snd('film');sheet(!sheetOn)}longChip=false});
let longChip=false;
$('#sheetBg').addEventListener('pointerdown',e=>{e.preventDefault();sheet(false)});
let sy=null;$('#sheet').addEventListener('pointerdown',e=>{sy=e.clientY});
$('#sheet').addEventListener('pointerup',e=>{if(sy!=null&&e.clientY-sy>90&&$('#sheet').scrollTop===0&&!e.target.closest('#fgrid'))sheet(false);sy=null});
$('#swDate').addEventListener('click',()=>{ac();S.date=!S.date;snd('flag');sync(true)});
/* sound pack: your recordings / samples override the synth */
const packN=()=>{const n=Object.keys(RAW).filter(k=>!k.startsWith('cand:')).length;$('#packN').textContent=n?n+' real sounds':'synth'};
$('#bPack').addEventListener('click',()=>$('#packf').click());
$('#packf').addEventListener('change',async e=>{const f=e.target.files[0];e.target.value='';if(!f)return;try{await importSamples(f);packN();toast('Sound pack loaded')}catch(err){toast('Cannot read the pack')}});
/* swipe the viewfinder = next film (when the camera is empty) */
let vs=null;
vfw.addEventListener('pointerdown',e=>{ac();vs={x:e.clientX,done:false};try{vfw.setPointerCapture(e.pointerId)}catch(_){}});
vfw.addEventListener('pointermove',e=>{if(!vs||vs.done)return;const dx=(e.clientX-vs.x)/SC;if(Math.abs(dx)>70){vs.done=true;changeFilm(S.film+(dx<0?1:-1));toast(FILMS[S.film].name+' '+FILMS[S.film].iso+' \u00b7 '+FILMS[S.film].type)}});
vfw.addEventListener('pointerup',()=>{vs=null});vfw.addEventListener('pointercancel',()=>{vs=null});

/* ---- photo import + live camera ---- */
$('#bPhoto').addEventListener('click',()=>{ac();$('#file').click()});
$('#file').addEventListener('change',async e=>{const f=e.target.files[0];e.target.value='';if(!f)return;
  const url=URL.createObjectURL(f),im=new Image();im.src=url;try{await im.decode()}catch(_){toast('Cannot read image');return}
  const s=Math.min(1,3072/Math.max(im.naturalWidth,im.naturalHeight)),w=Math.round(im.naturalWidth*s),h=Math.round(im.naturalHeight*s);
  const c=document.createElement('canvas');c.width=w;c.height=h;c.getContext('2d').drawImage(im,0,0,w,h);URL.revokeObjectURL(url);
  stopCam();setScene(c,w,h);sheet(false);toast('Photo as the scene')});
const vid=$('#cam');let camStream=null;
async function startCam(){try{camStream=await navigator.mediaDevices.getUserMedia({video:{facingMode:{ideal:'environment'},width:{ideal:1920},height:{ideal:1440}},audio:false});
    vid.srcObject=camStream;await vid.play();live=true;$('#perm').style.display='none'}catch(err){live=false;$('#perm').style.display='block'}}
function stopCam(){live=false;if(camStream){camStream.getTracks().forEach(t=>t.stop());camStream=null}vid.srcObject=null}
addEventListener('pointerdown',()=>{if(!live&&!camStream)startCam()},{once:true});document.addEventListener('visibilitychange',()=>{if(!document.hidden&&!live)startCam()});
$('#perm').addEventListener('pointerdown',e=>{e.stopPropagation();e.preventDefault();startCam()});

/* ---- shutter: the frame is recorded as a latent image; it only becomes a photo when the roll is developed ---- */
const shBtn=$('#shutter');
shBtn.addEventListener('pointerdown',e=>{ac();e.preventDefault();try{shBtn.setPointerCapture(e.pointerId)}catch(_){}shBtn.classList.add('dn');fire()});
['pointerup','pointercancel'].forEach(n=>shBtn.addEventListener(n,()=>shBtn.classList.remove('dn')));
function grab(){let el,w,h;if(live&&vid.videoWidth){el=vid;w=vid.videoWidth;h=vid.videoHeight}else{el=SCENE.el;w=SCENE.w;h=SCENE.h}
  const s=Math.min(1,2560/Math.max(w,h)),c=document.createElement('canvas');c.width=Math.round(w*s);c.height=Math.round(h*s);c.getContext('2d').drawImage(el,0,0,c.width,c.height);return c}
async function fire(){if(busy||rewinding||labOpen||sheetOn)return;
  if(backOpen){toast('Close the back first');return}
  if(S.frame>=S.len){toast('End of roll · rewind');return}
  if(!armed){toast('Wind the lever');levHint();return}
  busy=true;armed=false;levRest();snd('shutter');
  vfw.classList.add('bo');setTimeout(()=>vfw.classList.remove('bo'),190);
  const fp=previewFp();fp.burn=BURN[S.burnNext];const c=grab();
  const blob=await new Promise(r=>c.toBlob(r,'image/jpeg',.92));
  await put('raw',{i:S.frame,blob,p:fp,sw:c.width,sh:c.height});
  if(S.burnNext>0)S.burnNext--;S.frame++;S.shots++;wearDraw();sync(true);setTimeout(()=>snd('counter'),150);busy=false;
  if(S.frame>=S.len)toast('Roll finished · rewind it');}

/* ---- developing ---- */
function expSize(sw,sh){const sa=sw/sh;let H=sa<=FA?sw/FA:sh;H=Math.round(clamp(H,960,2400));return[Math.round(H*FA),H]}
const ob=(k,n,op)=>op?(k<3?[1,.8,.55][k]:(k===n-1?.5:.22)):0;
let labItems=[];
function showLab(items,developing){labOpen=true;$('#lab').classList.add('on');$('#labGrid').innerHTML='';labItems=[];
  $('#labTitle').textContent=developing?'DEVELOPING':'LAST ROLL';$('#labSub').textContent=items.length+' FRAMES';$('#labFill').style.width=developing?'0%':'100%';
  $('#labSave').style.display=developing?'none':'';$('#labClose').style.display=developing?'none':'';
  if(!developing)items.forEach(addFig)}
function addFig(it){const u=URL.createObjectURL(it.blob);labItems.push({u,it});const f=document.createElement('figure');
  f.innerHTML='<img alt=""><figcaption><span>'+it.cap.l+'</span><span>'+it.cap.r+'</span></figcaption>';f.firstChild.src=u;
  f.addEventListener('click',()=>showPrint(u,it));$('#labGrid').appendChild(f)}
function withBorder(src,fp,k,n){const b=fp.brd|0;if(!b)return src;const W=src.width,H=src.height;let l,t,r,bt;
  if(b===3){const o=Math.round(W*.014),v=[[.03,.024,.04,.03],[.036,.03,.028,.036],[.026,.034,.036,.024]][k%3];l=Math.round(W*v[0]);t=Math.round(W*v[1]);r=Math.round(W*v[2]);bt=Math.round(W*v[3]);
    const c=document.createElement('canvas');c.width=W+l+r+2*o;c.height=H+t+bt+2*o;const x=c.getContext('2d');
    x.fillStyle='#f3f1ea';x.fillRect(0,0,c.width,c.height);x.fillStyle='#050505';
    const rr=Math.round(W*.03);x.beginPath();x.roundRect?x.roundRect(o,o,c.width-2*o,c.height-2*o,rr):x.rect(o,o,c.width-2*o,c.height-2*o);x.fill();
    x.save();x.beginPath();const ri=Math.round(W*.012);x.roundRect?x.roundRect(o+l,o+t,W,H,ri):x.rect(o+l,o+t,W,H);x.clip();x.drawImage(src,o+l,o+t);x.restore();return c}
  if(b===1){l=r=t=Math.round(W*.06);bt=Math.round(W*.2)}else{l=r=Math.round(W*.035);t=bt=Math.round(W*.11)}
  const c=document.createElement('canvas');c.width=W+l+r;c.height=H+t+bt;const x=c.getContext('2d');
  if(b===1){x.fillStyle='#efeadc';x.fillRect(0,0,c.width,c.height);x.drawImage(src,l,t);
    const g=x.createLinearGradient(0,t,0,t+H);x.strokeStyle='rgba(0,0,0,.18)';x.lineWidth=2;x.strokeRect(l,t,W,H);
    x.fillStyle='#6a6458';x.font=Math.round(W*.034)+'px "DM Mono",ui-monospace,monospace';x.textBaseline='middle';x.fillText(FILMS[fi(fp)].name+' '+FILMS[fi(fp)].iso,l,t+H+bt*.5);
    x.textAlign='right';x.fillText(new Date(fp.ts).toLocaleDateString('en-GB').replace(/\//g,'.'),l+W,t+H+bt*.5)}
  else{x.fillStyle='#0b0b0a';x.fillRect(0,0,c.width,c.height);x.drawImage(src,l,t);
    const hw=Math.round(W*.035),hh=Math.round(W*.05),st=Math.round(W*.075);x.fillStyle='#e9e3d2';
    for(const y0 of[Math.round(t*.18),c.height-Math.round(t*.18)-hh])for(let px=st*.4;px<c.width;px+=st){x.beginPath();x.roundRect?x.roundRect(px,y0,hw,hh,hw*.25):x.rect(px,y0,hw,hh);x.fill()}
    x.fillStyle='#e8903a';x.font='600 '+Math.round(t*.2)+'px "DM Mono",ui-monospace,monospace';x.textBaseline='middle';
    const yy=c.height-t*.8;x.textAlign='left';x.fillText('\u25b8 '+(k+1)+'   '+(k+1)+'A',l,yy);x.textAlign='right';x.fillText(FILMS[fi(fp)].name+' '+FILMS[fi(fp)].iso,c.width-l,yy)}
  return c}
async function developRoll(raws0,tank){const raws=raws0||(await all('raw')).sort((a,b)=>a.i-b.i);if(!raws.length){S.frame=0;sync(true);return}
  DEV=true;showLab(raws,true);await sleep(400);const out=[],n=raws.length,pw=cv.width,ph=cv.height;
  for(let k=0;k<n;k++){const r=raws[k];let bmp;try{bmp=await createImageBitmap(r.blob)}catch(e){continue}
    FA=faOf(r.p.fmt||0,r.p.land);uploadSrc(bmp,bmp.width,bmp.height);if(bmp.close)bmp.close();
    const fp=Object.assign({},r.p);fp.burn=Math.max(fp.burn||0,ob(k,n,tank?tank.opened:S.opened));
    const[W,H]=expSize(r.sw,r.sh);cv.width=W;cv.height=H;freeRT();makeStamp(fp.ts);renderFilm(fp,14);
    const blob=await new Promise(res=>withBorder(ENG.capture(),fp,k,n).toBlob(res,'image/jpeg',.92));
    const it={i:k,blob,cap:{l:'No.'+String(k+1).padStart(2,'0')+' · '+LENSES[fp.lens].mm+'mm',r:fp.burn>0?'light-struck':FILMS[fi(fp)].name+' '+FILMS[fi(fp)].iso}};
    out.push(it);addFig(it);$('#labFill').style.width=Math.round((k+1)/n*100)+'%';$('#labSub').textContent=(k+1)+' / '+n;await sleep(60);
    $('#labScroll').scrollTop=1e5}
  DEV=false;FA=faOf(S.fmt,LAND);cv.width=pw;cv.height=ph;freeRT();makeStamp(Date.now());recalcCover();if(!live&&SCENE.el)uploadSrc(SCENE.el,SCENE.w,SCENE.h);dirty=true;
  await clr('dev');for(const it of out)await put('dev',it);
  if(tank){await tdel(tank.id);const x=TK.findIndex(t=>t.id===tank.id);if(x>=0)TK.splice(x,1);tankTick()}
  else{await clr('raw');S.frame=0;S.opened=false;S.burnNext=0;armed=true;levRest()}
  FA=faOf(S.fmt,LAND);sync(true);
  $('#labTitle').textContent='DEVELOPED';$('#labSave').style.display='';$('#labClose').style.display=''}
$('#labClose').addEventListener('click',()=>{labOpen=false;$('#lab').classList.remove('on');labItems.forEach(x=>URL.revokeObjectURL(x.u));labItems=[]});
$('#labSave').addEventListener('click',()=>saveBlobs(labItems.map(x=>x.it.blob),labItems.map((x,i)=>'darkslide-'+String(i+1).padStart(2,'0')+'.jpg')));
let curIt=null;
function showPrint(u,it){curIt=it;$('#pimg').src=u;$('#capL').textContent=it.cap.l;$('#capR').textContent=it.cap.r;$('#print').classList.add('on')}
$('#pClose').addEventListener('click',()=>$('#print').classList.remove('on'));
$('#pSave').addEventListener('click',()=>{if(curIt)saveBlobs([curIt.blob],['darkslide-'+String(curIt.i+1).padStart(2,'0')+'.jpg'])});
/* last developed roll: long-press the film chip */
let kp=null;$('#chip').addEventListener('pointerdown',()=>{kp=setTimeout(async()=>{longChip=true;sheet(false);if(backOpen||S.frame>0)return;const d=await all('dev');if(!d.length){toast('No developed roll yet');return}showLab(d.sort((a,b)=>a.i-b.i),false)},650)});
['pointerup','pointercancel'].forEach(n=>$('#chip').addEventListener(n,()=>clearTimeout(kp)));

/* ---- preview loop ---- */
let lastT=0;
function loop(t){requestAnimationFrame(loop);
  if(labOpen&&!$('#lab').classList.contains('on'))labOpen=false;
  if(labOpen)return;
  if(live&&vid.readyState>=2&&vid.videoWidth){if(t-lastT<30)return;lastT=t;uploadSrc(vid,vid.videoWidth,vid.videoHeight);dirty=true}
  if(dirty){renderFilm(previewFp(),6);dirty=false}}

/* ---- fit: full-bleed. The stage is 390 wide and as tall as the screen needs ---- */
function fit(){const f=$('#fit'),w=f.clientWidth,h=f.clientHeight,wasL=LAND;
  LAND=false;
  if(LAND){SC=Math.min(h/390,1.8);SH=390;SW=Math.max(390,Math.round(w/SC))}
  else{SC=Math.min(w/390,1.6,h/700);SH=Math.max(700,Math.round(h/SC));SW=390}
  document.body.classList.toggle('land',LAND);
  const st=$('#stage');st.style.width=SW+'px';st.style.height=SH+'px';st.style.transform='scale('+SC+')';
  if(!labOpen){cv.width=Math.round(SW*420/390);cv.height=Math.round(SH*420/390);freeRT()}
  wc.width=SW*2;wc.height=SH*2;wc.style.width=SW+'px';wc.style.height=SH+'px';
  if(!DEV){FA=faOf(S.fmt,LAND);recalcCover();makeStamp(Date.now())}
  layoutFrame();wearDraw();dirty=true}
addEventListener('resize',fit);

/* ================= boot ================= */
(async()=>{
  makeBrushedNone();
  const d=demoScene();setScene(d,d.width,d.height);makeStamp(Date.now());
  try{sdb=await sopen();Object.assign(RAW,await sgetAll())}catch(e){sdb=null}packN();
  fit();setFormat(S.fmt||0);drawFilms();setLP(S.lens*72,false);sync(true);levRest(true);
  let raws=[];try{db=await idb();raws=await all('raw');for(const r of await tall())TK.push({id:r.id,ready:r.ready,n:r.items.length,film:r.film})}catch(e){db=null}tankTick();if(raws.length!==S.frame){S.frame=raws.length;sync(true)}
  requestAnimationFrame(loop);
  toast('Wind · shoot · rewind to develop');
  startCam();
})();
function makeBrushedNone(){}
window.__latent=window.__darkslide={S,renderFilm,previewFp,developRoll,fire,all,finishRoll,developTank,TK,tankTick,wind:()=>{armed=true;levRest()},openBack,sheet};
})();
