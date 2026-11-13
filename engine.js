/* ================= PixiEngine: PixiJS 7 render pipeline =================
   source Sprite(s) -> [BlurFilter] + ColorMatrixFilter (per-preset grade)
   + bloom / halation (bright duplicate sprites, blurred, SCREEN)
   + light leaks / burn (SCREEN) + vignette PNG-style texture + dust texture
   + tiling noise grain (overlay emulated with MULTIPLY + ADD: iOS has no advanced blend modes)
   + LED date stamp + viewfinder dim. Capture = renderer.extract.canvas(renderTexture).            */
const _rng=(a)=>()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296};
const _I5=()=>[1,0,0,0,0, 0,1,0,0,0, 0,0,1,0,0, 0,0,0,1,0, 0,0,0,0,1];
const _mul5=(A,B)=>{const C=new Array(25).fill(0);for(let i=0;i<5;i++)for(let j=0;j<5;j++){let s=0;for(let k=0;k<5;k++)s+=A[i*5+k]*B[k*5+j];C[i*5+j]=s}return C};
const _gain=(r,g,b,o)=>{o=o||[0,0,0];const m=_I5();m[0]=r;m[6]=g;m[12]=b;m[4]=o[0];m[9]=o[1];m[14]=o[2];return m};
/* preset -> one 5x5 colour matrix (apply order: WB, exposure, crosstalk, saturation/mono, contrast, fade, split tone) */
function gradeMatrix(P){
  let M=_I5();const ap=m=>{M=_mul5(m,M)};
  ap(_gain(1+(P.temp||0)*.16,1-(P.tint||0)*.10,1-(P.temp||0)*.20));
  const e=Math.pow(2,(P.exposure||0)*.8);ap(_gain(e,e,e));
  if(P.xt){const m=_I5();for(let i=0;i<3;i++)for(let j=0;j<3;j++)m[i*5+j]=P.xt[i*3+j];ap(m)}
  const lw=[.2126,.7152,.0722];
  if(P.mono){const w=P.mw||[.3,.55,.15],m=_I5();for(let i=0;i<3;i++)for(let j=0;j<3;j++)m[i*5+j]=w[j];ap(m)}
  else{const s=P.saturation==null?1:P.saturation,m=_I5();for(let i=0;i<3;i++)for(let j=0;j<3;j++)m[i*5+j]=(1-s)*lw[j]+(i===j?s:0);ap(m)}
  const c=1+((P.contrast||1)-1)*.8;ap(_gain(c,c,c,[.5*(1-c),.5*(1-c),.5*(1-c)]));
  const f=P.fade||0;ap(_gain(1-f,1-f,1-f,[f*.8,f*.8,f*.8]));
  const st=P.shadowTone||[0,0,0],ht=P.highlightTone||[0,0,0];
  ap(_gain(1+ht[0]*2,1+ht[1]*2,1+ht[2]*2,[st[0]*.7,st[1]*.7,st[2]*.7]));
  ap(_gain(.9,.9,.9,[.015,.015,.015]));   // highlight headroom: ColorMatrix clamps, so pre-compress
  return M;
}
/* bright-pass matrix applied AFTER the grade: out = tint * k * (x - thr)   (per-channel or luma-based) */
function brightMatrix(G,thr,tint,luma){
  const k=1/Math.max(.05,1-thr),B=_I5(),lw=[.2126,.7152,.0722];
  for(let i=0;i<3;i++){const t=tint?tint[i]:1;for(let j=0;j<3;j++)B[i*5+j]=t*k*(luma?lw[j]:(i===j?1:0));B[i*5+4]=-t*k*thr}
  return _mul5(B,G);
}
class PixiEngine{
  constructor(canvas){
    if(!window.PIXI)throw new Error('PixiJS не загрузился');
    const P=PIXI;this.W=canvas.width;this.H=canvas.height;
    this.app=new P.Application({view:canvas,width:this.W,height:this.H,backgroundColor:0x000000,antialias:false,resolution:1,autoDensity:false,preserveDrawingBuffer:true,autoStart:false,powerPreference:'high-performance'});
    this.app.ticker.stop();this.R=this.app.renderer;this.stage=this.app.stage;
    this.srcCv=document.createElement('canvas');this.srcCv.width=this.srcCv.height=4;this.srcCx=this.srcCv.getContext('2d');
    this._mkSrcTex();
    // generated textures (PNG-style canvases)
    this.texVig=this._vigTex();this.texDust=this._dustTex();this.texBlob=this._blobTex();this.texBurn=this._burnTex();
    this.texGM=this._grainTex(true);this.texGA=this._grainTex(false);
    // scene graph
    this.baseC=this._grid();this.stage.addChild(this.baseC);
    this.blurF=new P.BlurFilter(1,2,1);this.cmF=new P.ColorMatrixFilter();
    this.bloomRoot=new P.Container();this.bloomC=this._grid();this.bloomRoot.addChild(this.bloomC);this.bloomRoot.scale.set(.5);
    this.halRoot=new P.Container();this.halC=this._grid();this.halRoot.addChild(this.halC);this.halRoot.scale.set(.5);
    this.bloomCM=new P.ColorMatrixFilter();this.bloomBl=new P.BlurFilter(8,3,1);this.bloomC.filters=[this.bloomCM,this.bloomBl];
    this.halCM=new P.ColorMatrixFilter();this.halBl=new P.BlurFilter(16,3,1);this.halC.filters=[this.halCM,this.halBl];
    this.bloomRT=P.RenderTexture.create({width:Math.max(2,this.W>>1),height:Math.max(2,this.H>>1)});
    this.halRT=P.RenderTexture.create({width:Math.max(2,this.W>>1),height:Math.max(2,this.H>>1)});
    this.bloomS=new P.Sprite(this.bloomRT);this.bloomS.blendMode=P.BLEND_MODES.SCREEN;this.stage.addChild(this.bloomS);
    this.halS=new P.Sprite(this.halRT);this.halS.blendMode=P.BLEND_MODES.SCREEN;this.stage.addChild(this.halS);
    const sp=(tex,bm)=>{const s=new P.Sprite(tex);if(bm!=null)s.blendMode=bm;this.stage.addChild(s);return s};
    this.leak1=sp(this.texBlob,P.BLEND_MODES.SCREEN);this.leak2=sp(this.texBlob,P.BLEND_MODES.SCREEN);
    this.burnS=sp(this.texBurn,P.BLEND_MODES.SCREEN);this.burnW=sp(P.Texture.WHITE,P.BLEND_MODES.SCREEN);
    this.vigS=sp(this.texVig);this.dustS=sp(this.texDust);
    this.grainM=new P.TilingSprite(this.texGM,64,64);this.grainM.blendMode=P.BLEND_MODES.MULTIPLY;this.stage.addChild(this.grainM);
    this.grainA=new P.TilingSprite(this.texGA,64,64);this.grainA.blendMode=P.BLEND_MODES.ADD;this.stage.addChild(this.grainA);
    this.stampS=new P.Sprite(P.Texture.EMPTY);this.stage.addChild(this.stampS);this._stampKey='';
    this.dimG=new P.Graphics();this.stage.addChild(this.dimG);
    this.capRT=null;
  }
  _mkSrcTex(){
    const P=PIXI;if(this.srcTex)this.srcTex.destroy(true);
    const bt=new P.BaseTexture(this.srcCv,{scaleMode:P.SCALE_MODES.LINEAR,mipmap:P.MIPMAP_MODES.OFF});
    this.srcTex=new P.Texture(bt);this._sprites&&this._sprites.forEach(s=>s.texture=this.srcTex);
  }
  _grid(){
    const P=PIXI,c=new P.Container();c.tiles=[];
    for(let dy=-1;dy<=1;dy++)for(let dx=-1;dx<=1;dx++){const s=new P.Sprite(this.srcTex);s.anchor.set(.5);s.dx=dx;s.dy=dy;c.addChild(s);c.tiles.push(s);(this._sprites=this._sprites||[]).push(s)}
    return c;
  }
  _place(c,cx,cy,sw,sh,W,H){
    const tw=this.srcCv.width,th=this.srcCv.height;
    for(const s of c.tiles){
      const x=cx+s.dx*sw,y=cy+s.dy*sh;
      s.visible=!(x+sw/2<0||x-sw/2>W||y+sh/2<0||y-sh/2>H);       // mirrored neighbours only where they show
      s.position.set(x,y);s.scale.set((s.dx?-1:1)*sw/tw,(s.dy?-1:1)*sh/th);
    }
  }
  /* ---- texture factories (canvas PNGs) ---- */
  _vigTex(){const n=128,c=document.createElement('canvas');c.width=c.height=n;const x=c.getContext('2d'),d=x.createImageData(n,n);
    for(let j=0;j<n;j++)for(let i=0;i<n;i++){const u=(i+.5)/n*2-1,v=(j+.5)/n*2-1,r=Math.hypot(u,v)/Math.SQRT2,q=1.9*r,a=1-1/Math.pow(1+q*q,2);const k=(j*n+i)*4;d.data[k]=d.data[k+1]=d.data[k+2]=0;d.data[k+3]=Math.round(255*Math.min(1,a*1.05))}
    x.putImageData(d,0,0);return PIXI.Texture.from(c)}
  _blobTex(){const n=256,c=document.createElement('canvas');c.width=c.height=n;const x=c.getContext('2d'),g=x.createRadialGradient(n/2,n/2,0,n/2,n/2,n/2);
    g.addColorStop(0,'rgba(255,255,255,1)');g.addColorStop(.35,'rgba(255,255,255,.55)');g.addColorStop(1,'rgba(255,255,255,0)');x.fillStyle=g;x.fillRect(0,0,n,n);return PIXI.Texture.from(c)}
  _burnTex(){const c=document.createElement('canvas');c.width=256;c.height=4;const x=c.getContext('2d'),g=x.createLinearGradient(0,0,256,0);
    g.addColorStop(0,'rgba(255,200,120,1)');g.addColorStop(.12,'rgba(255,110,25,.85)');g.addColorStop(.5,'rgba(255,66,10,.3)');g.addColorStop(1,'rgba(255,60,10,0)');x.fillStyle=g;x.fillRect(0,0,256,4);return PIXI.Texture.from(c)}
  _grainTex(mul){const n=256,c=document.createElement('canvas');c.width=c.height=n;const x=c.getContext('2d'),d=x.createImageData(n,n),R=_rng(mul?1234:98765);
    for(let i=0;i<n*n;i++){const g=(R()+R()+R())/3,v=mul?Math.round(255*(1-g)):Math.round(255*g*.9);d.data[i*4]=d.data[i*4+1]=d.data[i*4+2]=v;d.data[i*4+3]=255}
    x.putImageData(d,0,0);const t=PIXI.Texture.from(c);t.baseTexture.wrapMode=PIXI.WRAP_MODES.REPEAT;return t}
  _dustTex(){const n=1024,c=document.createElement('canvas');c.width=c.height=n;const x=c.getContext('2d'),R=_rng(777);
    x.fillStyle='#fff';
    for(let i=0;i<70;i++){const r=.45+Math.pow(R(),4)*1.5;x.globalAlpha=.35+R()*.5;x.beginPath();x.arc(R()*n,R()*n,r,0,7);x.fill()}
    x.strokeStyle='#fff';
    for(let i=0;i<7;i++){x.globalAlpha=.28+R()*.25;x.lineWidth=.7+R()*.5;const sx=R()*n,sy=R()*n,L=30+R()*90,a=R()*6.28;x.beginPath();x.moveTo(sx,sy);x.quadraticCurveTo(sx+Math.cos(a)*L*.6+(R()-.5)*40,sy+Math.sin(a)*L*.6+(R()-.5)*40,sx+Math.cos(a)*L,sy+Math.sin(a)*L);x.stroke()}
    for(let i=0;i<3;i++){x.globalAlpha=.1+R()*.1;x.lineWidth=.8;const sx=R()*n;x.beginPath();x.moveTo(sx,R()*n*.3);x.lineTo(sx+(R()-.5)*8,n*(.5+R()*.5));x.stroke()}
    return PIXI.Texture.from(c)}
  _stampTex(S,col,hot){
    const g=S.stamp,u=40,pad=26,cw=Math.ceil(g.width*u+pad*2),ch=Math.ceil(1.9*u+pad*2),c=document.createElement('canvas');c.width=cw;c.height=ch;const x=c.getContext('2d');
    const SEG={0:'abcdef',1:'bc',2:'abdeg',3:'abcdg',4:'bcfg',5:'acdfg',6:'acdefg',7:'abc',8:'abcdefg',9:'abcdfg'};
    const rect=(sx,sy,w,h)=>x.fillRect(pad+sx,pad+sy,w,h),t=.17*u,w=.95*u,h=.85*u;
    const css=a=>'rgb('+a.map(v=>Math.round(Math.min(1,v)*255)).join(',')+')';
    x.shadowColor=css(col);x.shadowBlur=u*.55;x.fillStyle=css(hot);
    g.glyphs.forEach((gl,i)=>{const ox=g.xs[i]*u;
      if(gl===10){rect(ox,0,t,.5*u);return}if(gl===11){rect(ox,1.75*u-t,t,t);return}
      const s=SEG[gl]||'';
      if(s.includes('a'))rect(ox+t*.5,0,w-t,t);if(s.includes('g'))rect(ox+t*.5,h-t/2,w-t,t);if(s.includes('d'))rect(ox+t*.5,2*h-t,w-t,t);
      if(s.includes('f'))rect(ox,t*.5,t,h-t);if(s.includes('b'))rect(ox+w-t,t*.5,t,h-t);
      if(s.includes('e'))rect(ox,h+t*.1,t,h-t);if(s.includes('c'))rect(ox+w-t,h+t*.1,t,h-t)});
    return {tex:PIXI.Texture.from(c),pad,u};
  }
  /* ---- source ---- */
  setSource(el){
    const w0=el.videoWidth||el.naturalWidth||el.displayWidth||el.width,h0=el.videoHeight||el.naturalHeight||el.displayHeight||el.height;if(!w0||!h0)return;
    const k=Math.min(1,2048/Math.max(w0,h0)),w=Math.max(2,Math.round(w0*k)),h=Math.max(2,Math.round(h0*k));
    if(this.srcCv.width!==w||this.srcCv.height!==h){this.srcCv.width=w;this.srcCv.height=h;this._mkSrcTex()}
    this.srcCx.drawImage(el,0,0,w,h);this.srcTex.baseTexture.update();
  }
  /* ---- render ---- */
  render(P,S,W,H){
    const PX=PIXI;W=Math.max(2,W|0);H=Math.max(2,H|0);
    if(W!==this.W||H!==this.H){this.W=W;this.H=H;this.R.resize(W,H);this.bloomRT.resize(Math.max(2,W>>1),Math.max(2,H>>1));this.halRT.resize(Math.max(2,W>>1),Math.max(2,H>>1))}
    const sc=Math.max(W,H)/1000,view=S.view||[1,1],fW=W/view[0],fH=H/view[1],cx=W/2,cy=H*(.5-(S.shift||0)),fx=cx-fW/2,fy=cy-fH/2;
    const tw=this.srcCv.width,th=this.srcCv.height,sa=tw/th,FA=S.frameA||fW/fH,z=P.zoom||1;
    let sw,sh;if(sa>FA){sh=fH*z;sw=sh*sa}else{sw=fW*z;sh=sw/sa}
    // 1 · grade + optical softness
    const G=gradeMatrix(P);this.cmF.matrix=G.slice(0,20);
    const bl=(P.softness||0)*2.4*sc;
    if(bl>.35){this.blurF.strength=bl;this.baseC.filters=[this.blurF,this.cmF]}else this.baseC.filters=[this.cmF];
    this.baseC.filterArea=new PX.Rectangle(0,0,W,H);
    this._place(this.baseC,cx,cy,sw,sh,W,H);
    // 2 · bloom + halation (half-res bright duplicates)
    const bloomOn=(P.bloom||0)>.04,halOn=(P.halation||0)>.04;
    if(bloomOn){
      this.bloomCM.matrix=brightMatrix(G,Math.min(.9,(P.bloomThreshold||.6)+.1),null,false).slice(0,20);
      this.bloomBl.strength=(5+9*(P.bloomWide||.5))*(P.bloomRadius||1)*sc;
      this.bloomC.filterArea=new PX.Rectangle(0,0,W,H);this._place(this.bloomC,cx,cy,sw,sh,W,H);
      this.R.render(this.bloomRoot,{renderTexture:this.bloomRT,clear:true});
      this.bloomS.width=W;this.bloomS.height=H;this.bloomS.alpha=Math.min(.9,(P.bloom||0)*.7);
    }
    this.bloomS.visible=bloomOn;
    if(halOn){
      this.halCM.matrix=brightMatrix(G,.62,P.halationColor||[1,.25,.05],true).slice(0,20);
      this.halBl.strength=11*(P.halationRadius||1)*sc;
      this.halC.filterArea=new PX.Rectangle(0,0,W,H);this._place(this.halC,cx,cy,sw,sh,W,H);
      this.R.render(this.halRoot,{renderTexture:this.halRT,clear:true});
      this.halS.width=W;this.halS.height=H;this.halS.alpha=Math.min(1,(P.halation||0)*.75);
    }
    this.halS.visible=halOn;
    // 3 · leaks / burn
    const R=_rng(Math.floor(S.leakSeed||0)+5),lc=P.leakColors||[[1,.3,.06],[1,.7,.2]],tint=a=>(Math.round(a[0]*255)<<16)|(Math.round(a[1]*255)<<8)|Math.round(a[2]*255);
    const blob=(s,col,size,amp)=>{const side=R();let x,y;if(side<.5){x=fx+(R()<.5?0:fW);y=fy+R()*fH}else{y=fy+(R()<.5?0:fH);x=fx+R()*fW}
      s.anchor.set(.5);s.position.set(x,y);s.width=s.height=size;s.tint=tint(col);s.alpha=amp;s.visible=amp>.01};
    const la=Math.min(.85,(P.leak||0)*.5*(S.leakGain==null?1:S.leakGain));
    blob(this.leak1,lc[0],fH*(.8+R()*.6),la);blob(this.leak2,lc[1],fH*(.5+R()*.5),la*.7);
    const br=S.burn||0;
    this.burnS.visible=this.burnW.visible=br>.001;
    if(br>.001){this.burnS.position.set(fx,fy);this.burnS.width=fW;this.burnS.height=fH;this.burnS.alpha=Math.min(1,br*.95);
      this.burnW.tint=0xff4a0a;this.burnW.position.set(fx,fy);this.burnW.width=fW;this.burnW.height=fH;this.burnW.alpha=br*.18}
    // 4 · vignette (semi-transparent texture), dust, grain
    this.vigS.position.set(fx,fy);this.vigS.width=fW;this.vigS.height=fH;this.vigS.alpha=Math.max(0,Math.min(.95,(P.vignette||0)*.8));
    const dR=_rng(Math.floor(S.shotSeed||0)+3),ds=dR()<.5?-1:1,dt=dR()<.5?-1:1;
    this.dustS.anchor.set(.5);this.dustS.position.set(cx,cy);this.dustS.scale.set(ds*fW/1024*1.0,dt*fH/1024*1.0);
    this.dustS.alpha=Math.min(.85,(P.dust||0)*.7);this.dustS.tint=P.dustDark?0x000000:0xfff4e4;
    const gs=Math.max(.7,(P.grainSize||1.5)*.6*sc),ga=Math.max(.03,Math.min(.06,.02+(P.grain||0)*.55));
    for(const [g,sd] of [[this.grainM,1],[this.grainA,2]]){
      g.position.set(fx,fy);g.width=fW;g.height=fH;g.tileScale.set(gs,gs);
      const gr=_rng(Math.floor(S.seed||0)*7+sd);g.tilePosition.set(gr()*256,gr()*256);g.alpha=ga;
    }
    // 5 · LED date stamp
    const stm=S.stamp&&P.stamp?S.stamp:null;
    if(stm&&stm.on){
      const col=P.stampColor||[1,.45,.1],hot=[Math.min(1,col[0]*.78+.22),Math.min(1,col[1]*.78+.2),Math.min(1,col[2]*.78+.12)],key=stm.glyphs.join(',')+'|'+col.join(',');
      if(key!==this._stampKey){this._stampKey=key;this._st=this._stampTex({stamp:stm},col,hot);this.stampS.texture=this._st.tex}
      const U=Math.max(fW,fH)*.0165,k=U/this._st.u;
      this.stampS.scale.set(k);
      this.stampS.position.set(fx+fW-fW*.045-stm.width*U-this._st.pad*k,fy+fH-fH*.055-1.9*U-this._st.pad*k);
      this.stampS.visible=true;
    }else this.stampS.visible=false;
    // 6 · viewfinder dim (outside the 35mm frame)
    const dg=this.dimG;dg.clear();
    if(S.dim&&(view[0]>1.002||view[1]>1.002)){dg.beginFill(0x000000,.64);
      dg.drawRect(0,0,W,Math.max(0,fy));dg.drawRect(0,fy+fH,W,Math.max(0,H-fy-fH));dg.drawRect(0,fy,Math.max(0,fx),fH);dg.drawRect(fx+fW,fy,Math.max(0,W-fx-fW),fH);dg.endFill()}
    this.R.render(this.stage);
  }
  /* full-quality snapshot of the current frame, filters included */
  capture(){
    const W=this.W,H=this.H;
    if(!this.capRT)this.capRT=PIXI.RenderTexture.create({width:W,height:H});
    else if(this.capRT.width!==W||this.capRT.height!==H)this.capRT.resize(W,H);
    this.R.render(this.stage,{renderTexture:this.capRT,clear:true});
    return this.R.extract.canvas(this.capRT);
  }
}

function stampLayout(P, now = new Date()){
  const y = P.stampYear || now.getFullYear(), m = now.getMonth()+1, d = now.getDate();
  const p2 = (n) => String(n).padStart(2, '0');
  let seq = [];
  if(P.stampFmt === 0){ const s = p2(y%100)+' '+p2(m)+' '+p2(d); seq = ["'", ...s.split('')]; }
  else { const s = String(y).padStart(4,'0')+'.'+p2(m)+'.'+p2(d); seq = s.split(''); }
  const glyphs = [], xs = []; let x = 0;
  for(const ch of seq){
    if(ch === ' '){ x += .7; continue; }
    if(ch === "'"){ glyphs.push(10); xs.push(x); x += .55; continue; }
    if(ch === '.'){ glyphs.push(11); xs.push(x); x += .6; continue; }
    glyphs.push(+ch); xs.push(x); x += 1.3;
  }
  return { on:true, glyphs, xs, width:x };
}
