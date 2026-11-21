// Room-split push-optimal Sokoban solver: BFS over pushes per room.
import{mkdirSync,readdirSync,readFileSync,writeFileSync}from'node:fs';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const D=[[0,-1,'u'],[0,1,'d'],[-1,0,'l'],[1,0,'r']];
function P(t){const r=t.split('\n').filter(x=>x),w=Math.max(...r.map(x=>x.length)),W=new Uint8Array(w*r.length).fill(1),G=[],B=[];let p=0;
r.forEach((s,y)=>{for(let x=0;x<s.length;x++){const i=y*w+x,c=s[x];if(c=='#')continue;W[i]=0;if('.*+'.includes(c))G.push(i);if('$*'.includes(c))B.push(i);if('@+'.includes(c))p=i}});
return{w,W,G,B,p}}
function L(w,W,G){const d=new Int32Array(W.length).fill(-1),q=[...G];
for(const g of G)d[g]=0;
for(let i=0;i<q.length;i++){const c=q[i];for(const[dx,dy]of D){const v=dy*w+dx,b=c-v;if(W[b]||W[b-v]||d[b]>=0)continue;d[b]=d[c]+1;q.push(b)}}
return d}
function R(w,W,o,f,S,t,K){let l=f,n=0;K[n++]=f;S[f]=t;
while(n){const p=K[--n];if(p<l)l=p;for(const[dx,dy]of D){const q=p+dy*w+dx;if(!W[q]&&!o[q]&&S[q]!=t){S[q]=t;K[n++]=q}}}
return l}
function F(w,W,o,g,t){for(const a of[t,t-1,t-w,t-w-1]){const c=[a,a+1,a+w,a+w+1];
if(c.every(x=>W[x]||o[x])&&c.some(x=>o[x]&&!g[x]))return 1}return 0}
function A(w,W,o,f,t){if(f==t)return'';const v=new Int32Array(W.length).fill(-1),h=[],q=[f];v[f]=f;
for(let i=0;i<q.length;i++){const p=q[i];if(p==t)break;for(const[dx,dy,l]of D){const n=p+dy*w+dx;
if(W[n]||o[n]||v[n]>=0)continue;v[n]=p;h[n]=l;q.push(n)}}
let s='';for(let p=t;p!=f;p=v[p])s=h[p]+s;return s}
function S(b){const{w,W,G,B,p}=b,N=W.length,g=new Uint8Array(N);
for(const x of G)g[x]=1;const d=L(w,W,G);if(B.some(x=>d[x]<0))return null;
const o=new Uint8Array(N),Y=new Int32Array(N),Z=new Int32Array(N),K=new Int32Array(N);let T=0;
const key=(a,l)=>{let k=l;for(const x of a)k=k*N+x;return k};
const BA=[B],PA=[p],PR=[-1],PD=[-1],ix=new Map;
for(const x of B)o[x]=1;ix.set(key(B,R(w,W,o,p,Y,++T,K)),0);for(const x of B)o[x]=0;
let f=B.every(x=>g[x])?0:-1;
for(let h=0;f<0&&h<BA.length;h++){const a=BA[h];for(const x of a)o[x]=1;
R(w,W,o,PA[h],Y,++T,K);const s=T;
for(let j=0;j<a.length&&f<0;j++){const q=a[j];
for(let e=0;e<4;e++){const[dx,dy]=D[e],v=dy*w+dx,t=q+v;
if(Y[q-v]!=s||W[t]||o[t]||d[t]<0)continue;
o[q]=0;o[t]=1;const z=F(w,W,o,g,t);let k=-1,n=null;
if(!z){n=a.slice();n[j]=t;n.sort((x,y)=>x-y);k=key(n,R(w,W,o,q,Z,++T,K))}
o[t]=0;o[q]=1;if(z||ix.has(k))continue;
if(BA.length>=250000){for(const x of a)o[x]=0;return null}
ix.set(k,BA.length);BA.push(n);PA.push(q);PR.push(h);PD.push(e);
if(n.every(x=>g[x])){f=BA.length-1;break}}}
for(const x of a)o[x]=0}
if(f<0)return null;
const path=[];for(let s=f;s>0;s=PR[s])path.push(s);path.reverse();
let m='',pl=p,cur=B;
for(const s of path){const n=BA[s],fr=cur.find(x=>!n.includes(x)),to=n.find(x=>!cur.includes(x)),e=PD[s],[dx,dy]=D[e],v=dy*w+dx;
for(const x of cur)o[x]=1;m+=A(w,W,o,pl,fr-v);for(const x of cur)o[x]=0;m+=D[e][2];pl=fr;cur=n}
return{m,e:pl}}
function M(l){const{w,W,G,B,p}=l,v=L(w,W,G),r=Math.floor(p/w),C=new Uint8Array(W.length);
for(let i=r*w;i<(r+1)*w;i++)if(!W[i]&&v[i]<0)C[i]=1;
if(B.some(b=>C[b]))return null;
const part=new Int32Array(W.length).fill(-1),R2=[];
for(let s=0;s<W.length;s++){if(W[s]||C[s]||part[s]>=0)continue;const q=[s];part[s]=R2.length;
for(let i=0;i<q.length;i++)for(const[dx,dy]of D){const n=q[i]+dy*w+dx;
if(!W[n]&&!C[n]&&part[n]<0){part[n]=R2.length;q.push(n)}}
R2.push({B:[],G:[],d:0})}
for(const b of B)R2[part[b]].B.push(b);
for(const g of G)if(part[g]>=0)R2[part[g]].G.push(g);
if(G.some(g=>part[g]<0)||R2.some(x=>x.B.length!=x.G.length))return null;
return R2.filter(x=>x.B.length)}
function V(t){const l=P(t),R2=M(l);if(!R2){const r=S(l);return r?r.m:''}
let m='',p=l.p;
for(const r of R2){const W=l.W.slice();
for(const o of R2)if(o!=r)for(const b of o.d?o.G:o.B)W[b]=1;
const s=S({w:l.w,W,G:r.G,B:r.B,p});
if(!s)return'';m+=s.m;p=s.e;r.d=1}
return m}
for(const id of readdirSync(I).sort()){const m=V(readFileSync(I+'/'+id+'/level.txt','utf8'));
mkdirSync(O+'/'+id,{recursive:true});writeFileSync(O+'/'+id+'/solution.txt',m+'\n')}
