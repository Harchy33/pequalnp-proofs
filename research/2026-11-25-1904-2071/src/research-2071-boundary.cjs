const fs=require('fs'),cp=require('child_process'),path=require('path');
const mode='twoStars',size=Number(process.argv[2]||9),restricted=false,honest=false,requireDouble=process.argv[3]==='double';
const n=9,side=2,fullRows=1<<n,conflictLimit=Number(process.argv[4]||1000000);
const edges=[[0,2],[0,3],[0,4],[0,5],[1,2],[1,6],[1,7],[1,8]];
// All inputs of size at most two detect any first unsafe AND (upstream
// R_meta_1904_493). The four maximal independent inputs certify the output
// together with the eight minimal positive inputs, by monotonicity.
const masks=Array.from({length:fullRows},(_,r)=>r).filter(r=>r.toString(2).replace(/0/g,'').length<=2);
for(let points=0;points<4;points++){
  let r=points;
  for(let l=2;l<n;l++)if(!edges.some(([p,q])=>q===l&&(points>>p&1)))r|=1<<l;
  if(!masks.includes(r))masks.push(r);
}
masks.sort((a,b)=>a-b);
const rows=masks.length;
const adjacent=(a,b)=>edges.some(([x,y])=>(a===x&&b===y)||(a===y&&b===x));
for(let a=0;a<n;a++)for(let b=0;b<n;b++)for(let c=0;c<n;c++){
  if(adjacent(a,b)&&adjacent(b,c)&&adjacent(c,a))throw Error('Triangle');
  for(let d=0;d<n;d++)if(a!==c&&b!==d&&adjacent(a,b)&&adjacent(b,c)&&adjacent(c,d)&&adjacent(d,a))throw Error('Four-cycle');
}
const covers=[];
for(let set=0;set<(1<<n);set++)if(edges.every(([a,b])=>(set>>a&1)||(set>>b&1)))covers.push({set,size:set.toString(2).replace(/0/g,'').length});
const minCover=Math.min(...covers.map(x=>x.size));
const target=r=>edges.some(([a,b])=>(r>>a&1)&&(r>>b&1));
const targetRow=r=>target(masks[r]);
let vars=0;const clauses=[],fresh=()=>++vars,add=(...c)=>clauses.push(c);
const one=xs=>{add(...xs);for(let i=0;i<xs.length;i++)for(let j=0;j<i;j++)add(-xs[i],-xs[j]);};
const and=(v,xs)=>{for(const x of xs)add(-v,x);add(v,...xs.map(x=>-x));};
const or=(v,xs)=>{for(const x of xs)add(v,-x);add(-v,...xs);};
const blocks=[];
for(let g=0;g<size;g++){
  const count=n+g,sa=Array.from({length:count},fresh),sb=Array.from({length:count},fresh),op=fresh();
  const a=Array.from({length:rows},fresh),b=Array.from({length:rows},fresh),z=Array.from({length:rows},fresh);
  one(sa);one(sb);
  for(let i=0;i<count;i++)for(let j=0;j<=i;j++)add(-sa[i],-sb[j]);
  for(let r=0;r<rows;r++){
    for(let w=0;w<count;w++)for(const [sel,v] of [[sa[w],a[r]],[sb[w],b[r]]]){
      if(w<n)add(-sel,(masks[r]>>w&1)?v:-v);
      else{const p=blocks[w-n].z[r];add(-sel,-v,p);add(-sel,v,-p);}
    }
    add(op,-z[r],a[r]);add(op,-z[r],b[r]);add(op,z[r],-a[r],-b[r]);
    add(-op,z[r],-a[r]);add(-op,z[r],-b[r]);add(-op,-z[r],a[r],b[r]);
  }
  blocks.push({sa,sb,op,a,b,z});
}
for(let r=0;r<rows;r++)add(targetRow(r)?blocks.at(-1).z[r]:-blocks.at(-1).z[r]);
if(honest)for(let g=0;g<size;g++)for(let r=0;r<rows;r++)if(!target(r))add(blocks[g].op,-blocks[g].z[r]);
if(requireDouble){
  const dirty=[];
  for(let g=0;g<size;g++)for(let r=0;r<rows;r++)if(!targetRow(r)){
    const d=fresh();and(d,[-blocks[g].op,blocks[g].z[r]]);dirty.push(d);
  }
  add(...dirty);
  for(const [base,other] of [[0,2],[2,0]]){
    const trace=[];
    for(let g=0;g<size;g++){
      const h=blocks[g],da=fresh(),db=fresh(),d=fresh();
      for(let w=0;w<n+g;w++)for(const [sel,v] of [[h.sa[w],da],[h.sb[w],db]]){
        if(w<n)add(-sel,w===other?v:-v);
        else{const p=trace[w-n];add(-sel,-v,p);add(-sel,v,-p);}
      }
      const ab=fresh(),ba=fresh(),andD=fresh(),orD=fresh();
      const singletonRow=masks.indexOf(1<<base);
      if(singletonRow<0)throw Error('Missing singleton');
      and(ab,[h.a[singletonRow],db]);and(ba,[da,h.b[singletonRow]]);or(andD,[ab,ba]);or(orD,[da,db]);
      add(-h.op,-d,orD);add(-h.op,d,-orD);add(h.op,-d,andD);add(h.op,d,-andD);
      trace.push(d);
    }
    add(-trace.at(-1));
  }
}
const uses=blocks.map((_,g)=>blocks.map((h,k)=>{
  if(k<=g)return null;const u=fresh();or(u,[h.sa[n+g],h.sb[n+g]]);return u;
}));
for(let g=0;g<size-1;g++)add(...uses[g].filter(Boolean));
if(restricted){
  const T=blocks.map(fresh),below=blocks.map(fresh),pureP=[],pureL=[],bad=[];
  const mux=(v,sels,prior,kind)=>{
    sels.forEach((sel,w)=>{
      if(w<n)add(-sel,(kind==='P'?w<side:w>=side)?v:-v);
      else{const p=prior[w-n];add(-sel,-v,p);add(-sel,v,-p);}
    });
  };
  for(let g=0;g<size;g++){
    const h=blocks[g],pA=fresh(),pB=fresh(),lA=fresh(),lB=fresh(),pg=fresh(),lg=fresh();
    mux(pA,h.sa,pureP,'P');mux(pB,h.sb,pureP,'P');mux(lA,h.sa,pureL,'L');mux(lB,h.sb,pureL,'L');
    and(pg,[h.op,pA,pB]);and(lg,[h.op,lA,lB]);pureP.push(pg);pureL.push(lg);
    const good1=fresh(),good2=fresh(),bg=fresh();and(good1,[pA,lB]);and(good2,[lA,pB]);and(bg,[-h.op,-good1,-good2]);bad.push(bg);
    and(below[g],h.z.filter((_,r)=>!target(r)).map(v=>-v));
    add(-T[g],h.op);
    if(g<size-1){
      const parents=[];
      for(let k=g+1;k<size;k++){
        const q=fresh();parents.push(q);add(-q,T[g]);add(-q,T[k]);add(-q,uses[g][k]);
        for(let j=g+1;j<size;j++)if(j!==k)add(-q,-uses[g][j]);
      }
      add(-T[g],...parents);
    }
  }
  add(...bad);
  for(let g=0;g<size;g++){
    const orRead=[];
    for(let k=g+1;k<size;k++){const q=fresh();and(q,[uses[g][k],blocks[k].op]);orRead.push(q);}
    const any=fresh();or(any,orRead);
    for(let k=g+1;k<size;k++)add(-below[g],-any,-uses[g][k],T[k]);
  }
}
const stem=`research-2071-${mode}-${size}${requireDouble?'-double':''}-boundary`;
fs.writeFileSync(stem+'.cnf',`p cnf ${vars} ${clauses.length}\n`+clauses.map(c=>c.join(' ')+' 0').join('\n')+'\n');
console.log(JSON.stringify({mode,size,requireDouble,vars,clauses:clauses.length,rows,edges,minCover,starUpper:edges.length+minCover-1,conflictLimit}));
const fd=fs.openSync(stem+'.solver.log','w');
const solver=(process.env.CADICAL || 'cadical');
const started=Date.now();
const run=cp.spawnSync(solver,['-c',String(conflictLimit),stem+'.cnf'],{stdio:['ignore',fd,fd]});fs.closeSync(fd);
const output=fs.readFileSync(stem+'.solver.log','utf8');
const result={mode,size,requireDouble,edges,minCover,starUpper:edges.length+minCover-1,conflictLimit,exit:run.status,signal:run.signal,seconds:(Date.now()-started)/1000,verdict:run.status===10?'SAT':run.status===20?'UNSAT (encoding only; no Lean certificate)':run.status===0?'UNKNOWN':'ERROR',exhausted:false};
if(run.status===10){
  const selected=new Set([...output.matchAll(/^v (.*)$/gm)].flatMap(m=>m[1].trim().split(/\s+/).map(Number)).filter(v=>v>0));
  for(let i=0;i<clauses.length;i++)if(!clauses[i].some(v=>v>0?selected.has(v):!selected.has(-v)))throw Error('Invalid model at clause '+i);
  const gates=blocks.map(h=>({op:selected.has(h.op)?'or':'and',a:h.sa.findIndex(v=>selected.has(v)),b:h.sb.findIndex(v=>selected.has(v))}));
  if(gates.some(g=>g.a<0||g.b<0))throw Error('Missing selector');
  const errors=[];
  for(let r=0;r<fullRows;r++){
    const wires=Array.from({length:n},(_,i)=>!!(r>>i&1));
    for(const g of gates)wires.push(g.op==='and'?wires[g.a]&&wires[g.b]:wires[g.a]||wires[g.b]);
    if(wires.at(-1)!==target(r))errors.push(r);
  }
  if(errors.length)throw Error('Circuit invalid on rows '+errors);
  const readers=Array.from({length:n+size},()=>[]),eligible=Array(size).fill(false),colours=Array.from({length:n},(_,i)=>i<side?1:2);
  gates.forEach((g,k)=>{readers[g.a].push(k);readers[g.b].push(k);colours.push(g.op==='or'&&colours[g.a]===colours[g.b]?colours[g.a]:0)});
  for(let g=size-1;g>=0;g--){const rs=[...new Set(readers[n+g])];eligible[g]=gates[g].op==='or'&&(g===size-1||(rs.length===1&&eligible[rs[0]]));}
  const below=Array.from({length:n+size},()=>true);
  for(let r=0;r<fullRows;r++)if(!target(r)){
    const wires=Array.from({length:n},(_,i)=>!!(r>>i&1));
    for(const g of gates)wires.push(g.op==='and'?wires[g.a]&&wires[g.b]:wires[g.a]||wires[g.b]);
    wires.forEach((v,w)=>{if(v)below[w]=false});
  }
  const topStuck=readers.every((rs,w)=>!below[w]||!rs.some(k=>gates[k].op==='or')||rs.every(k=>eligible[k]));
  const allAndClean=gates.every((g,k)=>g.op==='or'||below[n+k]);
  if(honest&&!allAndClean)throw Error('Honesty encoding failed independent verification');
  const traceAt=(base,other)=>{
    const actual=Array.from({length:n},(_,w)=>w===base),trace=Array.from({length:n},(_,w)=>w===other);
    for(const g of gates){
      trace.push(g.op==='or'?trace[g.a]||trace[g.b]:(actual[g.a]&&trace[g.b])||(trace[g.a]&&actual[g.b]));
      actual.push(g.op==='or'?actual[g.a]||actual[g.b]:actual[g.a]&&actual[g.b]);
    }
    return trace.at(-1);
  };
  const traces=[traceAt(0,2),traceAt(2,0)];
  if(requireDouble&&(allAndClean||traces.some(Boolean)))throw Error('Double-read encoding failed independent verification');
  const twoLevel=gates.every(g=>g.op==='or'||(colours[g.a]&&colours[g.b]&&colours[g.a]!==colours[g.b]));
  if(restricted&&(!topStuck||twoLevel))throw Error('Structural encoding failed independent verification');
  Object.assign(result,{gates,output:n+size-1,allAndClean,traces,encodedRows:rows,verifiedRows:fullRows});
}
fs.writeFileSync(stem+'.json',JSON.stringify(result,null,2));console.log(JSON.stringify(result));
