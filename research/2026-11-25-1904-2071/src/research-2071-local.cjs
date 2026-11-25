const fs = require('fs');
const nP = 2, nL = Number(process.argv[2] || 2), n = nP+nL;
if(n>5) throw new Error('This enumerator stores at most 32 truth-table rows.');
const rows=1<<n;
const truthMask=rows===32 ? 0xffffffff : (2**rows-1);
const variables=Array.from({length:n},(_,i)=>{
  let v=0;for(let x=0;x<rows;x++)if((x>>>i)&1)v=(v|(1<<x))>>>0;return v;
});
const targets=new Map();
for(let graph=1;graph<(1<<(nP*nL));graph++){
  let common=0;for(let l=0;l<nL;l++)if((graph&(1<<l))&&(graph&(1<<(nL+l))))common++;
  if(common>1)continue;
  let f=0;for(let x=0;x<rows;x++){
    let hit=false;for(let p=0;p<nP;p++)for(let l=0;l<nL;l++)
      if((graph&(1<<(p*nL+l)))&&((x>>>p)&1)&&((x>>>(nP+l))&1))hit=true;
    if(hit)f=(f|(1<<x))>>>0;
  }
  targets.set(f,{graph,minimum:null,leastCircuits:0,topStuckLeast:0,badLeast:0});
}
const gates=[], values=[...variables], deps=variables.map(()=>0), colours=variables.map((_,i)=>i<nP?1:2);
let nodes=0, leafCount=0, witnesses=[],dirtyLeast=0,doubleLeast=0,dirtyDoubleLeast=0;
function singleRead(base,other){
  const singleton=1<<base;
  const d=Array.from({length:n},(_,w)=>w===other);
  for(const g of gates){
    const a=!!(values[g.a]>>>singleton&1),b=!!(values[g.b]>>>singleton&1);
    d.push(g.op==='or'?(d[g.a]||d[g.b]):((a&&d[g.b])||(d[g.a]&&b)));
  }
  return d.at(-1);
}
function topStuck(f){
  const readers=Array.from({length:n+gates.length},()=>[]);
  gates.forEach((g,j)=>{readers[g.a].push(j);readers[g.b].push(j)});
  const eligible=Array(gates.length).fill(false);
  for(let j=gates.length-1;j>=0;j--){
    if(gates[j].op!=='or')continue;
    const rs=[...new Set(readers[n+j])];
    eligible[j]=j===gates.length-1||(rs.length===1&&eligible[rs[0]]);
  }
  for(let w=0;w<values.length;w++){
    const below=((values[w]&(~f))>>>0)===0;
    const rs=readers[w];
    if(below&&rs.some(j=>gates[j].op==='or')&&rs.some(j=>!eligible[j]))return false;
  }
  return true;
}
function visit(depth,limit,bad){
  nodes++;
  if(depth===limit){
    leafCount++;
    if(deps[n+depth-1]!==((1<<depth)-1))return;
    const f=values[n+depth-1],target=targets.get(f);
    if(!target)return;
    const stuck=topStuck(f);
    if(target.minimum===null)target.minimum=limit;
    if(target.minimum===limit){
      target.leastCircuits++;
      const dirty=gates.some((g,k)=>g.op==='and'&&((values[n+k]&~f)>>>0)!==0);
      if(dirty)dirtyLeast++;
      const double=[];
      for(let p=0;p<nP;p++)for(let l=0;l<nL;l++)if((target.graph>>(p*nL+l))&1)
        if(!singleRead(p,nP+l)&&!singleRead(nP+l,p))double.push([p,nP+l]);
      if(double.length)doubleLeast++;
      if(dirty&&double.length){dirtyDoubleLeast++;if(witnesses.length<10)witnesses.push({graph:target.graph,limit,gates:gates.map(g=>({...g})),double,dirty:true});}
      if(stuck)target.topStuckLeast++;
      if(stuck&&bad)target.badLeast++;
    }
    return;
  }
  const count=n+depth;
  for(let a=0;a<count;a++)for(let b=a+1;b<count;b++)for(let op=0;op<2;op++){
    const v=(op?(values[a]|values[b]):(values[a]&values[b]))>>>0;
    if(values.includes(v))continue;
    const colour=op&&colours[a]===colours[b]?colours[a]:0;
    const nextBad=bad||(!op&&!(colours[a]&&colours[b]&&colours[a]!==colours[b]));
    values.push(v);deps.push(deps[a]|deps[b]|(1<<depth));colours.push(colour);
    gates.push({op:op?'or':'and',a,b});
    visit(depth+1,limit,nextBad);
    gates.pop();values.pop();deps.pop();colours.pop();
  }
}
const started=Date.now();
for(let limit=1;limit<=5;limit++){
  visit(0,limit,false);
  console.log(JSON.stringify({nP,nL,limit,nodes,leafCount,targets:targets.size,found:[...targets.values()].filter(x=>x.minimum!==null).length,dirtyLeast,doubleLeast,dirtyDoubleLeast,seconds:(Date.now()-started)/1000}));
}
const result={nP,nL,method:'Finite diagnostic enumeration, not a Lean certificate or a proof of the plane task. Pairs are commutative; semantic duplicates and unused gates are pruned. No exhaustive claim outside these input and gate bounds.',nodes,leafCount,dirtyLeast,doubleLeast,dirtyDoubleLeast,targets:[...targets.values()],witnesses,seconds:(Date.now()-started)/1000};
fs.writeFileSync(`research-2071-local-${nP}x${nL}.json`,JSON.stringify(result,null,2));
