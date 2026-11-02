// Exact reference experiments for the proposed support acquisition.
// Executes in JavaScript BigInt; this is not a Rust, Python or Lean replay.
export class Refused extends Error {}
class Exhausted extends Error {}
const ZERO = [0n, 1n], ONE = [1n, 1n];
function bits(n) { return (n < 0n ? -n : n).toString(2).replace(/^0$/, "").length; }
function q(n, d = 1n) {
  if (d === 0n) throw new Refused("zero denominator");
  if (d < 0n) { n = -n; d = -d; }
  let a = n < 0n ? -n : n, b = d;
  while (b) { const r = a % b; a = b; b = r; }
  const v = [n / a, d / a];
  if (bits(v[0]) > 8192 || bits(v[1]) > 8192) throw new Exhausted("internal_rational_cap");
  return v;
}
const add = (a,b) => q(a[0]*b[1]+b[0]*a[1], a[1]*b[1]);
const neg = a => [-a[0], a[1]];
const sub = (a,b) => add(a,neg(b));
const mul = (a,b) => q(a[0]*b[0],a[1]*b[1]);
const div = (a,b) => q(a[0]*b[1],a[1]*b[0]);
const eq = (a,b) => a[0]===b[0] && a[1]===b[1];
const str = a => a[1]===1n ? String(a[0]) : a[0]+"/"+a[1];
function pow(a,n) { let out=ONE; for(let i=0;i<n;i++) out=mul(out,a); return out; }
function parse(s) {
  if (typeof s!=="string" || s.length>80 || !/^-?(?:0|[1-9][0-9]*)(?:\/[1-9][0-9]*)?$/.test(s))
    throw new Refused("rational grammar");
  const p=s.split("/"), v=q(BigInt(p[0]),p.length===1?1n:BigInt(p[1]));
  if (bits(v[0])>128 || bits(v[1])>128) throw new Refused("input_rational_cap");
  return v;
}
function tokens(raw) {
  if (typeof raw!=="string" || raw.length>262144 || /[^\x00-\x7f]/.test(raw))
    throw new Refused("wire size or encoding");
  const cleaned=raw.replace(/^[ \t\r\n\v\f]+|[ \t\r\n\v\f]+$/g,"");
  return cleaned ? cleaned.split(/[ \t\r\n\v\f]+/) : [];
}
function reader(raw) {
  const a=tokens(raw); let at=0;
  return {
    token() { if(at>=a.length) throw new Refused("missing token"); return a[at++]; },
    natural(cap) { const s=this.token(); if(!/^(?:0|[1-9][0-9]*)$/.test(s)) throw new Refused("natural grammar");
      const n=BigInt(s); if(n>BigInt(cap)) throw new Refused("natural cap"); return Number(n); },
    rational() { const s=this.token(); return {value:parse(s),literal:s}; },
    end() { if(at!==a.length) throw new Refused("trailing token"); }
  };
}
function trim(a) { while(a.length && a[a.length-1][0]===0n) a.pop(); return a; }
function pmul(a,b) {
  const c=Array.from({length:a.length+b.length-1},()=>ZERO);
  a.forEach((x,i)=>b.forEach((y,j)=>c[i+j]=add(c[i+j],mul(x,y))));
  return c;
}
function padd(a,b) {
  const c=Array.from({length:Math.max(a.length,b.length)},()=>ZERO);
  a.forEach((x,i)=>c[i]=add(c[i],x)); b.forEach((x,i)=>c[i]=add(c[i],x)); return c;
}
function peq(a,b) { a=trim(a.slice()); b=trim(b.slice()); return a.length===b.length && a.every((v,i)=>eq(v,b[i])); }
function evalPoly(p,x) { let y=ZERO; for(let i=p.length-1;i>=0;i--) y=add(p[i],mul(x,y)); return y; }
function solve(rows) {
  const n=rows.length;
  for(let c=0;c<n;c++) {
    const p=rows.findIndex((row,r)=>r>=c && row[c][0]!==0n);
    if(p<0) throw new Exhausted("singular_supported_interpolation");
    [rows[c],rows[p]]=[rows[p],rows[c]];
    const pivot=rows[c][c]; rows[c]=rows[c].map(v=>div(v,pivot));
    for(let r=0;r<n;r++) if(r!==c) {
      const f=rows[r][c]; rows[r]=rows[r].map((v,j)=>sub(v,mul(f,rows[c][j])));
    }
  }
  return rows.map(row=>row[n]);
}
function monicDivide(p,d) {
  const rem=p.slice(), out=Array.from({length:p.length-d.length+1},()=>ZERO);
  if(!eq(d[d.length-1],ONE)) throw new Exhausted("nonmonic_divisor");
  for(let top=p.length-1;top>=d.length-1;top--) {
    const k=top-d.length+1, a=rem[top]; out[k]=a;
    d.forEach((v,j)=>rem[k+j]=sub(rem[k+j],mul(a,v)));
  }
  if(rem.some(v=>v[0]!==0n)) throw new Exhausted("nonzero_division_remainder");
  return trim(out);
}
// Independent expansion of the existing weighted-square certificate language.
export function checkCertificate(c) {
  const l=c.level;
  if(!Number.isInteger(l)||l<1||l>8||c.coefficients.length!==l||c.moments.length!==l)
    throw new Refused("certificate level");
  const coefficients=c.coefficients.map(parse), moments=c.moments.map(parse);
  if(coefficients.every(x=>x[0]===0n)||!eq(moments[0],ONE)||moments.some(v=>v[0]<0n||v[0]>v[1]))
    throw new Refused("certificate normalization");
  const p=Array.from({length:l*(l-1)/2+1},()=>ZERO);
  coefficients.forEach((v,i)=>p[i*(i+1)/2]=v);
  if(c.nonnegative_terms.length<1||c.nonnegative_terms.length>16) throw new Refused("term cap");
  let expanded=[];
  for(const t of c.nonnegative_terms) {
    const w=parse(t.weight), f=t.square.map(parse);
    if(w[0]<0n||f.length<1||f.length>15||![0,1].includes(t.left)||![0,1].includes(t.right))
      throw new Refused("square domain");
    let a=pmul(f,f).map(v=>mul(v,w));
    if(t.left) a=[ZERO,...a];
    if(t.right) a=pmul(a,[ONE,neg(ONE)]);
    expanded=padd(expanded,a);
  }
  if(!peq(p,expanded)) throw new Refused("weighted-square identity mismatch");
  if(coefficients.reduce((v,c,i)=>add(v,mul(c,moments[i])),ZERO)[0]!==0n)
    throw new Refused("nonzero annihilation");
  return {support_cap:l-1,source_existence:false};
}
function wire(c) {
  const a=["COMMON_CERT_V1",String(c.level),...c.coefficients,...c.moments,String(c.nonnegative_terms.length)];
  for(const t of c.nonnegative_terms) a.push(t.weight,String(t.left),String(t.right),String(t.square.length),...t.square);
  return a.join(" ")+"\n";
}
export function acquire(raw) {
  const r=reader(raw);
  if(r.token()!=="COMMON_GENERATE_SUPPORT_V1") throw new Refused("generator wire version");
  const count=r.natural(3);
  if(count===0) throw new Refused("positive support required");
  const nodes=Array.from({length:count},()=>r.rational().value);
  if(nodes.some(x=>x[0]<=0n||x[0]>x[1])||new Set(nodes.map(str)).size!==count)
    throw new Refused("distinct candidate survivals in (0,1] required");
  const level=r.natural(8);
  if(level!==2*count+1) throw new Refused("exactly 2r+1 supplied moments required");
  const supplied=Array.from({length:level},()=>r.rational()); r.end();
  const moments=supplied.map(x=>x.value);
  if(!eq(moments[0],ONE)||moments.some(x=>x[0]<0n||x[0]>x[1])) throw new Refused("normalized moment domain");
  try {
    const exponents=Array.from({length:level},(_,i)=>i*(i+1)/2);
    const last=exponents[level-1], rows=[];
    for(const a of nodes) {
      rows.push([...exponents.slice(0,-1).map(e=>pow(a,e)),neg(pow(a,last))]);
      rows.push([...exponents.slice(0,-1).map(e=>e===0?ZERO:mul(q(BigInt(e)),pow(a,e-1))),
        neg(mul(q(BigInt(last)),pow(a,last-1)))]);
    }
    const coefficients=[...solve(rows),ONE];
    const p=Array.from({length:last+1},()=>ZERO);
    coefficients.forEach((v,i)=>p[exponents[i]]=v);
    let f=[ONE]; for(const a of nodes) f=pmul(f,[neg(a),ONE]);
    const quotient=monicDivide(p,pmul(f,f));
    if(!quotient.length||quotient[0][0]<=0n||quotient.some(v=>v[0]<0n))
      throw new Exhausted("quotient_not_in_supported_positive_language");
    const terms=[];
    quotient.forEach((v,j)=>{
      if(v[0]!==0n) terms.push({weight:str(v),left:j%2,right:0,
        square:[...Array.from({length:Math.floor(j/2)},()=>"0"),...f.map(str)]});
    });
    const certificate={schema:"common_sparse_certificate_v1",level,coefficients:coefficients.map(str),
      moments:supplied.map(x=>x.literal),nonnegative_terms:terms};
    let check; try { check=checkCertificate(certificate); }
    catch(e) { if(e instanceof Refused) return {status:"UNKNOWN",reason:"generated_certificate_not_accepted_by_existing_language"}; throw e; }
    const certificate_wire=wire(certificate);
    if(certificate_wire.length>262144) throw new Exhausted("generated_wire_cap");
    return {status:"GENERATED_AND_CHECKED",certificate,certificate_wire,check};
  } catch(e) {
    if(e instanceof Exhausted) return {status:"UNKNOWN",reason:e.message};
    throw e;
  }
}
export function lawRequest(nodes,weights,literals=false) {
  const n=nodes.map(parse),w=weights.map(parse),l=2*n.length+1;
  if(n.length!==w.length||w.reduce((v,x)=>add(v,x),ZERO)[0]===0n) throw new Error("fixture law");
  const moments=Array.from({length:l},(_,i)=>str(n.reduce((v,x,j)=>add(v,mul(w[j],pow(x,i*(i+1)/2))),ZERO)));
  if(literals) moments[0]="2/2";
  return "COMMON_GENERATE_SUPPORT_V1 "+n.length+" "+nodes.join(" ")+" "+l+" "+moments.join(" ");
}
function assert(ok,label) { if(!ok) throw new Error("FAIL "+label); }
export function runSuite() {
  const outcomes={generated:0,unknown:0,refused:0,mutation_rejections:0,permutation_equalities:0};
  const corpus=[];
  const expect=(raw,status,label)=>{
    let actual,result; try { result=acquire(raw); actual=result.status; }
    catch(e) { if(!(e instanceof Refused)) throw e; actual="REFUSED"; }
    assert(actual===status,label+": "+actual);
    outcomes[status==="REFUSED"?"refused":status==="UNKNOWN"?"unknown":"generated"]++;
    corpus.push({label,request:raw,expected:status,result});
    return result;
  };
  const fractions=["1/5","1/4","1/3","1/2","2/3","3/4","4/5","1"];
  for(const a of fractions) expect(lawRequest([a],["1"]),"GENERATED_AND_CHECKED","singleton "+a);
  for(let i=0;i<fractions.length;i++) for(let j=i+1;j<fractions.length;j++)
    for(const w of ["1/4","1/2","3/4"]) {
      const weights=[w,str(sub(ONE,parse(w)))],nodes=[fractions[i],fractions[j]];
      const result=expect(lawRequest(nodes,weights),"GENERATED_AND_CHECKED","two "+nodes+" "+w);
      const reverse=expect(lawRequest(nodes.slice().reverse(),weights.slice().reverse()),"GENERATED_AND_CHECKED","reverse "+nodes+" "+w);
      assert(result.certificate_wire===reverse.certificate_wire,"node order invariance"); outcomes.permutation_equalities++;
      for(const field of ["coefficient","moment","weight"]) {
        const changed=JSON.parse(JSON.stringify(result.certificate));
        if(field==="coefficient") changed.coefficients[0]=str(add(parse(changed.coefficients[0]),ONE));
        if(field==="moment") changed.moments[1]=str(add(parse(changed.moments[1]),q(1n,100n)));
        if(field==="weight") changed.nonnegative_terms[0].weight="-1";
        let rejected=false; try {checkCertificate(changed);} catch(e) {rejected=e instanceof Refused;}
        assert(rejected,"false certificate "+field); outcomes.mutation_rejections++;
      }
    }
  for(const nodes of [["1/4","1/2","3/4"],["1/3","2/3","1"],["1/5","1/2","4/5"]])
    for(const weights of [["1/3","1/3","1/3"],["1/2","1/4","1/4"]])
      expect(lawRequest(nodes,weights),"GENERATED_AND_CHECKED","three "+nodes+" "+weights);
  const spelling=expect(lawRequest(["2/4"],["1"],true),"GENERATED_AND_CHECKED","preserved rational spelling");
  assert(spelling.certificate.moments[0]==="2/2","literal moment spelling");
  expect("COMMON_GENERATE_SUPPORT_V1 1 1/2 3 1 1/2 1/7","UNKNOWN","moments mismatch");
  expect("COMMON_GENERATE_SUPPORT_V1 2 1/3 2/3 5 1 1/2 1/6 65/1458 1/2","UNKNOWN","high moment mismatch");
  const a="6000000000000/6000000000001";
  expect(lawRequest([a],["1"]),"UNKNOWN","derived transport cap");
  const good=lawRequest(["1/3","2/3"],["1/2","1/2"]);
  for(const [label,raw] of [
    ["empty",""],["version",good.replace("_V1","_V0")],["zero count","COMMON_GENERATE_SUPPORT_V1 0"],
    ["count cap","COMMON_GENERATE_SUPPORT_V1 4"],["leading count",good.replace("V1 2 ","V1 02 ")],
    ["duplicate",good.replace("1/3 2/3","1/3 2/6")],["zero node",good.replace("1/3","0")],
    ["negative node",good.replace("1/3","-1/3")],["node above one",good.replace("1/3","4/3")],
    ["float",good.replace("1/3","0.3")],["zero denominator",good.replace("1/3","1/0")],
    ["wrong level",good.replace(" 5 "," 4 ")],["trailing",good+" extra"],["truncated",good.slice(0,good.lastIndexOf(" "))],
    ["bad normalization",good.replace(" 5 1 "," 5 0 ")],["moment domain",good.replace(" 5 1 "," 5 2 ")],
    ["nonascii",good+"\u0080"],["bytes"," ".repeat(262145)],
    ["input bit cap",good.replace("1/3","1/340282366920938463463374607431768211456")]
  ]) expect(raw,"REFUSED",label);
  return {schema:"support_reference_experiments_v1",runtime:"functions.exec V8 JavaScript BigInt",outcomes,corpus,
    rust_compiled:false,lean_compiled:false,canonical_python_executed:false,source_existence_certified:false};
}
