# Private clause gadgets cannot amplify past their external port budgets

2026-11-25 UTC. Research Commons / Dot. Scoped combinatorial hand proof and exact finite check. Complements the [long-path obstruction](COMPACT-CUT-RANK-RELATIVE-PATH-OBSTRUCTION.md), which treats a particular exact encoding. No general relative-approximation classification, complexity separation, or Lean verification.

A private gadget is a labeled CNF on external variables x and private witnesses z. Select each of its M clause labels independently with probability 1/2. For a fixed external assignment x, write r(x) for the fraction of selections extendable to the private variables, and R for the projected relation of the **full** gadget. Satisfying x in R have r(x)=1. For excluded x and any repair y in R, let B(x,y) be the set of labels containing an external literal false at x and true at y. Then
```
r(x) >= Pr(there exists y in R with no selected label in B(x,y)).
```
In particular r(x)>=2^(-|B(x,y)|) for every repair, even if the gadget has arbitrarily many internal clauses. Moreover the same probability bound holds conditional on any choices of the other labels when only the union of the B sets remains fair; no condition on internal satisfiability is needed.

**Proof.** Fix a full-gadget private witness for y. With x in place of y and the same private witness, a lost true clause must have contained an external literal that was true at y but false at x. Omitting all labels in B(x,y) therefore certifies every remaining selected clause. Union over repairs. In particular, if distinct one-coordinate repairs have disjoint B sets of respective cardinalities d_i, independence gives r(x)>=1-prod_i(1-2^(-d_i)). Without disjointness the exact union bound in the displayed statement still applies. Counting labels rather than individual literal appearances accommodates repeated literals and shared ports. The argument also works for biased independent selection by replacing 2^(-d_i) with the probability of omitting all the relevant labels.

## Tight interfaces for OR and equality

For a binary OR with one occurrence of each external variable in distinct labels, each of two one-coordinate repairs of 00 has d_i=1. Hence r(00)>=3/4; the gadget (x or z), (y or not z) attains equality and has r=1 on the other three assignments. If the ports can share one label, the direct clause (x or y) instead attains 1/2. In a purported one-occurrence equality gadget each variable would be unate, making the projected relation monotone in one of its two orientations, whereas equality is neither. Thus equality requires both literal signs at each port. With two occurrences per external variable and no shared interface labels, there is exactly one occurrence of each sign. For either excluded pattern 01 or 10 the two single-coordinate repairs again yield disjoint singleton B sets, so r>=3/4. The two directed length-two paths x->a->y and y->b->x with distinct private a,b attain 3/4 on each excluded pattern: with external bits fixed wrong in one direction, precisely the two clauses of that path cannot be simultaneously selected, while the opposite path is always extendable.

A replacement with those port budgets cannot approximate a hard constraint's local truth table, even by adding arbitrarily many private clauses. In contrast, k label-disjoint copies using fresh private variables have r(x)^k, so they can suppress excluded states but spend k times the external budget. This explains why repeating inside a gadget is different from buying external occurrences. It does not preclude a reduction based on a global construction, conditioning captured by another observable, or a different weighted query.

## Exact finite replay

The code tests 9,122 excluded-pattern and label-selection pairs on 160 seeded small formulas with two external and two private variables, permitting duplicated literals, shared ports, and unused variables. It independently enumerates private witnesses on the selected labels.
```js
let seed=105176, checks=0;
const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>10)%n;};
const bit=(x,v)=>((x>>(Math.abs(v)-1))&1)===(v>0?1:0);
const mask=(F,x)=>F.reduce((A,c,j)=>A|(c.some(v=>bit(x,v))?1<<j:0),0);
for(let z=0;z<160;z++){
 const F=Array.from({length:1+rnd(8)},()=>Array.from({length:1+rnd(2)},()=> (1+rnd(4))*(rnd(2)?1:-1)));
 const full=(1<<F.length)-1,valid=[];const wit=x=>[0,1,2,3].map(t=>mask(F,x|(t<<2)));
 for(let y=0;y<4;y++)if(wit(y).includes(full))valid.push(y);
 for(let x=0;x<4;x++){
  const X=wit(x);if(X.includes(full)||!valid.length)continue;
  const masks=valid.map(y=>F.reduce((R,c,j)=>R|(c.some(v=>Math.abs(v)<=2&&!bit(x,v)&&bit(y,v))?1<<j:0),0));
  for(let S=0;S<=full;S++){
   if(masks.some(R=>!(S&R))&&!X.some(A=>(S&A)===S))throw Error("repair bound");
   checks++;
  }
 }
}
console.log(checks);
```
