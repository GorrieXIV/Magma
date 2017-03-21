freeze;

import "psl2p.m": DihedralTrick, FindInvolution;
import "gl2.m": PGammaLD2;

/*
Constructively recognise and find maximal subgroups  of L(2,p^3).?
Recognition by Derek Holt.
Maximals by Colva Roney-Dougal
*/

/* This function produces the semilinear group, by 
 * looking for a random pair of involutions that 
 * generate a dihedral group of the correct order, p+1.
 * input is a group isomorphic to PSL and the prime p. In practice
 * this is currently used with the *standard* copy of PSL, as this 
 * is likely to have smaller degree than the "black box" PSL generated 
 * by the user. 
 */

function GetL2p3Semilin(group, p)

proc:= RandomProcess(group);

got_seed_invol:=false;
while not got_seed_invol do
    x:= Random(proc);
    o:= Order(x);
    q, r:= Quotrem(o, 2);
    if r eq 0 then
        invol:= x^q;
        got_seed_invol:= true;
        //"invol = ", invol;
    end if;
end while;

made_semilin:= false;
while not made_semilin do
    y:= invol^Random(proc);
    //"Order of product =", Order(invol*y);
    if Order(invol*y) eq Integers()!((p^3+1)/2) then
        made_semilin:= true;
    end if;
end while;

return sub<group|invol, y>;
end function;

/********************************************************/

/*
 * This function produces the subfield group SL(2, p) < SL(2, p^3). This is 
 * maximal.
 */
 
function GetSubfield(sl, p)

gens:= SetToSequence(Generators(SL(2, p)));
newgens:= [];

for i in [1..#gens] do
     Append(~newgens, sl!Eltseq(gens[i]));
end for;

return sub<sl|newgens>;

end function;

FindGeneratingPElement := function(G,g,p)
/* g should be element returned by FindInvolution(G).
 * Find a p-element y such that <g,y> = G.
 */
  local proc;

  GenG := function(g,y)
    local procb, z;
    //To test whether G=<g,y>, we do a quick probabilistic test using orders
    procb := RandomProcess(sub<G|g,y>);
    for i in [1..50] do
      z := Random(procb);
      if (p^3 * (p^3-1) * 15) mod Order(z) ne 0 then
        return true;
      end if;
    end for;
    return false;
  end function;

  proc := RandomProcess(G);
  y:=Random(proc);
  //while  y eq Id(G) or (p^3 - 1) mod Order(y) ne 0 do
  while  Order(y) le 2 or (p^3 - 1) mod Order(y) ne 0 do
    y:=Random(proc);
  end while;
  z := (y,y^Random(proc));
  while (Order(z) ne p) or (not GenG(g,z)) do
    z := (y,y^Random(proc));
  end while;
  return z;
end function;

/* In the following function, psl, apsl are standard copies of PSL(2,p^3) and
 * Aut(PSL(2,p^3)) = PGammaL(2,p^3).
 * group is our unknown almost simple group with socle dgroup isomorphic
 * to PSL(2,p^3).
 * We start by defining isomorphism dgroup -> psl and then extend to
 * monomorphism group -> apsl.
 */
MakeHomom := function(dgroup, group, p, psl, apsl, conj_invol, field_auto:
                      Print:=0)
  // for generators, we choose an involution (unique class) and another
  // random generating p-element.

  local procg, procdg, procp;
  a1 := FindInvolution(psl);
  b1 := FindGeneratingPElement(psl,a1,p);
  // try getting b1 to fix 1 - may help FPGroupStrong!
  for x in Fix(b1) do
   isc, g := IsConjugate(psl,x,1);
   if isc then a1:=a1^g; b1:=b1^g; break; end if;
  end for;

  // set up word group for isomorphism test
  psls:= sub< psl |  a1, b1 >;
  AssertAttribute(psls,"Order",#psl);
  ChangeBase(~psls,[1]);
  BSGS(psls);
  ReduceGenerators(~psls);
  t:=Cputime();
  F,phi := FPGroupStrong(psls);
  if Print gt 0 then print "Time for FPGroupStrong:",Cputime(t); end if;
  iwm := InverseWordMap(psls);
  Fgens := [F.i @ phi @ iwm : i in [1..Ngens(F)]];
  wg := Parent(Fgens[1]);

  // now look for required element in group
  a := FindInvolution(dgroup);
  b := FindGeneratingPElement(dgroup,a,p);

  procdg := RandomProcess(dgroup);
  gotisom := false;
  o1:=Order(a1*b1); o2:=Order(a1*b1^-1); o3:=Order((a1,b1));
  while not gotisom do
    //print "looping";
    if Order(a*b) ne o1 or Order (a*b^-1) ne o2 or Order((a,b)) ne o3 then
       b := b^Random(procdg);
       continue;
    end if;
    wgtoG := hom< wg->dgroup | [a, b] >;
    FtoG  := hom< F->dgroup  | [g @ wgtoG : g in Fgens ] >;
    gotisom := true;
    for r in Relations(F) do
      if not LHS(r) @ FtoG eq RHS(r) @ FtoG then
        gotisom := false; break;
      end if;
    end for;
    if not gotisom then
       b := b^Random(procdg);
    end if;
  end while;
  dgs := sub<dgroup|a,b>;
  AssertAttribute(dgs,"Order",#psl);

  homom := hom < dgs -> apsl | [a1,b1] >;

  ind := Index(group,dgroup);
  if ind eq 1 then
    return homom, F, phi;
  end if;

  procg:= RandomProcess(group);
  procp := RandomProcess(psl);

  if ind eq 2 or ind eq 6 then
      // get 2-element in outer automorphism group
      c := Random(procg);
      while c^3 in dgroup do c := Random(procg); end while;
      if not c^2 in dgroup then c:=c^3; end if;
      ac := (a^c) @ homom;  bc := (b^c) @ homom;

      c1 := conj_invol;
      g := DihedralTrick(a1^c1, ac, procp);
      c1 := c1*g;
      isc, g := IsConjugate(Centraliser(psl,ac),b1^c1,bc);
      if not isc then error "pgl error"; end if;
      c1 := c1*g;
      dgs := sub<group|a,b,c>;
      AssertAttribute(dgs,"Order",#psl*2);
      if ind eq 2 then
          return hom < dgs -> apsl | [a1,b1,c1] >, F, phi;
      end if;
  end if;

  // get 3-element in outer automorphism group
  d := Random(procg);
  while d^2 in dgroup do d := Random(procg); end while;
  if not d^3 in dgroup then d:=d^2; end if;
  ad := (a^d) @ homom;  bd := (b^d) @ homom;

  d1 := field_auto;
  g := DihedralTrick(a1^d1, ad, procp);
  d1 := d1*g;
  isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  if not isc then //d1^2 should do the trick
    d1 := d1^2;
    g := DihedralTrick(a1^d1, ad, procp);
    d1 := d1*g;
    isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
    if not isc then error "psigmal error"; end if;
  end if;
  d1 := d1*g;
  if ind eq 3 then
     dgs := sub<group|a,b,d>;
     AssertAttribute(dgs,"Order",#psl*3);
     return hom < dgs -> apsl | [a1,b1,d1] >, F, phi;
  end if;
  dgs := sub<group|a,b,c,d>;
  AssertAttribute(dgs,"Order",#psl*6);
  return hom < dgs -> apsl | [a1,b1,c1,d1] >, F, phi;

end function;

/*******************************************************************
*                   The main function                              *
* The intersections of _any_ almost simple group with socle        *
* PSL(2, p^3) are the point stabiliser; D_{p^3 - 1}, the           *
* imprimitive group; D_{p^3 + 1}, the superfield group;            *
* and PSL(2, p). We get one copy of each.                          *
********************************************************************/

function L2p3Identify(group, q : max := true, Print := 0)

fac:= Factorisation(q);
assert #fac eq 1 and fac[1][2] eq 3;

p := fac[1][1];
assert IsPrime(p);
assert p gt 2;

if Print gt 1 then "Making standard pgl"; end if;

gl:= GL(2, q);
sl := SL(2,q);
apsl := PGammaLD2(q);
factor := hom< gl->apsl | [apsl.1, apsl.2 ] >;
psl := sl @ factor;
AssertAttribute(psl, "Order", #PSL(2, q));

if Print gt 1 then "Making outer involution in PGL"; end if;

z:= PrimitiveElement(GF(q));
conj_invol:= (gl![z, 0, 0, 1])@factor;

field_auto:= apsl.3;

dgroup := DerivedGroup(group);

if Print gt 1 then print "Setting up homomorphisms"; end if;
homom, F, phi :=
    MakeHomom(dgroup, group, p, psl, apsl, conj_invol, field_auto:Print:=Print);
dh := Domain(homom);
apsl := sub<apsl | homom(dh.1), homom(dh.2), conj_invol, field_auto >;
AssertAttribute(apsl, "Order", #psl * 6);

maximals:=[];

if not max then
  return homom, apsl, maximals, F, phi;
end if;

if Print gt 1 then "Making reducible"; end if;
Append(~maximals, Stabiliser(psl, 1));

if Print gt 1 then "Making imprimitive"; end if;
Append(~maximals, Stabiliser(psl, {1, 2}));

if Print gt 1 then "Making semilinear"; end if;
Append(~maximals, GetL2p3Semilin(psl, p));

if Print gt 1 then "Getting subfield"; end if;
Append(~maximals, (GetSubfield(sl, p)@factor));
if Print gt 1 then print "Found maximals in standard copy"; end if;

  return homom, apsl, maximals, F, phi;
end function;
