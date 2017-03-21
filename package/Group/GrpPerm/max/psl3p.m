freeze;

import "gl2.m": PGL2, PGammaL2;
import "psl2p.m": DihedralTrick, FindInvolution, FindGoodGens;

/*
Constructively recognise and find maximal subgroups  of L(3,p).?
Recognition by Derek Holt.
Maximals by Colva Roney-Dougal.
*/


/*This function returns the maximal C_9 group 3.Alt(6), which occurs whenever 
 *5 is a square in the field GF(p^e), and GF(p^e) contains a cube root
 *of unity. tested on primes p in range [1..10000].
 */

function GetAlt6(q)
assert #Factorisation(q) eq 1;
assert IsSquare(GF(q)!5);

r5:= SquareRoot(GF(q)!5);
b5:= GF(q)!((-1 + r5)/2);
omega:= RootOfUnity(3, GF(q));
h:= omega - b5;
hbar:= omega^2 - b5;  /*b5 real, omegabar = omega^2*/
half := GF(q)!(2^-1);


assert omega in GF(q);

group:= sub<GL(3, q) |
[-1,   0,   0,
  0,  -1,   0,
  0,   0,   1],
[ 0,   1,   0, 
  0,   0,   1, 
  1,   0,   0],
[-1,  0, 0,
  0, 0, -1,
  0, -1, 0],
[half, -half, -h*half,
 -half, half, -h*half,
 hbar*half, hbar*half, 0]
>;

return group;

end function;

function GetExtraspec(p)

z:= PrimitiveElement(GF(p));
omega:= z^Integers()!((p-1)/3);
if p mod 9 eq 1 then
     ninth:= z^Integers()!((p-1)/9);
end if;
a:= GL(3, p)!DiagonalMatrix([1, omega, omega^2]);
b:= GL(3, p)!
[0, 1, 0,
 0, 0, 1, 
 1, 0, 0];
if p mod 9 eq 1 then
   c:= GL(3, p)!DiagonalMatrix([ninth^2, ninth^5, ninth^2]);
else
   c:= GL(3, p)!DiagonalMatrix([1, omega, 1]);
end if;
d:= GL(3, p)!
[1,   1,        1,
 1, omega, omega^2,
 1, omega^2, omega];
grp:= sub<GL(3, p)|a, b, c, d>;
newgrp:= grp meet SL(3, p);
return newgrp;
end function;

//tested on prime p in the range 1..1000.

function GetImprims(p)
z:= PrimitiveElement(GF(p));
m1:= SL(3, p)!DiagonalMatrix([z, 1, z^-1]);
m2:= SL(3, p)![0, 1, 0, 0, 0, 1, 1, 0, 0];
m3:= SL(3, p)![-1, 0, 0, 0, 0, -1, 0, -1, 0]; 
grp:= sub<SL(3, p)|m1, m2, m3>;
//assert #grp eq (p-1)^2*6;
return grp;
end function;

/*This function produces the C_9 group PSL(2, 7), which occurs
 *whenever Root(-7) lies in the field. The matrices come from the
 *Atlas "Reflection" construction. Tested on primes p in range 7..10000.
 */

function GetPSL2_7(q)
assert q gt 3 and not q eq 7;
assert #Factorisation(q) eq 1;

z:= GF(q)!(-7);

assert IsSquare(z);
sqrt:= SquareRoot(z);
half:= GF(q)!(2^-1);
quarter:= GF(q)!(4^-1);

group:= sub<SL(3, q) | 
SL(3, q)!DiagonalMatrix([1, -1, -1]), 

SL(3, q)![-1,  0,  0,
           0,  0, -1,
           0, -1,  0],
SL(3, q)![ 0, -1,  0,
          -1,  0,  0,
           0,  0, -1],
SL(3, q)![  -half,       half,       (-1 + sqrt)*quarter,
             half,      -half,       (-1 + sqrt)*quarter,
          (-1 -sqrt)*quarter, (-1 -sqrt)*quarter,     0]>;

assert #group eq 168;

return group;
end function;

function GetSLTorus(p, sl)
z:= PrimitiveElement(GF(p));
a:= sl!DiagonalMatrix([z, 1, z^-1]);
b:= sl!DiagonalMatrix([z, z^-1, 1]);
return sub<sl|a, b>;
end function;

/* 
 * Point_meet_line is all matrices of shape
 *          [*, *, *
 *           0, *, *,
 *           0, 0, *];
 * where the point is <(0, 0, 1)> and the line is {(0, a, b)}.
 * Tested for having correct order on all primes in range [1..100].
 */

function GetPointMeetLine(p, sl)
torus:= GetSLTorus(p, sl);
a:= sl![1, 1, 0,
        0, 1, 0, 
        0, 0, 1];
b:= sl![1, 0, 1, 
        0, 1, 0,
        0, 0, 1];
c:= sl![1, 0, 0, 
        0, 1, 1, 
        0, 0, 1];
group:=  sub<sl|torus, a, b, c>;
return group;
end function;


/*
 * Point_unmeet_line is all matrices of shape
 *        [*, 0, 0,
 *         0, *, *,
 *         0, *, *];
 * where the point is <(1, 0, 0)> and the line is {(0, a, b)}.
 * We generate it by taking the generators for GL(2, p) and 
 * correcting the determinant using hte [1][1] position.
 * Tested for correct order on all primes in range [1..100].
 */

function GetPointUnmeetLine(p, sl)
gens:= SetToSequence(Generators(GL(2, p)));
newgens:= [];
for i in [1..#gens] do
     d:= Determinant(gens[i]);
     list:= Eltseq(gens[i]);
     Append(~newgens, sl![d^-1,  0,       0,
                           0, list[1], list[2],
                           0, list[3], list[4]]);
end for;
return sub<sl|newgens>;
end function;

/*
 * The basic reducibles are just the point stabiliser and the line
 * stabiliser. point stabiliser is the stabiliser of <(1, 0, 0)>, 
 * line stabiliser is the stabiliser of <(0, a, b)>. Tested for being
 * correct order on all primes in the range [1..100].
 */

function GetLineStab(p, sl)
group:= sub<sl|GetPointUnmeetLine(p, sl), 
[1, 1, 0, 
 0, 1, 0,
 0, 0, 1],
[1, 0, 1, 
 0, 1, 0, 
 0, 0, 1]>;                  
return group;
end function;

function GetPointStab(p, sl)
group:= sub<sl|GetPointUnmeetLine(p, sl),
[1, 0, 0, 
 1, 1, 0,
 0, 0, 1],
[1, 0, 0, 
 0, 1, 0, 
 1, 0, 1]>;
return group;
end function;


function GetSemilin(p, sl, gl)

//"making Singer Cycle";
pol := DefiningPolynomial(GF(p^3));
x := Parent(pol).1;
coeffs:= Coefficients(pol);
mat:= gl![0, 1, 0, 0, 0, 1, -coeffs[1], -coeffs[2], -coeffs[3]];

//"putting cycle into sl";
det:= Determinant(mat);
o:= Order(det);
newelt:= sl!Eltseq(mat^o);

//find field automorphism - the reason that x^3 has been added to the
//argument below is to ensured that cxp[2] and cxp2[2] are always defined!
cxp := Coefficients(x^3 + x^p mod pol);
cxp2 := Coefficients(x^3 + (x^2)^p mod pol);
field_auto := sl![1,0,0,cxp[1],cxp[2],cxp[3],cxp2[1],cxp2[2],cxp2[3]];

grp:= sub<sl|newelt, field_auto>;
return grp;

end function;

/*****************************************************
* The following function is used in the noncoprime   *
* case - we start by making 3 copies of a group,     *
* which are conjugate under the outer 3-cycle.       *
* a unique one of these will commute with our        *
* given involution, so in the case psl.2 we require  *
* this to be appended to the list of maximals        *
*****************************************************/

function SelectGroup(psl, initial, three_cyc, invol)
looking := true;
for i in [0..2] do
    group := initial^(three_cyc^i);
    if IsConjugate(psl, group, group^invol) then
        looking := false;
        break;
    end if;
end for;
if looking then "Error normalising subgroup in PSL.2"; end if;
return group;
end function;
    
/* MakeHomom functions - DFH
 * For generators of PSL(3,p), we choose an involution and a non-central
 * p-element. These are in unique p-classes.
 */

FindCentralPElement := function(G,p)
proc := RandomProcess(G);
foundelt:= false;
while not foundelt do
      x:= Random(proc);
      o := Order(x);
      if o gt p and o mod p eq 0 then
        x := x^(o div p);
        foundelt:= true;
      end if;
end while;
return x;
end function;

FindGeneratingPElement := function(G,g,x,p)
/* g should be element returned by FindInvolution(G), and
 * x as returned by FindCentralPElement(G,p).
 * Find a p-element y such that <g,y> = G.
 */
  local proc;

  GenG := function(g,y)
    local procb, z;
    //To test whether G=<g,y>, we do a quick probabilistic test using orders
    procb := RandomProcess(sub<G|g,y>);
    for i in [1..50] do
      z := Random(procb);
      if (p^2 * (p^2-1) * (p^2-p)) mod Order(z) ne 0 then
        return true;
      end if;
    end for;
    return false;
  end function;

  proc := RandomProcess(G);
  y:=(x,Random(proc));
  while (Order(y) ne p) or (not GenG(g,y)) do
     y:=(x^Random(proc),Random(proc));
  end while;
  return y;
end function;


/* In the following function, psl, apsl are standard copies of PSL(3,p) and
 * Aut(PSL(3,p)).
 * group is our unknown almost simple group with socle dgroup isomorphic
 * to PSL(3,p).
 * we start by defining isomorphism dgroup -> psl and then extend to
 * monomorphism group -> apsl.
 */
MakeHomom := function(dgroup, group, p, psl, apsl : Print:=0)
  // for generators, we choose an involution (unique class) and another
  // random generating element.

  local procg, procdg, procp, procap;
  if p eq 8 then
     a1,b1 := FindGoodGens(psl, 21);
     psls:= sub< psl |  a1, b1 >;
     AssertAttribute(psls,"Order",#psl);
     F,phi := FPGroupStrong(psls);
     a,b   := FindGoodGens(dgroup, 21);
  else
    a1 := FindInvolution(psl);
    x := FindCentralPElement(psl,p);
    b1 := FindGeneratingPElement(psl,a1,x,p);
    // try getting b1 to fix 1 - may help FPGroupStrong!
    for x in Fix(b1) do
     isc, g := IsConjugate(psl,x,1);
     if isc then a1:=a1^g; b1:=b1^g; break; end if;
    end for;
    if Print gt 1 then print "Got psl gens"; end if;
  
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
    if Print gt 1  then print "Got word group"; end if;
  
    // now look for required element in group
    a := FindInvolution(dgroup);
    x := FindCentralPElement(dgroup,p);
    b := FindGeneratingPElement(dgroup,a,x,p);
    if Print gt 1  then print "Got group gens"; end if;
  
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
  end if;
  if Print gt 1 then "Identified psl"; end if;

  dgs := sub<dgroup|a,b>;
  AssertAttribute(dgs,"Order",#psl);

  homom := hom < dgs -> apsl | [a1,b1] >;

  if dgroup eq group then
    return homom, F, phi;
  end if;

  procg:= RandomProcess(group);
  procap := RandomProcess(apsl);
  procp := RandomProcess(psl);

  if Index(group,dgroup) mod 3 eq 0 then
      // first deal with 3-element in outer automorphism group
      c := Random(procg);
      while c^2 in dgroup  or not c^3 in dgroup do
        c := Random(procg);
      end while;
      ac := (a^c) @ homom;  bc := (b^c) @ homom;
      
      c1 := Random(procap);
      while c1^2 in psl  or not c1^3 in psl do
        c1 := Random(procap);
      end while;
      g := DihedralTrick(a1^c1, ac, procp);
      c1 := c1*g;
      isc, g := IsConjugate(Centraliser(psl,ac),b1^c1,bc);
      if not isc then //c1^2 should do the trick
        c1 := c1^2;
        g := DihedralTrick(a1^c1, ac, procp);
        c1 := c1*g;
        isc, g := IsConjugate(Centraliser(psl,ac),b1^c1,bc);
      end if;
      c1 := c1*g;
      if Print gt 1  then print "Identified psl.3"; end if;
      dgs := sub<group|a,b,c>;
      AssertAttribute(dgs,"Order",#psl*3);
      if Index(group,dgroup) eq 3 then
          return hom < dgs -> apsl | [a1,b1,c1] >, F, phi;
      end if;

      //  now with 2-element in outer automorphism group
      d := Random(procg);
      while d^3 in dgroup or not d^2 in dgroup do d := Random(procg);
      end while;
      ad := (a^d) @ homom;  bd := (b^d) @ homom;
      
      d1 := Random(procap);
      while d1^3 in psl or not d1^2 in psl do d1 := Random(procap);
      end while;
      g := DihedralTrick(a1^d1, ad, procp);
      d1 := d1*g;
      isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
      if not isc then // need to try d1^c1 and d1^(c1^2)
        d1 := d1^c1;
        g := DihedralTrick(a1^d1, ad, procp);
        d1 := d1*g;
        isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
        if not isc then // need to try d1^c1 and d1^(c1^2)
          d1 := d1^c1;
          g := DihedralTrick(a1^d1, ad, procp);
          d1 := d1*g;
          isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
        end if;
      end if;
      d1 := d1*g;
      if Print gt 1  then print "Identified psl.6"; end if;
      dgs := sub<group|a,b,c,d>;
      AssertAttribute(dgs,"Order",#psl*6);
      return hom < dgs -> apsl | [a1,b1,c1,d1] >, F, phi;
  end if;

  //Finally the psl.2 case
  d := Random(procg);
  while d^3 in dgroup do d := Random(procg); end while;
  ad := (a^d) @ homom;  bd := (b^d) @ homom;
  dgs := sub<group|a,b,d>;
  AssertAttribute(dgs,"Order",#psl*2);

  d1 := Random(procap);
  while d1^3 in psl or not d1^2 in psl do d1 := Random(procap); end while;
  g := DihedralTrick(a1^d1, ad, procp);
  d1 := d1*g;
  isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  if isc then
     d1 := d1*g;
     return hom < dgs -> apsl | [a1,b1,d1] >, F, phi;
  end if;

  //The awkward case when we have the wrong isomorphism onto psl
  //Find outer 3-element in apsl.
  c1 := Random(procap);
  while c1^2 in psl do c1 := Random(procap); end while;

  a1 := a1^c1; b1 := b1^c1;
  homom := hom < sub<group|a,b> -> apsl | [a1,b1] >;
  ad := (a^d) @ homom;  bd := (b^d) @ homom;
  g := DihedralTrick(a1^d1, ad, procp);
  d1 := d1*g;
  isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  if isc then
     d1 := d1*g;
     psi := hom< psls -> sub< apsl | a1,b1 > | [a1,b1] >;
     return hom < dgs -> apsl | [a1,b1,d1] >, F, phi*psi;
  end if;

  //Try again - must work this time!
  a1 := a1^c1; b1 := b1^c1;
  homom := hom < sub<group|a,b> -> apsl | [a1,b1] >;
  ad := (a^d) @ homom;  bd := (b^d) @ homom;
  g := DihedralTrick(a1^d1, ad, procp);
  d1 := d1*g;
  isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  if isc then
     d1 := d1*g;
     psi := hom< psls -> sub< apsl | a1,b1 > | [a1,b1] >;
     return hom < dgs -> apsl | [a1,b1,d1] >, F, phi*psi;
  end if;
  error "Failed to find map onto PSL.2";

end function;

 
/*****************************************************
* First we do the case where 3 does not divide       *
* p-1, as this has much simpler behavour - Out = 2   *
* which is handy for a start.....                    *
******************************************************/

function CoprimeMaximals(group, p: max:= true, Print:=0)

if Print gt 1 then print "Making standard group"; end if;
  gl := GL(3,p);
  sl := SL(3,p);
  apsl := PGL2(3,p);
  factor := hom< gl->apsl | [ apsl.1, apsl.2] >;
  psl := sl @ factor;

o:= Order(group);
IsPSL := o eq #psl;
dgroup:= DerivedSubgroup(group);

/*
 * Note that since 3 does not divide (p-1) we have pgl = psl. We may
 * still have an outer element of order 2, but since the two copies of
 * the reducible groups are computed directly, as are the novelty
 * intersections, we don't need it ever. 
 */

if Print gt 1 then print "Setting up homomorphisms"; end if;
homom, F, phi := MakeHomom(dgroup, group, p, psl, apsl : Print:=Print);
dh := Domain(homom);
assert not apsl.3 in psl;
apsl := sub<apsl | homom(dh.1), homom(dh.2), apsl.3 >;
AssertAttribute(apsl, "Order", #psl * 2);

maximals:= [];
if not max then
  return homom, apsl, maximals, F, phi;
end if;

/*
 * Reducible - if we have psl then we get 2 classes, conjugate under
 * inverse transpose. Otherwise, we get two novelties, intersections 
 * are point with line containing it and point with line not
 * containing it. In both cases the two groups are returned as matrix
 * groups, so we factor by the centre before applying homom.
 */

if Print gt 1 then print "Getting reducibles"; end if;
if IsPSL then
   Append(~maximals,  GetPointStab(p, sl)@factor);
   Append(~maximals,  GetLineStab(p, sl)@factor);
else 
   Append(~maximals, GetPointMeetLine(p, sl)@factor);
   Append(~maximals, GetPointUnmeetLine(p, sl)@factor);
end if;

/* 
 * The maximal imprimitive is unique, and extends. The function 
 * returns a matrix group, so we factor by the centre before applying 
 * homom. 
 */

if Print gt 1 then print "Getting imprimitives"; end if;
Append(~maximals, GetImprims(p)@factor);

/*
 * The maximal semilinear is unique, and extends. It is returned as a 
 * permutation group.
 */

if Print gt 1 then print "Getting semilinears"; end if;
Append(~maximals, GetSemilin(p, sl, gl)@factor);


/*
 * There is a classical subgroup PSO(3, p) - we take SO(3, p) and
 * apply factor to it. It appears to always extend. 
 */

if Print gt 1 then print "Getting classicals"; end if;
Append(~maximals, SO(3, p)@factor);

/*
 * Finally, there is PSL(2, 7), which is a maximal C_9 group whenever 
 * -7 is a square in GF(p). For reasons that are not entirely clear to
 * me at present, it appears to extend. Is returned as a matrix
 * subgroup so apply factor to it. 
 */

if p gt 7 and IsSquare(GF(p)!(-7)) then
    if Print gt 1 then print "Getting PSL(2, 7)"; end if;
    Append(~maximals, GetPSL2_7(p)@factor);
end if;
if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, apsl, maximals, F, phi;
end function;



/****************************************************
* Now we do the case where 3 does divide p-1. This  *
* means that we get additional conjugacy classes    *
* of some groups, we get extraspecial groups, and   *
* we get alt_6 as a C_9 group whenever 5 is a       *
* square in GF(p)                                   *
*****************************************************/

function NonCoprimeMaximals(group, p: max:= true, Print:=0)
/*
 * first we make our standard copies of pgl, psl etc. we need 
 * pgl to give us the element of order 3 which will later provide us
 * with multiple copies of O_3(p) and alt_6.
 */
if Print gt 1 then print "Making standard group"; end if;
  gl := GL(3,p);
  sl := SL(3,p);
  apsl := PGL2(3,p);
  factor := hom< gl->apsl | [ apsl.1, apsl.2] >;
  psl := sl @ factor;


dgroup:= DerivedSubgroup(group);

o:= Order(group);
orderpsl:= #PSL(3, p);
if o eq orderpsl then
    type:= "psl";
elif o eq 2*orderpsl then
    type:= "psl.2";
elif o eq 3*orderpsl then
    type:= "psl.3";
else
    assert o eq 6*orderpsl;
    type:= "psl.sym3";
    dgroup:= DerivedSubgroup(dgroup);
end if;
//Note - dgroup is actually the socle, not always the derived group!

/*
 * Now we must make the element of order 3 which will be used to get
 * multiple copies of some groups.
 */

z:= PrimitiveElement(GF(p));
three_cyc:= (gl!DiagonalMatrix([z, 1, 1]))@factor;

if Print gt 1 then print "Setting up homomorphisms"; end if;
homom, F, phi := MakeHomom(dgroup, group, p, psl, apsl : Print:=Print);
dh := Domain(homom);
assert not apsl.3 in psl;
if type eq "psl.2" then invol := homom(dh.3);
    //necessary to get normalisers of subgroups correct.
else invol := apsl.3;
end if;
apsl := sub<apsl | homom(dh.1), homom(dh.2), three_cyc, invol >;
AssertAttribute(apsl, "Order", #psl * 6);

maximals:= [];
if not max then
  return homom, apsl, maximals, F, phi;
end if;

/* 
 * first we must return the reducibles. in cases psl and psl.3 we have
 * two classes - the point and line stabiliser. these are returned as
 * matrix groups and so we must apply factor to them before applying 
 * homom. in cases psl.2 and psl.sym_3 the classes fuse, but there are
 * novelty subgroups coming from the normalisers of the stabiliser of
 * point and a line containing it, and the stabiliser of a point and a
 * line not containing it.
 */

if Print gt 1 then print "Getting reducibles"; end if;
if type eq "psl" or type eq "psl.3" then
   Append(~maximals,  GetPointStab(p, sl)@factor);
   Append(~maximals,  GetLineStab(p, sl)@factor);
else
   Append(~maximals, GetPointMeetLine(p, sl)@factor);
   Append(~maximals, GetPointUnmeetLine(p, sl)@factor);
end if;


/* 
 * Next we get the imprimitive. This is unique, and extends in all
 * cases. 
 */

if Print gt 1 then print "Getting imprimitives"; end if;
Append(~maximals, GetImprims(p)@factor);

/* 
 * Next we get the semilinear group. This is unique, and extends in
 * all cases. 
 */ 

if Print gt 1 then print "Getting semilinear"; end if;
Append(~maximals, GetSemilin(p, sl, gl)@factor);

/* 
 * Next we get the extraspecial group.
 */ 

if Print gt 1 then print "Getting extraspecials"; end if;
if p mod 9 eq 1 then
  // three classes in pgl
  if type eq "psl" then
    initial:= GetExtraspec(p)@factor;
    Append(~maximals, initial);
    Append(~maximals, initial^three_cyc);
    Append(~maximals, initial^(three_cyc^2));
  elif type eq "psl.2" then
    initial:= GetExtraspec(p)@factor;
    Append(~maximals, SelectGroup(psl, initial, three_cyc, invol));
  end if;
else
  Append(~maximals, GetExtraspec(p)@factor);
end if;

/*
 * Next we do the classical group. What seems to happen here is
 * that in PSL there are 3 classes, in PSL.2 two of them fuse, and one
 * remains which commutes with the outer involution, and in PSL.3 and
 * PSL.sym_3 all three of them fuse. 
 */

if Print gt 1 then print "Getting classicals"; end if;
if type eq "psl" then
    initial:= SO(3, p)@factor;
    Append(~maximals, initial);
    Append(~maximals, initial^three_cyc);
    Append(~maximals, initial^(three_cyc^2));
elif type eq "psl.2" then
    initial:= SO(3, p)@factor;
    Append(~maximals, SelectGroup(psl, initial, three_cyc, invol));
end if;

/* 
 * Now we have only the C_9s left to do. Start with Alt(6). Same
 * fusion/splitting pattern as for O(3, p).
 */

if IsSquare(GF(p)!5) then
    if Print gt 1 then print "Getting alt6"; end if;
    if type eq "psl" then
        initial:= GetAlt6(p)@factor;
        Append(~maximals, initial);
        Append(~maximals, initial^three_cyc);
        Append(~maximals, initial^(three_cyc^2));
    elif type eq "psl.2" then
        initial:= GetAlt6(p)@factor;
        Append(~maximals, SelectGroup(psl, initial, three_cyc, invol));
    end if;
end if;
 
/*
 * And finally we do PSL(2, 7). Again, same fusion/splitting pattern
 * as for O(3, p). 
 */

if p gt 3 and not p eq 7 and IsSquare(GF(p)!(-7)) then
    if Print gt 1 then print "Getting PSL(2, 7)"; end if;
    if type eq "psl" then
        initial:= GetPSL2_7(p)@factor;
        Append(~maximals, initial);
        Append(~maximals, initial^three_cyc);
        Append(~maximals, initial^(three_cyc^2));
    elif type eq "psl.2" then
        initial:= GetPSL2_7(p)@factor;
        Append(~maximals, SelectGroup(psl, initial, three_cyc, invol));
    end if;
end if;
if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, apsl, maximals, F, phi;
  
end function;

function WhichGroupl38(group)
o:= Order(group);
order_psl:= 16482816;
if o eq order_psl then type:= "psl"; 
elif o eq 2*order_psl then type:= "psl.2";
elif o eq 3*order_psl then type:= "psigmal";
elif o eq 6*order_psl then type:= "psl.6";
end if;

return type;
end function;


function L3_8Maximals(group: max:= true, Print:=0)

/*
 * setting up groups. psl = pgl = sl. psigmal = pgammal = g.3.
 */

if Print gt 1 then print "Making standard group"; end if;
gl := GL(3,8);
sl := SL(3,8); 
apsl := PGammaL2(3,8);
factor := hom< gl->apsl | apsl.1, apsl.2 >;
psl := sl @ factor;

// note apsl.3 is field auto, apsl.4 is graph auto.

dgroup:= DerivedSubgroup(group);

/* setting up field.
 */

if Print gt 1 then print "Setting up homomorphism"; end if;
homom, F, phi := MakeHomom(dgroup, group, 8, psl, apsl : Print:=Print);
dh := Domain(homom);
apsl := sub<apsl | homom(dh.1), homom(dh.2), apsl.3, apsl.4 >;
AssertAttribute(apsl, "Order", #psl * 6);

maximals:= [];
if not max then
  return homom, apsl, maximals, F, phi;
end if;

z:= PrimitiveElement(GF(8));

/* type is one of "psl", "psl.2", "psigmal" or "psl.6".
 */
type:= WhichGroupl38(group);


/*
 * point_unmeet_line is all matrices of shape [* 0 0 
 *                                             0 * *
 *                                             0 * *];
 * point_meet_line is all matrices of shape    [* * *
 *                                             0 * *
 *                                             0 0 *];
 * If the outer aut. part of the group has even order, 
 * then we have point-line duality and hence there are novelty 
 * subgroups. otherwise we have the point stabiliser and the line
 * stabiliser.  
 */                             

if Print gt 1 then print "Getting reducibles"; end if;
point_unmeet_line:= sub<sl|[z^-1, 0, 0, 0, z, 0, 0, 0, 1],
                               [1, 0, 0, 0, 1, 1, 0, 1, 0]>;
point_meet_line:= sub<sl|DiagonalMatrix([z^-1, 1, z]), 
                                 DiagonalMatrix([z^-1, z, 1]),
                                 [1, 1, 0, 0, 1, 0, 0, 0, 1],
                                 [1, 0, 1, 0, 1, 0, 0, 0, 1],
                                 [1, 0, 0, 0, 1, 1, 0, 0, 1]>;

if type eq "psl.2" or type eq "psl.6" then
     Append(~maximals, point_meet_line@factor);
     Append(~maximals, point_unmeet_line@factor);
else
     point:= sub<sl|point_unmeet_line, [1, 0, 0, 1, 1, 0, 0, 0, 1],
                    [1, 0, 0, 0, 1, 0, 1, 0, 1]>;
     Append(~maximals, point@factor);
     line:= sub<sl|point_unmeet_line, [1, 1, 0, 0, 1, 0, 0, 0, 1],
                   [1, 0, 1, 0, 1, 0, 0, 0, 1]>;
     Append(~maximals, line@factor);
end if;

if Print gt 1 then print "Getting imprimitive"; end if;
imprim:= sub<sl|DiagonalMatrix([z^-1, 1, z]), DiagonalMatrix([z^-1, z, 1]), 
                [0, 1, 0, 0, 0, 1, 1, 0, 0], [1, 0, 0, 0, 0, 1, 0, 1,
		0]>;
Append(~maximals, imprim@factor);

if Print gt 1 then print "Getting semilinear"; end if;
semilin:= sub<sl|[0, 1, 0, 0, 0, 1, -1, -z, 0], 
                 [1, 0, 0, 0, z^2, z, 0, z^2, z^6]>;
Append(~maximals, semilin@factor);

if Print gt 1 then print "Getting subfield"; end if;
psl3_2:= sub<sl|[1, 1, 0, 0, 1, 0, 0, 0, 1],
                [0, 0, 1, 1, 0, 0, 0, 1, 0]>;
Append(~maximals, (psl3_2)@factor);
if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, apsl, maximals, F, phi;
end function;

function WhichGroupl39(group:Print:=0)
o:= Order(group);
order_psl:= 42456960;
if o eq order_psl then type:= "psl"; 
elif o eq 4*order_psl then type:= "psl.4";
else assert o eq 2*order_psl;
  proc := RandomProcess(group);
  dgroup := DerivedGroup(group);
  while true do
    g := Random(proc);
    o := Order(g);
    if o eq 14 then type := "psl.fg"; break; end if;
    if o eq 26 then type := "psl.f"; break; end if;
    if o eq 20 and not g in dgroup then type := "psl.g"; break; end if;
  end while;
end if;

return type;
end function;

MakeHomoml39 :=
      function(dgroup, group, p, psl, apsl, type, field_auto, graph_auto:
                Print:=0)
  // for generators, we choose an involution (unique class) and another
  // random generating element.

  local procg, procdg, procp;
  procp := RandomProcess(psl);
  a1 := FindInvolution(psl);
  b1 := Random(procp);
  while Order(b1) ne 3 or Order(a1*b1) ne 24 do b1:=Random(procp); end while;
  psls:= sub< psl |  a1, b1 >;
  AssertAttribute(psls,"Order",#psl);
  F,phi := FPGroupStrong(psls);

  procdg := RandomProcess(dgroup);
  a := FindInvolution(dgroup);
  b := Random(procdg);
  while Order(b) ne 3 or Order(a*b) ne 24 do b:=Random(procdg); end while;
  if Print gt 1 then print "Got psl gens"; end if;

  dgs := sub<dgroup|a,b>;
  AssertAttribute(dgs,"Order",#psl);

  homom := hom < dgs -> apsl | [a1,b1] >;

  if type eq "psl" then
    return homom, F, phi;
  end if;

  procg:= RandomProcess(group);
  if type eq "psl.f" or type eq "psl.4" then
      // get 2-element in outer automorphism group
      c := Random(procg);
      while c in dgroup do c := Random(procg); end while;
      seeking := type eq "psl.4";
      while seeking do
        s := sub<group|dgroup,c>;
        AssertAttribute(s, "Order", 2 * #psl);
        if WhichGroupl39(s) eq "psl.f" then
          seeking := false;
        else
          c := Random(procg);
          while c in dgroup do c := Random(procg); end while;
        end if;
      end while;
      ac := (a^c) @ homom;  bc := (b^c) @ homom;

      c1 := field_auto;
      g := DihedralTrick(a1^c1, ac, procp);
      c1 := c1*g;
      isc, g := IsConjugate(Centraliser(psl,ac),b1^c1,bc);
      if not isc then error "psl.f error"; end if;
      c1 := c1*g;
      if Print gt 1 then print "Identified psl.f"; end if;
      if type eq "psl.f" then
          dgs := sub<group|a,b,c>;
          AssertAttribute(dgs,"Order",#psl*2);
          return hom < dgs -> apsl | [a1,b1,c1] >, F, phi;
      end if;
  end if;

  if type eq "psl.g" or type eq "psl.4" then
      // get 2-element in outer automorphism group
      d := Random(procg);
      while d in dgroup do d := Random(procg); end while;
      seeking := type eq "psl.4";
      while seeking do
        s := sub<group|dgroup,d>;
        AssertAttribute(s, "Order", 2 * #psl);
        if WhichGroupl39(s) eq "psl.g" then
          seeking := false;
        else
          d := Random(procg);
          while d in dgroup do d := Random(procg); end while;
        end if;
      end while;
      ad := (a^d) @ homom;  bd := (b^d) @ homom;

      d1 := graph_auto;
      g := DihedralTrick(a1^d1, ad, procp);
      d1 := d1*g;
      isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
      if not isc then error "psl.g error"; end if;
      d1 := d1*g;
      if Print gt 1 then print "Identified psl.g"; end if;
      if type eq "psl.g" then
        dgs := sub<group|a,b,d>;
        AssertAttribute(dgs,"Order",#psl*2);
        return hom < dgs -> apsl | [a1,b1,d1] >, F, phi;
      else
        dgs := sub<group|a,b,c,d>;
        AssertAttribute(dgs,"Order",#psl*4);
        return hom < dgs -> apsl | [a1,b1,c1,d1] >, F, phi;
      end if;
  end if;

  //remaining case is psl.fg
  d := Random(procg);
  while d in dgroup do d := Random(procg); end while;
  ad := (a^d) @ homom;  bd := (b^d) @ homom;

  d1 := field_auto * graph_auto;
  g := DihedralTrick(a1^d1, ad, procp);
  d1 := d1*g;
  isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  if not isc then error "psl.fg error"; end if;
  d1 := d1*g;
  if Print gt 1 then print "Identified psl.fg"; end if;
  dgs := sub<group|a,b,d>;
  AssertAttribute(dgs,"Order",#psl*2);
  return hom < dgs -> apsl | [a1,b1,d1] >, F, phi;

end function;


function L3_9Maximals(group: max:= true, Print:=0)

if Print gt 1 then print "Making standard group"; end if;
gl := GL(3,9);
sl := SL(3,9); 
apsl := PGammaL2(3,9);
factor := hom< gl->apsl | apsl.1, apsl.2 >;
psl := sl @ factor;

// note apsl.3 is field auto, apsl.4 is graph auto.
field_auto := apsl.3;
graph_auto := apsl.4;

dgroup:= DerivedSubgroup(group);

/* setting up field.
 */

type:= WhichGroupl39(group);
if Print gt 1 then print "Setting up homomorphism"; end if;
homom, F, phi :=
    MakeHomoml39(dgroup, group, 9, psl, apsl, type, field_auto, graph_auto:
                  Print:=Print);
dh := Domain(homom);
apsl := sub<apsl | homom(dh.1), homom(dh.2), apsl.3, apsl.4 >;
AssertAttribute(apsl, "Order", #psl * 4);

maximals:= [];
if not max then
  return homom, apsl, maximals, F, phi;
end if;

z:= PrimitiveElement(GF(9));


/*
 * point_unmeet_line is all matrices of shape [* 0 0 
 *                                             0 * *
 *                                             0 * *];
 * point_meet_line is all matrices of shape    [* * *
 *                                             0 * *
 *                                             0 0 *];
 * If the group is psl.g, psl.fg or psl.4,
 * then we have point-line duality and hence there are novelty 
 * subgroups. otherwise we have the point stabiliser and the line
 * stabiliser.  
 */                             

if Print gt 1 then print "Getting reducibles"; end if;
point_unmeet_line:= sub<sl|[z^-1, 0, 0, 0, z, 0, 0, 0, 1],
                               [1, 0, 0, 0, 1, 1, 0, -1, 0]>;
point_meet_line:= sub<sl|DiagonalMatrix([z^-1, 1, z]), 
                                 DiagonalMatrix([z^-1, z, 1]),
                                 [1, 1, 0, 0, 1, 0, 0, 0, 1],
                                 [1, 0, 1, 0, 1, 0, 0, 0, 1],
                                 [1, 0, 0, 0, 1, 1, 0, 0, 1]>;

if type eq "psl.g" or type eq "psl.fg" or type eq "psl.4" then
     Append(~maximals, point_meet_line@factor);
     Append(~maximals, point_unmeet_line@factor);
else
     point:= sub<sl|point_unmeet_line, [1, 0, 0, 1, 1, 0, 0, 0, 1],
                    [1, 0, 0, 0, 1, 0, 1, 0, 1]>;
     Append(~maximals, point@factor);
     line:= sub<sl|point_unmeet_line, [1, 1, 0, 0, 1, 0, 0, 0, 1],
                   [1, 0, 1, 0, 1, 0, 0, 0, 1]>;
     Append(~maximals, line@factor);
end if;

if Print gt 1 then print "Getting imprimitive"; end if;
imprim:= sub<sl|DiagonalMatrix([z^-1, 1, z]), DiagonalMatrix([z^-1, z, 1]), 
                [0, 1, 0, 0, 0, 1, 1, 0, 0], [-1, 0, 0, 0, 0, 1, 0, 1,
		0]>;
Append(~maximals, imprim@factor);

if Print gt 1 then print "Getting semilinear"; end if;
semilin:= sub<sl|[0, 1, 0, 0, 0, 1, 1, 0, 0], 
                 [z^7, z^7, z^2, z^7, 1, z, z^2, z, z^6]>;
Append(~maximals, semilin@factor);

if Print gt 1 then print "Getting subfield"; end if;
psl3_3:= sub<sl|[1, 1, 0, 0, 1, 0, 0, 0, 1],
                [0, 0, 1, 1, 0, 0, 0, 1, 0]>;
Append(~maximals, (psl3_3)@factor);

if Print gt 1 then print "Getting unitary"; end if;
psu3_3:= sub<sl|[z, 0, 0, 0, z^2, 0, 0, 0, z^5],
                [z^5, 2, 1, 2, 2, 0, 1, 0, 0]>;
Append(~maximals, (psu3_3)@factor);

if Print gt 1 then print "Getting orthogonal"; end if;
Append(~maximals, SO(3, 9)@factor);
if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, apsl, maximals, F, phi;
end function;

/*****************************************************
* This function ties all the rest together sadly     *
* The results have been compared with the ATLAS      *
* for p leq 11, and are correct for PSL and PGL.     *
* Have not been able to check psl.2 and psl.Sym3 as  *
* at present there is no usable homomorphism between *
* the socle of these groups and the standard copy of *
* psl                                                *
******************************************************/

function L3pIdentify(group, p : max := true, Print := 0)
assert p gt 4;
if p eq 8 then
    return  L3_8Maximals(group: max:=max, Print:=Print);
elif p eq 9 then
    return  L3_9Maximals(group: max:=max, Print:=Print);
elif ((p-1) mod 3) eq 0 then
    return NonCoprimeMaximals(group, p: max:=max, Print:=Print);
else
    return CoprimeMaximals(group, p: max:=max, Print:=Print);
end if;

end function;
