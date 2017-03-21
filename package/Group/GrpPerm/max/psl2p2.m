freeze;

import "psl2p.m": DihedralTrick, FindInvolution;
import "gl2.m": PGammaLD2;

/*
Constructively recognise and find maximal subgroups  of L(2,p^2).?
Recognition by Derek Holt.
Maximals by Colva Roney-Dougal
*/

/********************************************************
* This makes group D_(q+1) = D_(p^2+1) = PGamL(1, p^4)  *
* meet PSL(2, p^2).  Tested on all p^2 in range p       *
* = [5..500]                                            *
********************************************************/

function GetSemilin(group, q)

proc:= RandomProcess(group);

got_seed_invol:=false;
while not got_seed_invol do
    x:= Random(proc);
    o:= Order(x);
    d, r:= Quotrem(o, 2);
    if r eq 0 then
        invol:= x^d;
        assert Order(invol) eq 2;
        got_seed_invol:= true;
    end if;
end while;

made_semilin:= false;
while not made_semilin do
    y:= invol^Random(proc);
    if Order(invol*y) eq Quotrem(q+1, 2) then
        made_semilin:= true;
    end if;
end while;

return sub<group|invol, y>;
end function;

/*********************************************************
*   This function produces Alt(5), as a group generated  
*   by two mats [0, 1, -1, 0] and [a, b, c, d] where     
*   this latter matrix has trace -1 and the product       
*   has trace (1-sqrt(5)/2)                              
*                                                        
*      
* Will be maximal in PSL(2, p^2) whenever Alt(5) is      
* *not* a subgroup of PSL(2, p). Since Alt(5) is in
* PSL(2, p) whenever p^2 eq 1 mod 5, we will find it as 
* maximal subgroup of PSL(2, p^2) whenever 
* p^2 eq -1 mod 5.
*
* Tested on all p^2s congruent to -1 mod 5 in range    
* [6..10000].                                            
*              
**********************************************************/

function GetAlt5(q)

assert #Factorisation(q) eq 1 and IsSquare(q);

sigma:= GF(q)!((1 - Root(GF(q)!5, 2))/2);
 
a:= GF(q)!0;
P := PolynomialRing(GF(q)); b := P.1;
found:= false;
while not found do
    a:= a+1;
    d:= -1-a;               /*matrix order 3 has trace -1*/     
    f:= a*d - b*(b - sigma) - 1;
    roots:= Roots(f);
    if #roots gt 0 then 
        found:= true;
        b:= roots[1][1];
        c:= b - sigma;
    end if;
end while;

grp:= sub<SL(2, q) | SL(2, q)![0, 1, -1, 0], SL(2, q)![a, b, c, d]>;
if not #grp eq 120 then
    "failed to make Alt(5)";
end if;

return grp;
end function;

/*
 * The following function returns SL(2, p).2 as a subgroup 
 * of SL(2, p^2). tested on p in [4..100] (p^2 in [16..1000]).
 */


function GetSubfield(sl, p)
gens:= SetToSequence(Generators(SL(2, p)));
newgens:= [];
/*
 * This bit makes SL(2, p).
 */

for i in [1..#gens] do
     Append(~newgens, sl!Eltseq(gens[i]));
end for;

/* 
 * We now have to extend by an involution.
 */

z:= PrimitiveElement(GF(p^2));
if p mod 4 eq 1 then
    fac:= Factorisation(p^2 - 1);
    two_power:= 2^fac[1][2];
    power:= Integers()!((p^2 - 1)/two_power);
    return sub<sl|newgens, DiagonalMatrix([z^power, z^(-power)])>;
else
    i:= z^Integers()!((p^2 - 1)/4);
    return sub<sl|newgens, DiagonalMatrix([-i, i])>;
end if;
end function;

/**********************************************************
* There are a total of 5 almost simple groups with socle  *
* L_2(p^2). We denote these by "psl", "pgl", "psigmal",   *
* "psl.2"  and "pgammal". (this is ATLAS ordering L,      *
* L.2_1, L.2_2, L.2_3 and L.2^2, with the exception of    *
* L_2(9)=Alt(6) where the ATLAS swaps .2_1 and .2_2)      *
*                                                         *
* "psl" can be identified by its order                    *
* "pgammal" can be identified by its order                *
* "pgl" contains elements of order p2 \pm1 that do not    *
* lie in psl                                              *
* "psigmal" contains elements of order 2p that do not lie *
* in psl.                                                 *
* "psl.2" contains elements of order 2(p-1) and 2(p+1)    *
* that do not lie in psl. depending on the congruence of  *
* p mod 4 one or the other of these element orders        *
* distinguishes psl.2                                     *
*                                                         *
* most of the time is taken up with computing the         *
* derived subgroup, we return this as well, since it      *
* will be useful in other parts of the code.              *
*                                                         *
* tested for psl, pgl, psigmal, psl.2, pgammal in the     *
* range p in [3..1000]                                    *
**********************************************************/

function WhichGroup(group, q)

fac:= Factorisation(q);
assert #fac eq 1;
assert fac[1][2] eq 2;

/*
 * we make p the characteristic of the group (so p eq sqrt(q))
 */

p:= fac[1][1];

o:= #group;
order_psl:= #PSL(2, q);
if o eq order_psl then
    return "psl", group;
else
    //"computing derived subgroup";
    psl:= DerivedSubgroup(group);
    if  o eq order_psl*4 then
        return "pgammal", psl;
    end if;
end if;


/* we now have one of the .2s, just have to work out which. */


/* following does not work
found_initial:= false;
while not found_initial do
    x:= Random(group);
    if not x in psl then
        found_initial:= true;
    end if;
end while;

z:= q mod 4;
two_p_minus_1:= false;
two_p_plus_one:= false;
decided:= false;
while not decided do
    o:= Order(x);
    if (o eq (q + 1)) or (o eq (q - 1)) then
         return "pgl", psl;
    elif (o eq 2*p) then
         return "psigmal", psl;
    elif ((o eq 2*(p+1)) and (z eq 1)) or ((o eq 2*(p-1)) and (z eq
                                                                3)) then
         return "psl.2", psl;
    end if;
    x:= x*Random(psl);
end while;
*/

S :=Sylow(group,2);
ninv :=  #{c: c in Classes(S)|c[1] eq 2};
if ninv eq 3 then return "pgl", psl;
elif ninv eq 7 then return "psigmal", psl;
elif ninv eq 2 then return "psl.2", psl;
else error "wrong number of involution classes";
end if;

end function;

/* MakeHomom functions - DFH
 * For generators of PSL(2,p), we choose an involution and a p-element.
 */

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
      if (p^2 * (p^2-1) div 2) mod Order(z) ne 0 then
        return true;
      end if;
    end for;
    return false;
  end function;

  proc := RandomProcess(G);
  y:=(g^Random(proc),Random(proc));
  while (Order(y) ne p) or (not GenG(g,y)) do
     y:=(g^Random(proc),Random(proc));
  end while;
  return y;
end function;

/* In the following function, psl, apsl are standard copies of PSL(2,p^2) and
 * Aut(PSL(2,p^2)) = PGammaL(2,p^2).
 * group is our unknown almost simple group with socle dgroup isomorphic
 * to PSL(2,p^2).
 * We start by defining isomorphism dgroup -> psl and then extend to
 * monomorphism group -> apsl.
 */
MakeHomom := function(dgroup, group, p, psl, apsl, type, conj_invol, field_auto
                      : Print := 0)
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
  if Print gt 1 then print "Got word group"; end if;

  // now look for required element in group
  a := FindInvolution(dgroup);
  b := FindGeneratingPElement(dgroup,a,p);
  if Print gt 1 then print "Got group gens"; end if;

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
  if Print gt 1 then print "Identified psl"; end if;

  dgs := sub<dgroup|a,b>;
  AssertAttribute(dgs,"Order",#psl);

  homom := hom < dgs -> apsl | [a1,b1] >;

  if type eq "psl" then
    return homom, F, phi;
  end if;

  procg:= RandomProcess(group);
  procp := RandomProcess(psl);

  if type eq "pgl" or type eq "pgammal" then
      // get 2-element in outer automorphism group
      c := Random(procg);
      while c in dgroup do c := Random(procg); end while;
      seeking := type eq "pgammal";
      while seeking do
        s := sub<group|dgroup,c>;
        AssertAttribute(s, "Order", 2 * #psl);
        if WhichGroup(s, p^2) eq "pgl" then
          seeking := false;
        else
          c := Random(procg);
          while c in dgroup do c := Random(procg); end while;
        end if;
      end while;
      ac := (a^c) @ homom;  bc := (b^c) @ homom;

      c1 := conj_invol;
      g := DihedralTrick(a1^c1, ac, procp);
      c1 := c1*g;
      isc, g := IsConjugate(Centraliser(psl,ac),b1^c1,bc);
      if not isc then error "pgl error"; end if;
      c1 := c1*g;
      if Print gt 1 then print "Identified pgl"; end if;
      dgs := sub<group|a,b,c>;
      AssertAttribute(dgs,"Order",#psl*2);
      if type eq "pgl" then
          return hom < dgs -> apsl | [a1,b1,c1] >, F, phi;
      end if;
  end if;

  if type eq "psigmal" or type eq "pgammal" then
      // get 2-element in outer automorphism group
      d := Random(procg);
      while d in dgroup do d := Random(procg); end while;
      seeking := type eq "pgammal";
      while seeking do
        s := sub<group|dgroup,d>;
        AssertAttribute(s, "Order", 2 * #psl);
        if WhichGroup(s, p^2) eq "psigmal" then
          seeking := false;
        else
          d := Random(procg);
          while d in dgroup do d := Random(procg); end while;
        end if;
      end while;
      ad := (a^d) @ homom;  bd := (b^d) @ homom;

      d1 := field_auto;
      g := DihedralTrick(a1^d1, ad, procp);
      d1 := d1*g;
      isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
      if not isc then error "psigmal error"; end if;
      d1 := d1*g;
      if Print gt 1 then print "Identified psigmal"; end if;
      if type eq "psigmal" then
        dgs := sub<group|a,b,d>;
        AssertAttribute(dgs,"Order",#psl*2);
        return hom < dgs -> apsl | [a1,b1,d1] >, F, phi;
      else
        dgs := sub<group|a,b,c,d>;
        AssertAttribute(dgs,"Order",#psl*4);
        return hom < dgs -> apsl | [a1,b1,c1,d1] >, F, phi;
      end if;
  end if;

  //remaining case is psl.2
  d := Random(procg);
  while d in dgroup do d := Random(procg); end while;
  ad := (a^d) @ homom;  bd := (b^d) @ homom;

  d1 := conj_invol * field_auto;
  g := DihedralTrick(a1^d1, ad, procp);
  d1 := d1*g;
  isc, g := IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  if not isc then error "psl.2 error"; end if;
  d1 := d1*g;
  if Print gt 1 then print "Identified psl.2"; end if;
  dgs := sub<group|a,b,d>;
  AssertAttribute(dgs,"Order",#psl*2);
  return hom < dgs -> apsl | [a1,b1,d1] >, F, phi;

end function;

/*
 * This function is for the cases PSL(2, p^2) and PSigmaL(p^2).
 * The input group is always isomorphic to psl(2, p^2), as we find
 * this when we find the type. q = p^2.
 */

function PslOrPsigmalMaximals(group, q, type, dgroup : max:=true, Print:=0)

fac:= Factorisation(q);
assert #fac eq 1 and fac[1][2] eq 2;

p:= fac[1][1];

if Print gt 1 then "Making standard pgl"; end if;
gl:= GL(2, p^2);
apsl := PGammaLD2(p^2);
factor := hom< gl->apsl | [apsl.1, apsl.2 ] >;

sl:= SL(2, p^2);
psl:= sl@factor;
AssertAttribute(psl, "Order", #PSL(2, p^2));

if Print gt 1 then "Making outer involution in PGL"; end if;
z:= PrimitiveElement(GF(q));
conj_invol:= (gl![z, 0, 0, 1])@factor;

field_auto:= apsl.3;

if Print gt 1 then print "Setting up homomorphisms"; end if;
homom, F, phi :=
    MakeHomom(dgroup, group, p, psl, apsl, type, conj_invol, field_auto :
              Print:=Print);
dh := Domain(homom);
apsl := sub<apsl | homom(dh.1), homom(dh.2), conj_invol, field_auto >;
AssertAttribute(apsl, "Order", #psl * 4);

maximals:=[];

if not max then
  return homom, apsl, maximals, F, phi;
end if;

if Print gt 1 then "Making reducible"; end if;
Append(~maximals, Stabiliser(psl, 1));


if Print gt 1 then "Making imprimitive"; end if;
Append(~maximals, Stabiliser(psl, {1, 2}));

if Print gt 1 then "Making semilinear"; end if;
Append(~maximals, GetSemilin(psl, q));

if Print gt 1 then "Making subfield"; end if;
sub1:= GetSubfield(sl, p)@factor;
sub2:= sub1^conj_invol;
Append(~maximals, sub1);
Append(~maximals, sub2);

/* Alt(5). These are C_9 subgroups of PSL(2, q), fusing under PGL(2, q)
 */

if q mod 5 eq 4 then
   if Print gt 1 then "Making Alt5"; end if;
   alt5_1:= (GetAlt5(q)@factor);
   alt5_2:= alt5_1^conj_invol;
   Append(~maximals, alt5_1);
   Append(~maximals, alt5_2);
end if;
if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, apsl, maximals, F, phi;

end function;


/* 
 * The following function returns the maximals of pgl, pgl.2 and
 * pgammal, intersected with psl. They are the same in each case. 
 * does not include trivialities.
 */
 
function OtherMaximals(group, q, type, dgroup : max:=true, Print:=0 )

fac:= Factorisation(q);
assert #fac eq 1 and fac[1][2] eq 2;

p:= fac[1][1];

if Print gt 1 then "Making standard pgl"; end if;
gl:= GL(2, p^2);
apsl := PGammaLD2(p^2);
factor := hom< gl->apsl | [apsl.1, apsl.2 ] >;

if Print gt 1 then "Making standard psl"; end if;
sl:= SL(2, p^2);
psl:= sl@factor;
AssertAttribute(psl, "Order", #PSL(2, p^2));

if Print gt 1 then "Making outer involution in PGL"; end if;
z:= PrimitiveElement(GF(q));
conj_invol:= (gl![z, 0, 0, 1])@factor;

field_auto:= apsl.3;

if Print gt 1 then print "Setting up homomorphisms"; end if;
homom, F, phi:=
   MakeHomom(dgroup, group, p, psl, apsl, type, conj_invol, field_auto:
             Print:=Print);
dh := Domain(homom);
apsl := sub<apsl | homom(dh.1), homom(dh.2), conj_invol, field_auto >;
AssertAttribute(apsl, "Order", #psl * 4);

maximals:=[];

if not max then
  return homom, apsl, maximals, F, phi;
end if;

if Print gt 1 then "Making reducible"; end if;
Append(~maximals, Stabiliser(psl, 1));

if Print gt 1 then "Making imprimitive"; end if;
Append(~maximals, Stabiliser(psl, {1, 2}));

if Print gt 1 then "Making semilinear"; end if;
Append(~maximals, GetSemilin(psl, p^2));
if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, apsl, maximals, F, phi;

end function;


/********************************************************************
 * The following is the main function. It takes a permutation 
 * group lying between psl(2, p^2) and pgammal(2, p^2), 
 * calls WhichGrp to identify which of the 5 possible groups it is, 
 * and then calls the appropriate maximal subgroups algorithm.
 */

function L2p2Identify(group, q : max := true, Print := 0)
fac:= Factorisation(q);
assert #fac eq 1 and fac[1][2] eq 2;
type, derived:= WhichGroup(group, q);
if type cmpeq "psl" or type cmpeq "psigmal" then
    return PslOrPsigmalMaximals(group,q,type,derived : max:=max, Print:=Print);
else
    return OtherMaximals(group, q, type, derived : max:=max, Print:=Print);
end if;

end function;
