freeze;

/*
Constructively recognise and find maximal subgroups  of L(2,p).?
Recognition by Derek Holt.
maximals by Colva Roney-Dougal
*/

/*******************************************************
* This function uses the Bray trick to find the        *
* centraliser of an involution "elt" in a subgroup     *
* "group" of a group isomorphic to psl "psl". the      *
* parameter "grpsize" is how big we expect the         *
* resulting group to be. OK to test group order cos in *
* situation where we use it the groups are rather      *
* small.                                               *
********************************************************/

function CentraliseInvol(group, psl, elt, grpsize)
//"centralising invol";
assert Order(elt) eq 2;
process:= RandomProcess(group);
made := false;
grp:= sub<psl|elt>;
while not made do
    x:= Random(process);
    com:= (elt, x);
    o:= Order(com);
    //"o =", o;
    q, r:= Quotrem(o, 2);
    if r eq 1 then
        added_elt:= x*(com^q);
        grp:= sub<psl|grp, added_elt>;
        if #grp eq grpsize then
            made:= true;
        end if;
    else
        grp:= sub<psl|grp, com^q, (elt, x^-1)^q>;
        if #grp eq grpsize then
            made:= true;
        end if;
    end if;
end while;

return grp;

end function;


/********************************************************
* This function uses the dihedral trick to find         *
* an  element conjugating elt1 to elt 2 (both of which  *
* have order 2)                                         *
*********************************************************/

function DihedralTrick(elt1, elt2, process)
//"dihedral trick";
x:= Random(process);
while (Order((elt1^x)*elt2) mod 2 eq 0) do
    x:= Random(process);
end while;
q, r:= Quotrem(Order((elt1^x)*elt2), 2);
return x*(elt2*(elt1^x))^q;
end function;



/********************************************************
* This function finds a group isomorphic to Alt(4) by   *
* taking two matrices of order 4 in SL(2, p) whose      *
* square is -I, and whose product is another mat        *
* of order 4, taking the image of these in PSL          *
* (this is the Sylow 2-subgroup of PSL), and then       *
* using the "extended dihedral trick" to find a 3-cycle *
* which permutes them.                                  *
* "factor" is the homomorphism from sl to psl, all other*
* variable names are pretty obvious.                    *
********************************************************/


function GetAlt4(factor, p, sl, psl)

process:= RandomProcess(psl);
a:= sl![0, -1, 1, 0];

j:= 0;
for i in [1..p-1] do
     bool, x:= IsSquare(GF(p)!(-1 - i^2));
     if bool then
         j:= GF(p)!i;
         break;
     end if;
end for;

b:= sl![j, x, x, -j];

first_group:= sub<sl | a, b>;
assert #first_group eq 8;
 
/* first_group is now the extraspecial 2-group inside sl.
 */

invols:= [a@factor, b@factor, (a*b)@factor]; 

/* invols are the generators of the elementary abelian group
 * inside psl.
 * the idea is that we find a 3-cycle permuting them. this 
 * gives us alt4.
 */

conj1:= DihedralTrick(invols[1], invols[2], process);

if (p mod 4) eq 3 then     
    cent:= CentraliseInvol(psl, psl, invols[1], p+1);
else
    cent:= CentraliseInvol(psl, psl, invols[1], p-1);
end if;

conj2:= DihedralTrick(invols[2], invols[3]^(conj1^-1),
                RandomProcess(cent));
cent2:= CentraliseInvol(cent, psl, invols[2], 4);

conj3:= DihedralTrick(invols[3], invols[1]^(conj1^-1*conj2^-1),
              RandomProcess(cent2)); 

alt4:= sub<psl| invols[1], invols[2], conj3*conj2*conj1>;

assert #alt4 eq 12;
 
return alt4;
end function;


/*********************************************************
*    This function finds a group isomorphic to Sym(4),   *
*    by finding an elt a of order 2, and elt b of        *
*    order 3, and replacing b by random conjugates of    *
*    itself until Order(a*b) eq 4. Really should         *
*    modify it to use the alt4 code, as I think this     *
*    will be much faster.                                *
**********************************************************/

function GetSym4(group)

proc:= RandomProcess(group);

founda:= false;
foundb:= false;

while not founda do
    x:= Random(proc);
    o:= Order(x);
    q, r:= Quotrem(o, 2);
    if r eq 0 then
        a:= x^q;
        founda:= true;
        //"a = ", a;
    end if;
end while;

foundfirstb:= false;
while not foundfirstb do
    x:= Random(proc);
    o:= Order(x);
    q, r:= Quotrem(o, 3);
    if r eq 0 then
        b:= x^q;
        foundfirstb:= true;
        //"firstb = ", b;
    end if;
end while;

while not foundb do
    b:= b^Random(proc);
    if Order(a*b) eq 4 then
        foundb:= true;
    end if;
end while;

sym4:= sub<group | a, b>;
assert #sym4 eq 24;
assert not IsAbelian(sym4);

return sym4;

end function;

/*
 * This function produces the reducible subgroup as a
 * subgroup of SL(2, p). input is p and my copy of SL(2, p).
 */

function GetReducible(p, sl)
z:= PrimitiveElement(GF(p));
grp:= sub<sl| [z, 0, 0, z^-1], [1, 1, 0, 1]>;
//assert #grp eq Integers()!(p*(p-1));
return grp;
end function;

/***********************************************************/

/* This function produces the semilinear group, by 
 * looking for a random pair of involutions that 
 * generate a dihedral group of the correct order, p+1.
 * input is a group isomorphic to PSL and the prime p. In practice
 * this is currently used with the *standard* copy of PSL, as this 
 * is likely to have smaller degree than the "black box" PSL generated 
 * by the user. 
 */

function GetSemilin(group, p)

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
    if Order(invol*y) eq Integers()!((p+1)/2) then
        made_semilin:= true;
    end if;
end while;

return sub<group|invol, y>;
end function;

/********************************************************/

/*********************************************************
*   This function produces Alt(5), as a group generated  *
*   by two mats [0, 1, -1, 0] and [a, b, c, d] where     *
*   this latter matrix has trace -1 and the product      * 
*   has trace (1-sqrt(5)/2)                              *
**********************************************************/

function GetAlt5(p)

assert IsPrime(p);

sigma:= GF(p)!((1 - Root(GF(p)!5, 2))/2);
 
a:= GF(p)!0;
P := PolynomialRing(GF(p)); b := P.1;
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

grp:= sub<SL(2, p) | SL(2, p)![0, 1, -1, 0], SL(2, p)![a, b, c, d]>;
if not #grp eq 120 then
    "failed to make Alt(5)";
end if;

return grp;
end function;


/* 
 * The first stage is to find generators a and b of group such that a has 
 * order 2, b has order 3 and ab has order p. These generate g, and
 * are unique up to automorphisms of g, and hence the mapping between
 * any pair of them is an isomorphism.
 */

FindInvolution := function(G)
proc := RandomProcess(G);
foundinvol:= false;
while not foundinvol do
      x:= Random(proc);
      o:= Order(x);
      q, r:= Quotrem(o, 2);
      if r eq 0 then
          invol:= x^q;
          foundinvol:= true;
      end if;
end while;
return invol;
end function;

FindThreeElement := function(G)
proc := RandomProcess(G);
foundthree_elt:=false;
while not foundthree_elt do
      y:= Random(proc);
      o:= Order(y);
      q, r:= Quotrem(o, 3);
      if r eq 0 then
          three_elt:= y^q;
          foundthree_elt:= true;
      end if;
end while;
return three_elt;
end function;

function FindGoodGens(group, p)
proc:= RandomProcess(group);

invol := FindInvolution(group);

three_elt := FindThreeElement(group);

made_grp:= false;
while not made_grp do
      three_elt:= three_elt^Random(proc);
      if Order(invol*three_elt) eq p then 
	 made_grp:= true;
      end if;
end while;

return invol, three_elt;
end function;

/* 
 * The following function constructs the isomorphism between the
 * permutation group "group" and our standard copy of psl "psl".
 * It does this by finding standard generators first for "psl" and
 * then for "group". These are unique up to group automorphisms, and
 * hence one may define an isomorphism by mapping the ordered pair
 * to the ordered pair. 
 * If group is pgl, then it identifies psl first as above, and then
 * locates an outer automorphism.
 */

function MakeHomom(dgroup, group, p, psl, pgl:Print:=0)

a1, c1:= FindGoodGens(psl, p);
a, c:= FindGoodGens(dgroup, p);
// We will use elements of order 2 and p as out generators, because the
// p-element fixes a unique point.
b1 := a1*c1; b:=a*c;
// try getting b1 to fix 1 - may help FPGroupStrong!
for x in Fix(b1) do
   isc, g := IsConjugate(psl,x,1);
   if isc then a1:=a1^g; b1:=b1^g; break; end if;
end for;

psls:= sub< psl |  a1, b1 >;
AssertAttribute(psls,"Order",#psl);
ChangeBase(~psls,[1]);
BSGS(psls);
ReduceGenerators(~psls);
t:=Cputime();
F,phi := FPGroupStrong(psls);
if Print gt 0 then print "Time for FPGroupStrong:",Cputime(t); end if;

dgs := sub<dgroup|a,b>;
AssertAttribute(dgs,"Order",#psl);

homom:= hom< dgs -> pgl|[a1, b1]>;
if dgroup eq group then
    return homom, F, phi;
end if;


proc:= RandomProcess(group);

c := Random(proc);
while c in dgroup do c := Random(proc); end while;

ac := (a^c) @ homom;  bc := (b^c) @ homom;

proc := RandomProcess(pgl);

c1 := Random(proc);
while c1 in psl do c1 := Random(proc); end while;

proc := RandomProcess(psl);
g := DihedralTrick(a1^c1, ac, proc);

c1 := c1*g;

//print "Getting there!";

isc, g := IsConjugate(Centraliser(psl,ac),b1^c1,bc);
c1 := c1*g;

gs := sub<group|a,b,c>;
AssertAttribute(gs,"Order",#psl*2);
homom:= hom< gs -> pgl|[a1, b1, c1]>;

return homom, F, phi;
end function;
/*******************************************************************
*                   The main function                              *
********************************************************************/

function L2pIdentify(group, p: max:=true, Print:=0)
assert IsPrime(p);
assert p gt 11;

if Print gt 1 then "Making standard pgl"; end if;
sl:= SL(2, p);
gl:= GL(2, p);
factor, pgl:= OrbitAction(gl, Orbit(gl, sub<RSpace(gl)|[1,0]>));

if Print gt 1 then "Making standard psl"; end if;
psl:= sl@factor;
AssertAttribute(psl, "Order", #PSL(2, p));

if Print gt 1 then "Making outer involution"; end if;
conj_invol:= (gl![PrimitiveElement(GF(p)), 0, 0, 1])@factor;

o:= #group;
IsPSL := o eq #psl;
dgroup :=  DerivedSubgroup(group);

if Print gt 1 then "Setting up homomorphism"; end if;
homom, F, phi:= MakeHomom(dgroup, group, p, psl, pgl:Print:=Print);
dh := Domain(homom);
pgl := sub<pgl | homom(dh.1), homom(dh.2), conj_invol >;
AssertAttribute(pgl, "Order", #psl * 2);
 

maximals:=[];
if not max then
  return homom, pgl, maximals, F, phi;
end if;

/*
 * Reducible - isomorphic to p:(p-1)/2
 */
if Print gt 1 then "Making reducible"; end if;

Append(~maximals, (GetReducible(p, sl)@factor));

/*
 * Imprimitive - isomorphic to D_{p-1}. The former technique appears
 * to be faster. 
 */

if Print gt 1 then "Making imprimitive"; end if;
Append(~maximals, Stabiliser(psl, {1, 2}));

/*
 * Semilinear - isomorphic to D_{p+1}
 */
if Print gt 1 then "Making semilinear"; end if;
Append(~maximals, GetSemilin(psl, p));

/*
 *Extra-Special p-group - depends on congruence of p.
 */
mod16:= p^2 mod 16;
mod5:= p mod 5;
if mod16 eq 1 then 
   if IsPSL then
      if Print gt 1 then "Making sym4"; end if;
      sym4_1:= GetSym4(psl);
      sym4_2:= sym4_1^conj_invol;
      Append(~maximals, sym4_1);
      Append(~maximals, sym4_2);
   else    /*Sym4s fuse under PGL, so no maximals to find*/
      ;
   end if;
elif (mod5 eq 1 or mod5 eq 4) then
   if IsPSL then
      ;
   else
      if Print gt 1 then "Making alt(4)"; end if;
      Append(~maximals, GetAlt4(factor, p, sl, psl));
   end if;
else
   if Print gt 1 then "Making alt(4)"; end if;
   Append(~maximals, GetAlt4(factor, p, sl, psl));
end if;


/* Alt(5). These are C_9 subgroups of PSL(2, p), fusing under PGL(2, p)
 */

if ((mod5 eq 1 or mod5 eq 4) and IsPSL) then
   if Print gt 1 then "Making alt5"; end if;
   alt5_1:= (GetAlt5(p)@factor);
   alt5_2:= alt5_1^conj_invol;
   Append(~maximals, alt5_1);
   Append(~maximals, alt5_2);
end if;
if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, pgl, maximals, F, phi;
end function;
