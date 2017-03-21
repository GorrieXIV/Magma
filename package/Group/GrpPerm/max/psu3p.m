freeze;

import "psl2p.m": DihedralTrick, FindInvolution;

/* 
Constructively recognise and find maximal subgroups of U(3,p).?
Recognition by Derek Holt.
Maximals by Colva Roney-Dougal.
*/

ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power.
  local list;
  list:= Eltseq(a);
  for i in [1..#list] do list[i]:= list[i]^q; end for;
  return list;
end function;

/*
 * This function finds a conjugating matrix that sends a group
 * preserving a unitary form to a group preserving a unitary form
 * AntiDiag([1, 1, 1]);
 *
 * It could be made faster by doing row ops, and then using the fact
 * that the form matrix is hermitian at each point, but I figure that
 * in the 3\times3 case it really doesn't matter. 
 */

function CorrectFormPSU3p(form, p)

conj:= Identity(GL(3, p^2));
temp:= form;
while temp[1][1] eq 0 do
    conj:= Random(GL(3, p^2));
    temp:= conj*form*Transpose(GL(3, p^2)!ListMatToQ(conj, p));
end while;
form:= temp;

//"form = ", form;

assert not form[1][1] eq 0; 
conj_1:= GL(3, p^2 )![GF(p^2)!1, 0, 0, 
                  -form[2][1]/form[1][1], GF(p^2)!1, 0,
                  -form[3][1]/form[1][1], 0, GF(p^2)!1];
form1:= conj_1*form*Transpose(GL(3, p^2)!ListMatToQ(conj_1, p));

//"form1 = ", form1:Magma;

assert form1[2][1] eq 0;
assert form1[3][1] eq 0;

temp1:= form1;
tempconj:= Identity(GL(3, p^2));
while temp1[2][2] eq 0 do
    temp:= Random(GL(2, p^2));
    tempconj:= GL(3, p^2)![1, 0, 0, 0, temp[1][1], temp[1][2], 0,
                                              temp[2][1], temp[2][2]];
    temp1:= tempconj*form1*Transpose(GL(3, p^2)!ListMatToQ(tempconj, p));
end while;


conj_2:= GL(3, p^2)![1, 0, 0, 0, 1, 0, 0, -form1[3][2]/form1[2][2], 1];
form2:= conj_2*form1*Transpose(GL(3, p^2)!ListMatToQ(conj_2, p));

//"form2= ", form2:Magma;

assert IsDiagonal(form2);

conj_3:= GL(3, p^2)!DiagonalMatrix([Root((GF(p^2)!form2[i][i])^-1, p+1) : i
                                                        in [1..3]]);


//"form3= ", conj_3*form2*Transpose(GL(3, p^2)!ListMatToQ(conj_3, p)):Magma;

t:= Root(GF(p^2)!(-1), p+1);
half:= GF(p^2)!(2^(-1));
conj_4:= GL(3, p^2)![1, 0, t, 0, 1, 0, half, 0, -t*half];

return (conj_4*conj_3*conj_2*conj_1)^-1;
end function;

/*This function returns the C_9 group 3.Alt(6), which is 
 *a subgroup of U(3, p) whenever 5 is a square in GF(p) (i.e. p = \pm
 *1 mod 5) and omega (a cube root of unity) is in GF(p^2) \setminus
 *GF(p)  (i.e. p = -1 mod 3).
 *
 *These two conditions arise from the fact that a representation is
 *unitary if and only if the map induced by the frobenius automorphism
 *is equal to complex conjugation. Since b5 is real it must be fixed
 *by the frobenius map, and so 5 must be a square in GF(p). Since
 *omega is complex it is not fixed by the frobenius map, and so must
 *lie in GF(p^2) \setminus GF(p).
 * 
 *Has been shown to produce the correct unitary group in range p in
 *[5..1000], that is, a unitary group with form the antidiagonal
 * matrix [1, 1, 1].
 */
 
function GetAlt6(p)
assert IsPrime(p);
assert IsSquare(GF(p)!5);

q:= p^2;

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

/* We now have a group with form matrix the identity matrix, this
 * needs to be conjugated so that it has form matrix AntiDiag([1, 1,
 * 1]), as this is the pre-defined unitary form in magma.
 */

x:= Root(GF(q)!(-1), p+1);
mat:= GL(3, q)![1, 0, x,
                0, 1, 0, 
                half, 0, -x*half];

return group^(mat^-1);

end function;

/* This is a maximal subgroup of SU whenever p+1 eq 0 mod 3. It
 * would be nice to get rid of the SL intersection at some point
 * The form of the matrix b ensures that the basis is always of 
 * orthonormal vectors, so we have to conjugate to make the matrix of
 * sesquilinear form into AntiDiag[1, 1, 1].
 */

function GetExtraspec(p)

z:= PrimitiveElement(GF(p^2));
omega:= z^Integers()!((p^2-1)/3);

if p^2 mod 9 eq 1 then
     ninth:= z^Integers()!((p^2-1)/9);
end if;

/*
 * matrix definitions. a and b generate the 3^(1+2), then c and
 * d are the normaliser. 
 */

a:= GL(3, p^2)!DiagonalMatrix([1, omega, omega^2]);
b:= GL(3, p^2)!
[0, 1, 0,
 0, 0, 1, 
 1, 0, 0];
if p^2 mod 9 eq 1 then
   c:= GL(3, p^2)!DiagonalMatrix([ninth^2, ninth^5, ninth^2]);
else
   c:= GL(3, p^2)!DiagonalMatrix([1, omega, 1]);
end if;
d:= GL(3, p^2)!
[1,   1,        1,
 1, omega, omega^2,
 1, omega^2, omega];

/* 
 * If p^2 mod 9 is not equal to 1 then the derived subgroup of 
 * newgrp is equal to the intersection with SL. If p^2 mod 9 is
 * equal to 1 then the intersection is bigger than this.
 */

grp:= sub<GL(3, p^2)|a, b, c, d>;
if p^2 mod 9 eq 1 then
    newgrp:= grp meet SL(3, p^2);
else
    newgrp:= DerivedSubgroup(grp);
end if;

/*
 * Finally we conjugate so that the unitary form preserved by
 * the group is the correct one.
 */

t:= Root(GF(p^2)!(-1), p+1);
half:= GF(p^2)!(2^(-1));
conj_mat:= GL(3, p^2)![1, 0, t, 0, 1, 0, half, 0, -t*half];

return newgrp^(conj_mat^(-1));
end function;

/*
 * This makes the maximal imprimitive subgroup of SU(3, p). We 
 * make the matrices in the obvious way (just the same as in the
 * linear case, only we use elements of order dividing p+1). We
 * then conjugate the group so that it preserves AntiDiag([1, 1, 1]),
 * the form matrix preserved by SU(3, p) in Magma.
 * Tested for correct order in SL and form type for p in [3..500].
 */

function GetImprims(p)
z:= PrimitiveElement(GF(p^2))^(p-1);
t:= Root(GF(p^2)!(-1), p+1);
half:= GF(p^2)!(2^-1);
a:= GL(3, p^2)!DiagonalMatrix([z, 1, z^-1]);
b:= GL(3, p^2)![0, 1, 0,
                0, 0, 1,
                1, 0, 0];
c:= GL(3, p^2)![-1, 0, 0,
                 0, 0, -1,
                 0, -1, 0];

conj_mat:= GL(3, p^2)![1, 0, t,
                      0, 1, 0,
                      half, 0, -half*t];

grp:= sub<GL(3, p^2)|a, b, c>;
return grp^(conj_mat^(-1));
end function;

/*This function produces the C_9 group PSL(2, 7), which is a subgroup 
 * U(3, p) whenever Sqrt(-7) lies in GF(p^2) \setminus GF(p).
 *The matrices come from the Atlas "Reflection" construction. 
 * Tested on all appropriate p^2 in range [9..10000].
 */

function GetPSL2_7(q)
assert q gt 3 and not q eq 7;
fac:= Factorisation(q);
p:= fac[1][1];
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

//assert #group eq 168;

bool, form:= UnitaryForm(group);
assert bool;
return group^CorrectFormPSU3p(form,p);
end function;

/* This function gets the stabiliser of a nonisotropic point. 
 * It needs improving shortly - this is woefully inefficient.
 * [0, 1, 0] is always a nonisotropic point. 
 */

function GetReducibles(su, p)
return Stabiliser(su, sub<RSpace(su)|[0, 1, 0]>);
end function;

/* Tested for p in [5..11] */


function GetSemilin(p)

//"making Singer Cycle";
pol := DefiningPolynomial(GF(p^6), GF(p^2));
x := Parent(pol).1;
coeffs:= Coefficients(pol);
mat:= GL(3, p^2)![0, 1, 0, 0, 0, 1, -coeffs[1], -coeffs[2], -coeffs[3]];

//"forcing order of mat to be p^2 - p + 1";
o:= Order(mat);
q, r:= Quotrem(o, p^2 - p + 1);
assert r eq 0;
newelt:= SL(3, p^2)!Eltseq(mat^q);


//find field automorphism - the reason that x^7 has been added to the
//argument below is to ensured that cxp[2] and cxp2[2] are always defined!
cxp := Coefficients(x^7 + x^(p^2) mod pol);
cxp2 := Coefficients(x^7 + (x^2)^(p^2) mod pol);
field_auto := SL(3, p^2)![1,0,0,cxp[1],cxp[2],cxp[3],cxp2[1],cxp2[2],cxp2[3]];

//"making the group preserve the correct form";
grp:= sub<SL(3, p^2)|newelt, field_auto>;
bool, form:= UnitaryForm(grp);
assert bool eq true;
return grp^CorrectFormPSU3p(form, p);

end function;

/*
 * This function produces the subfield group SO(3, p) \leq SU(3, p). It
 * always appears to have form matrix AntiDiag[1, form_elt, 1], so 
 * conjugating by a Diag[1, x, 1], where x*x^p eq form_elt, turns 
 * it into a group with form matrix AntiDiag[1, 1, 1], i.e. a subgroup of
 * the standard magma copy of SU(3, p).
 *
 * Update by billu : May 2006: make more robust
 * new forms code from Derek => form_mat is AntiDiag[a,b,a] with a != 0,
 * so we now scale by 1/a to get form_elt
 */

function GetSubfield(p)
    F := GF(p^2);
    gl := GL(3,F);
    newgrp:= sub<gl|Eltseq(SO(3, p).1), Eltseq(SO(3, p).2)>;
    //form_mat:= ClassicalForms(newgrp)`bilinearForm;
    isit, form_mat:= UnitaryForm(newgrp);
    assert isit;
    assert IsZero(form_mat[1,1]);
    assert IsZero(form_mat[3,3]);
    assert IsZero(form_mat[1,2]);
    assert IsZero(form_mat[2,3]);
    assert not IsZero(form_mat[1,3]);
    form_elt:= form_mat[2,2] / form_mat[1,3];
    conj_elt:= Root(F!form_elt, p+1);
    conj_mat:= gl!DiagonalMatrix([1, conj_elt, 1]);
    return newgrp^conj_mat;
end function;

/*****************************************************
* The following function is used in the noncoprime   *
* case - we start by making 3 copies of a group,     *
* which are conjugate under the outer 3-cycle.       *
* a unique one of these will commute with our        *
* given involution, so in the case psl.2 we require  *
* this to be appended to the list of maximals        *
*****************************************************/

function SelectGroup(psu, initial, three_cyc, invol)
looking := true;
for i in [0..2] do
    group := initial^(three_cyc^i);
    if IsConjugate(psu, group, group^invol) then
        looking := false;
        break;
    end if;
end for;
if looking then "Error normalising subgroup in PSL.2"; end if;
return group;
end function;

/*****************************************************
* First we do the case where 3 does not divide       *
* p+1, as this has much simpler behavour - Out = 2.  *
*                                                    *
******************************************************/

forward MakeSU3HomomGeneral;

function CoprimeMaximals(group, p: max:= true, Print:=0)

/*
 * 3 does not divide (p+1), so pgu = psu. Since all subgroups of
 * PSU extend to PSigmaU there is no need for an outer involution. 
 */

if Print gt 1 then print "Making standard group"; end if;
  su := SU(3,p);
  psu := PSU(3,p);
  apsu := PGammaU(3,p);
  // get generators to correspond!
  for g in Generators(apsu) do if not g in psu then
    apsu := sub<apsu | psu.1, psu.2, g >;
    AssertAttribute(apsu, "Order", #psu * 2);
    break;
  end if; end for;
  factor := hom< su->apsu | [ apsu.1, apsu.2] >;
    
o:= Order(group);
IsPSL := o eq #psu;

if Print gt 1 then print "Setting up homomorphism"; end if;
homom, soc, group:=
       MakeSU3HomomGeneral(group, p, 1, psu, apsu, factor : Print:=0);

if Print gt 1 then print "Calling FPGroupStrong"; end if;
 F, phi := FPGroupStrong(sub< psu | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);

//homom, F, phi := MakeHomom(dgroup, group, p, psu, apsu : Print:=Print);
dh := Domain(homom);

apsu := sub<apsu | homom(dh.1), homom(dh.2), apsu.3 >;
AssertAttribute(apsu, "Order", #psu * 2);

maximals:= [];
if not max then
  return homom, apsu, maximals, F, phi;
end if;

/*
 * Reducibles. We need the stabiliser of an isotropic and a 
 * nonisotropic point. The istropic point is a point in the permutation
 * action of psu. 
 */

if Print gt 1 then print "Getting reducibles"; end if;
//isotropic
Append(~maximals, Stabiliser(psu, 1));
//nonisotropic.
Append(~maximals, GetReducibles(su, p)@factor);

/* 
 * The maximal imprimitive is unique, and extends. The function 
 * returns a matrix group, so we factor by the centre before applying 
 * homom. 
 */

if Print gt 1 then print "Getting imprimitives"; end if;
Append(~maximals, GetImprims(p)@factor);

/*
 * This needs doing.
 */

if Print gt 1 then print "Getting semilinears"; end if;
Append(~maximals, GetSemilin(p)@factor);

/*
 * There is a subfield subgroup PSO(3, p), which extends
 */

if Print gt 1 then print "Getting classicals"; end if;
Append(~maximals, GetSubfield(p)@factor);

/*
 * Finally, there is PSL(2, 7), which is a maximal C_9 group whenever 
 * -7 is a nonsquare in GF(p). It extends. 
 */

if p gt 7 and not IsSquare(GF(p)!(-7)) then
    if Print gt 1 then print "Getting PSL(2, 7)"; end if;
    Append(~maximals, GetPSL2_7(p^2)@factor);
end if;
    if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, apsu, maximals, F, phi;
end function;



/****************************************************
* Now we do the case where 3 does divide p+1. This  *
* means that we get additional conjugacy classes    *
* of some groups, we get extraspecial groups, and   *
* we get alt_6 as a C_9 group whenever 5 is a       *
* square in GF(p) and psl2_7 whenever (-7) is a     *
* square in GF(p).                                  *
*****************************************************/

function NonCoprimeMaximals(group, p: max:= true, Print:=0)

if Print gt 1 then print "Making standard group"; end if;
  su := SU(3,p);
  psu := PSU(3,p);
  apsu := PGammaU(3,p);
  // get generators in desired order!
  gens := [apsu|psu.1, psu.2];
  for g in Generators(apsu) do if g^3 in psu and not g in psu then
    Append(~gens,g); break;
  end if; end for;
  for g in Generators(apsu) do if g^2 in psu and not g in psu then
    Append(~gens,g); break;
  end if; end for;
  apsu := sub<apsu|gens>;
  AssertAttribute(apsu, "Order", #psu * 6);
  factor := hom< su->apsu | [ apsu.1, apsu.2] >;

//dgroup:= DerivedSubgroup(group);
o:= Order(group);
orderpsu:= #psu;
if o eq orderpsu then
    type:= "psu";
elif o eq 2*orderpsu then
    type:= "psigmau";
elif o eq 3*orderpsu then
    type:= "pgu";
elif o eq 6*orderpsu then
    type:= "pgammau";
    //dgroup:= DerivedSubgroup(dgroup);
else
    error "Function only accepts almost simple groups with socle PSU(3,p)";
end if;
if Print gt 1 then "Group is type ", type; end if;
//Note - dgroup is actually the socle, not always the derived group!

if Print gt 1 then print "Setting up homomorphism"; end if;
homom, soc, group:=
       MakeSU3HomomGeneral(group, p, 1, psu, apsu, factor : Print:=0);

if Print gt 1 then print "Calling FPGroupStrong"; end if;
 F, phi := FPGroupStrong(sub< psu | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);

//homom, F, phi := MakeHomom(dgroup, group, p, psu, apsu : Print:=Print);
dh := Domain(homom);

if type eq "psu" or type eq "psigmau" then
    three_cyc:= apsu.3;
else
    three_cyc:= homom(dh.3);
end if;
if type eq "psigmau" then invol := homom(dh.3);
elif type eq "pgammau" then invol := homom(dh.4);
else invol := apsu.4;
end if;

apsu := sub<apsu | homom(dh.1), homom(dh.2), three_cyc, invol >;
AssertAttribute(apsu, "Order", #psu * 6);

maximals:= [];
if not max then
  return homom, apsu, maximals, F, phi;
end if;

/*
 * Reducibles. We need the stabiliser of an isotropic and a 
 * nonisotropic point. The istropic point is a point in the permutation
 * action of psu. This could also be done with matrices, for
 * complexity analysis, as stabilising [1, 0, 0] would also do. In
 * practice however, this is faster. 
 *
 * The reducibles extend in each case.
 */

if Print gt 1 then print "Getting reducibles"; end if;
//isotropic
Append(~maximals, Stabiliser(psu, 1));
//nonisotropic.
Append(~maximals, GetReducibles(su, p)@factor);

/* 
 * The maximal imprimitive is unique, and extends in each case. The function 
 * returns a matrix group, so we factor by the centre before applying 
 * homom. 
 */

if Print gt 1 then print "Getting imprimitives"; end if;
Append(~maximals, GetImprims(p)@factor);

/*
 * This needs doing.
 */

if Print gt 1 then print "Getting semilinear"; end if;
Append(~maximals, GetSemilin(p)@factor);


/*
 * There is a subfield subgroup PSO(3, p). In a similar fashion to the 
 * PSL(3, p) code there are three copies of this, with Sym(3) acting
 * them. So for psu there are 3 intersections, for psigmau there is one,
 * and for pgu and pgammau there are none. 
 */

if type eq "psu" then
    if Print gt 1 then "Getting subfield"; end if;
    initial:= GetSubfield(p)@factor;
    Append(~maximals, initial);
    Append(~maximals, initial^three_cyc);
    Append(~maximals, initial^(three_cyc^2));
elif type eq "psigmau" then
    if Print gt 1 then "Getting subfield"; end if;
    initial:= (GetSubfield(p)@factor);
    Append(~maximals, SelectGroup(psu, initial, three_cyc, invol));
end if;


/* 
 * The final geometric subgroup is the extraspecials. If p^2 mod 9 is
 * not equal to 1 then there's a unique copy which extends all the way
 * up. If p^2 mod 9 = 1 then there's 3 copies with the Sym(3) thing
 * going on.  
 */

if not (p^2 mod 9 eq 1) then
    if Print gt 1 then print "Getting extraspecials"; end if;
    Append(~maximals, GetExtraspec(p)@factor);
elif type eq "psu" then
    if Print gt 1 then print "Getting extraspecials"; end if;
    initial:= GetExtraspec(p)@factor;
    Append(~maximals, initial);
    Append(~maximals, initial^three_cyc);
    Append(~maximals, initial^(three_cyc^2));
elif type eq "psigmau" then
    if Print gt 1 then print "Getting extraspecial"; end if;
    initial:= GetExtraspec(p)@factor;
    Append(~maximals, SelectGroup(psu, initial, three_cyc, invol));
end if;

/*
 * There is a C_9 subgroup isomorphic to 3.Alt(6). This exists and is
 * maximal whenever 5 is a square in GF(p) and p+1= 0 mod 3 (which is
 * always true in this function). As in the subfield case, there are
 * three copies in PSU, which Sym(3) acting on them. So for psu ther
 * are 3 intersections, for psigmau there is one, and for pgu and 
 * pgammau there are none.
 */

if IsSquare(GF(p)!5) and type eq "psu" then
    if Print gt 1 then print "Getting alt6"; end if;
    initial:= GetAlt6(p)@factor;
    Append(~maximals, initial);
    Append(~maximals, initial^three_cyc);
    Append(~maximals, initial^(three_cyc^2));
elif IsSquare(GF(p)!5) and type eq "psigmau" then
    if Print gt 1 then print "Getting alt6"; end if;
    initial:= GetAlt6(p)@factor;
    Append(~maximals, SelectGroup(psu, initial, three_cyc, invol));
end if;

/*
 * Finally, there is PSL(2, 7), which is a maximal C_9 group whenever 
 * -7 is a nonsquare in GF(p). Once again we have the Sym(3)
 * pattern as for O(3, p) and 3.Alt(6).
 */

if p gt 7 and not IsSquare(GF(p)!(-7)) and type eq "psu" then
    if Print gt 1 then print "Getting PSL(2, 7)"; end if;
    initial:= GetPSL2_7(p^2)@factor;
    Append(~maximals, initial);
    Append(~maximals, initial^three_cyc);
    Append(~maximals, initial^(three_cyc^2));
elif p gt 7 and not IsSquare(GF(p)!(-7)) and type eq "psigmau" then
    if Print gt 1 then print "Getting PSL(2, 7)"; end if;
    initial:= (GetPSL2_7(p^2)@factor);
    Append(~maximals, SelectGroup(psu, initial, three_cyc, invol));
end if;
    if Print gt 1 then print "Found maximals in standard copy"; end if;

return homom, apsu, maximals, F, phi;
end function;


/*****************************************************
* This function ties all the rest together.          *
* The results have been compared with the ATLAS      *
* for p eq 7 and 11                                  *
*                                                    *
* NOTE: the input value is the prime p NOT p^2       *
******************************************************/


function U3pIdentify(group, p : max := true, Print := 0)
assert p gt 5 and IsPrime(p);
if ((p+1) mod 3) eq 0 then
    if Print gt 1 then "non coprime case"; end if;
    return NonCoprimeMaximals(group, p: max:=max, Print:=Print);
else
    if Print gt 1 then "coprime case"; end if;
    return CoprimeMaximals(group, p: max:=max, Print:=Print);
end if;

end function;

MakeSU3HomomGeneral :=
                  function(group, p, e, psu, apsu, factor : Print:=0)
  local works, GtoSU, SUtoG, mat, homom, ims,
    g, newgens, subsoc, subgp, psugens, imgens, CG, ce, isc, h, socle;

  soc := Socle(group);
  /* Reduce number of generators of soc, and
   * rearrange generators of group to get those of soc coming first
   */
  d:=3;
  repeat
    newgens := [ group | Random(soc), Random(soc) ];
    subsoc := sub<soc|newgens>; RandomSchreier(subsoc);
  until subsoc eq soc;
/*
  while subsoc ne soc do
    x:=Random(soc);
    while x in subsoc do x:=Random(soc); end while;
    Append(~newgens,x); subsoc := sub<soc|newgens>; RandomSchreier(subsoc);
  end while;
*/
  soc := subsoc;
  subgp := subsoc;
  for g in Generators(group) do
   if not g in subgp then Append(~newgens,g);
    subgp := sub< group | newgens >; RandomSchreier(subgp);
   end if;
  end for;
  group := subgp;

  works := false;
  while not works do works, GtoSU := RecogniseSU3(soc,p^e); end while;
  psugens := [];
  for  i in [1..Ngens(soc)] do
      mat := GtoSU(soc.i);
      Append(~psugens,mat@factor);
  end for;
  //Now identify images of all generators of group in apsu.
  ims := psugens;
  for i in [Ngens(soc)+1..Ngens(group)] do
      g := group.i;
      CG := apsu; ce := Id(apsu);
      for j in [1.. #psugens] do
        mat := GtoSU(soc.j^g);
        isc, h := IsConjugate(CG,psugens[j]^ce,mat@factor);
        if not isc then error "Conjugation error in Aut(PSU(d,q))"; end if;
        CG := Centraliser(CG,mat@factor);
        ce := ce*h;
      end for;
      Append(~ims,ce);
  end for;
  return hom< group -> apsu | ims >, soc, group;
end function;

