freeze;

/*
function names in this file:
WhichGroup(group, q)
OuterInvol(group, q)
CopiesInGU3(group, q, factor, homom)
Imprims(q)
Semilin(q)
SubfieldSO(q)
SubfieldSU(p, e)
U3qMaximals(group, q)
*/

import "unitreds.m" : IsotropKStab, NonisotropKStab;
import "select_conj.m": SelectGroupGeneral;
import "psu3p.m": MakeSU3HomomGeneral;

/*****************************************************************/
//This function takes as input a group with socle PSU(3, q) for
//some nonprime q and returns the socle, and an integer.
//this integer is -1 if (3, q+1) = 1 and so there is at most
//one conjugacy class of each type of subfield group in PSU (the 
//same is therefore true of each extension of PSU. The integer is
//0 if (3, q+1) = 3 and the group contains PGU, so that in many
//instances no subfield groups are maximal. The integer is 1 if (3,
//q+1) = 3 and the group does not contain PGU. This means that of the 
//three conjugate copies of subfield groups under PGU, one will
//extend to a maximal subgroup of the input group, and the other two
//fuse. 

function WhichGroup(group, q)

  soc:= Socle(group);
  out_group, f:= quo<group|soc>;

  if Gcd(q+1, 3) eq 1 then
    return soc, -1;
  end if;

  if soc eq group then
    return soc, 3;
  end if;

  fac:= Factorisation(q);
  p:= fac[1][1]; e:= fac[1][2];
  if Gcd(e, 3) eq 1 then
    if #out_group mod 3 eq 0 then
      return soc, 0;
    elif IsEven(#out_group) then
      return soc, 1;
    else
      return soc, 3;
    end if;
  end if;

  assert e mod 3 eq 0;
  if not IsCyclic(out_group) or #out_group mod 9 eq 0 then
    return soc, 0;
  end if;

  if not (#out_group mod 3 eq 0) then
    if IsEven(#out_group) then
      return soc, 1;
    else
      return soc, 3;
    end if;
  end if;

  assert #out_group mod 3 eq 0; 
  //this final bit is somewhat time-consuming, but at least is
  //guaranteed to be right: trying to distinguish between the 
  //(at least) 3 groups of type PSU.3m. The one which is a subgroup of 
  //PSigmaU has different splitting and fusion patterns to the others.  
  assert #out_group mod 3 eq 0;
  m:= #out_group;
  s3:= SylowSubgroup(group, 3);
  n:= NormalSubgroups(PSigmaU(3, q): OrderEqual:= #group);
  target:= n[1]`subgroup;
  s3_sigma:= SylowSubgroup(target, 3);
  cls_group:= Classes(s3);
  cls_sigma:= Classes(s3_sigma);
  if not #cls_group eq #cls_sigma then
    return soc, 0;
  end if;
  info_group:= [<cls_group[i][1],cls_group[i][2]>: i in[1..#cls_group]];
  info_sigma:= [<cls_sigma[i][1],cls_sigma[i][2]>: i in[1..#cls_sigma]];
  if info_group eq info_sigma then
    if IsEven(#out_group) then
      return soc, 1;
    else 
      return soc, 3;
    end if;
  else
    return soc, 0;
  end if;

end function;

/*********************************************************************/
//This takes as input a group and its socle, which should be of 
//even index, and returns an outer involution.

function OuterInvol(group, socle)
  assert IsEven(#group div #socle);
  while true do
    x:= Random(group);
    o:= Order(x);
    if IsEven(o) and not x^(o div 2) in socle then
        return x^(o div 2);
    end if;
  end while;
  return 0;
end function;

/**********************************************************************/
//this function takes a subgroup of SU(3, q) and makes three copies of
//it which will be conjugate under GU but will not generally be
//conjugate under SU:

function CopiesInGU3(group, q, factor)
  z:= PrimitiveElement(GF(q^2));
  three_cyc:= GL(3, q^2)!DiagonalMatrix([1, z^(q-1), 1]);
  groups:= [];
  for i in [0..2] do
    Append(~groups, (group^(three_cyc^i))@factor);
  end for;
  return groups;
end function;
  
/**********************************************************************/
//This takes a prime power q and returns the maximal imprimitive
//subgroup   of SU(3, q).
 
function Imprims(q)
  z:= PrimitiveElement(GF(q^2))^(q-1);
  a:= GL(3, q^2)!DiagonalMatrix([z, 1, z^-1]);
  b:= GL(3, q^2)![0, 1, 0,
                0, 0, 1,
                1, 0, 0];
  c:= GL(3, q^2)![-1, 0, 0,
                 0, 0, -1,
                 0, -1, 0];
  if IsOdd(q) then
    t:= Root(GF(q^2)!(-1), q+1);
    half:= GF(q^2)!(2^-1);
    conj_mat:= GL(3, q^2)![1, 0, t,
                      0, 1, 0,
                      half, 0, -half*t];
  else
    conj_mat:= GL(3, q^2)!CorrectForm(
         Matrix(GF(q^2),3,3,[0,0,1,0,1,0,1,0,0]), 3, q^2, "unitary");
  end if;

  grp:= sub<GL(3, q^2)|a, b, c>;
  return grp^(conj_mat^-1);
end function;

/*******************************************************************/
//This takes the prime power q and returns the maximal semilinear
//subgroup of SU(3, q).

function Semilin(q)

  //"making Singer Cycle";
  pol := DefiningPolynomial(GF(q^6), GF(q^2));
  x := Parent(pol).1;
  coeffs:= Coefficients(pol);
  mat:= GL(3, q^2)![0, 1, 0, 0, 0, 1, -coeffs[1], -coeffs[2], -coeffs[3]];

  //"forcing order of mat to be q^2 - q + 1";
  o:= Order(mat);
  quot, r:= Quotrem(o, q^2 - q + 1);
  assert r eq 0;
  newelt:= SL(3, q^2)!Eltseq(mat^quot);


  //find field automorphism - the reason that x^3 has been added to the
  //argument below is to ensured that cxp[2] and cxp2[2] are always defined!
  cxp := Coefficients(x^7 + x^(q^2) mod pol);
  cxp2 := Coefficients(x^7 + (x^2)^(q^2) mod pol);
  field_auto:= SL(3, q^2)![1, 0, 0,
                  cxp[1],cxp[2],cxp[3],
                 cxp2[1],cxp2[2],cxp2[3]];

  //"making the group preserve the correct form";
  grp:= sub<SL(3, q^2)|newelt, field_auto>;
  bool, form:= UnitaryForm(grp);
  assert bool eq true;
  mat1:= GL(3, q^2)!CorrectForm(form, 3, q^2, "unitary");
  f2:= Matrix(GF(q^2),3,3,[0, 0, 1, 0, 1, 0, 1, 0, 0]);
  mat2:= GL(3, q^2)!CorrectForm(f2, 3, q^2, "unitary");
  return grp^(mat1*mat2^-1);  

end function;


/**********************************************************************/
/*
 * This function produces the subfield group SO(3, q) \leq SU(3, q).
 */

function SubfieldSO(q)
  newgrp:= sub<GL(3, q^2)|Eltseq(SO(3, q).1), Eltseq(SO(3, q).2)>;
  isit, form_mat:= UnitaryForm(newgrp);
  //form_mat:= ClassicalForms(newgrp)`sesquilinearForm;
  mat1:= GL(3, q^2)!CorrectForm(form_mat, 3, q^2, "unitary");
  mat2:= GL(3, q^2)!CorrectForm(
      Matrix(GF(q^2),3,3,[0, 0, 1, 0, 1, 0, 1, 0, 0]), 3, q^2, "unitary");
  return newgrp^(mat1*mat2^-1);
end function;

/******************************************************************/
//This function produces the collection of subfield groups SU(3,
//q^(1/b)).(b, d), where d:= (q+1, 3). It also returns Gcd(b, d) in
//each case, as PSU has (b, d) copies of the group, which fuse under
//PGU. 

function SubfieldSU(p, e)
  groups:=[];
  fac:= Factorisation(e);
  d:= Gcd(p^e+1, 3);
  z:= PrimitiveElement(GF(p^(2*e)));
  prim_scal:= ScalarMatrix(3, z^((p^(2*e)-1) div d));
  for facs in fac do 
    b:= facs[1];
    if IsPrime(b) and IsOdd(b) then
      f:= e div b;
      newgrp:= sub<GL(3, p^(2*e))|Eltseq(SU(3,
                           p^f).1),Eltseq(SU(3,p^f).2), prim_scal>;
      c:= Gcd(b, Gcd(p^e+1, 3));
      if c eq 3 then
        out_elt:= GL(3, p^(2*e))!Eltseq(GU(3, p^f).-1);
        x:= ((p^(2*e)-1)*p^f) div((p^f+1)*3);
        scal:= GL(3, p^(2*e))!ScalarMatrix(3, z^x);
        newgrp:= sub<GL(3, p^(2*e))|newgrp, out_elt*scal>;
      end if;
      Append(~groups, <Gcd(b, d), newgrp>);
    end if;
  end for;
  return groups;
end function;

/******************************************************************/
//This is the main function. Takes as input a group with socle PSU(3,
//q) and the integer q. q is assumed to be a proper prime power
//(i.e. not prime). Returns the maximal subgroups of the input group.

function U3qIdentify(group, q : max:= true, Print:=0)
  
  fac:= Factorisation(q);
  assert #fac eq 1;
  p := fac[1][1];
  e := fac[1][2];
  assert e gt 1;

  if Print gt 1 then "making standard group"; end if;
  gu := GU(3,q);
  su := SU(3,q);
  apsu := PGammaU(3,q);
  factor := hom< gu->apsu | [apsu.i :  i in [1..Ngens(gu)]] >;
  psu := su @ factor;

  if Print gt 1 then "setting up isomorphism"; end if;
  //homom, soc, group := MakeHomom(group, q, psu, apsu : Print:=Print);
  homom, soc, group :=
          MakeSU3HomomGeneral(group, p, e, psu, apsu, factor : Print:=Print);

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psu | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);
  
  if (q+1) mod 3 eq 0 then
    gens := [apsu|homom(group.1), homom(group.2), apsu.1, apsu.3];
  else gens := [apsu|homom(group.1), homom(group.2), apsu.3];
  end if;
  apsu := sub<apsu|gens>;

  maximals:= [];
  if not max then
    return homom, apsu, maximals, F, phi;
  end if;

  z:= PrimitiveElement(GF(q^2));
  
  soc, subgrp_copies:= WhichGroup(group, q);
  if subgrp_copies gt 0 then
    three_cyc:= (GL(3, q^2)!DiagonalMatrix([1, z^(q-1), 1])) @ factor;
  end if;
  if subgrp_copies eq 1 then
    out_invol:= OuterInvol(group, soc) @ homom;
  end if;

  if Print gt 1 then "getting reducibles"; end if;
  //isotropic
  //Append(~maximals, Stabiliser(psu, 1));
  Append(~maximals, IsotropKStab(3, q, 1)@factor);
  //nonisotropic.
  Append(~maximals, NonisotropKStab(3, q, 1)@factor);

  if Print gt 1 then "getting imprimitives"; end if;
  Append(~maximals, Imprims(q)@factor);

  if Print gt 1 then "getting semilinears"; end if;
  Append(~maximals, Semilin(q)@factor);

  if Print gt 1 then "getting unitary subfields"; end if;
  fac:= Factorisation(q); 
  p:= fac[1][1]; e:= fac[1][2];
  subfields:= SubfieldSU(p, e);
  for x in subfields do
    if x[1] eq 1 then
      Append(~maximals, x[2]@factor);
    elif x[1] eq 3 and subgrp_copies eq 1 then
      copy_of_x:= SelectGroupGeneral(psu,x[2]@factor,three_cyc,out_invol);
      maximals:= maximals cat [copy_of_x];
    elif x[1] eq 3 and subgrp_copies eq 3 then
      copies:= CopiesInGU3(x[2], q, factor);
      maximals:= maximals cat copies;
    end if;
  end for;
  
  if not IsEven(q) and not subgrp_copies eq 0 then
    if Print gt 1 then "getting orthogonal subfields"; end if;
    so:= SubfieldSO(q);
    if subgrp_copies eq -1 then
      Append(~maximals, so@factor);
    elif subgrp_copies eq 1 then
      copy_of_so:= SelectGroupGeneral(psu,so@factor,three_cyc,out_invol);
      maximals:= maximals cat [copy_of_so];
    elif subgrp_copies eq 3 then
      copies:= CopiesInGU3(so, q, factor);
      maximals:= maximals cat copies;
    end if;
  end if;
  
  return homom, apsu, maximals, F, phi;

end function;
