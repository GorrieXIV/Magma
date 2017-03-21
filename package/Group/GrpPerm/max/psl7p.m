freeze;
/*
This file contains functions called:
GetInvol(group,kernel)
Deq1WhichGroup(quot,groupquot,delta,iota,p)
Deq7WhichGroup(quot,groupquot,delta,iota,p,proj)
Deq1Maximals(p, factor,  is_novelty, has_sl211, has_sl3q, Print)
Deq7Maximals(p, factor, psl, d6, Print)
L7pIdentify(group, p)
*/

import "reds.m": SLPointStab, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
SLStabOfNSpaceMissDual, SLStabOfHalfDim;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "normes.m":NormaliserOfExtraSpecialGroup;
import "select_conj.m": ImageCopies, SelectGroupFromSubset;
import "classicals.m" : NormOfSp, NormOfO;
import "psl2q.m": MakeHomomGeneral;
import "construct.m": ReduceOverFiniteField;
import "gl2.m": PGL2, PSL2;

//files from DFH - slightly modified to return functions not 
//objects.
/*
load "~colva/maximals/code/construct.m";
load "~colva/maximals/code/psl7p/u33d7b";
*/

function Getu33d7b(p)
  c9lib := GetLibraryRoot() cat "/c9lattices/";
  _LRS := Read(c9lib cat "u33d7b");
  _LR := eval _LRS;
  L:= ReduceOverFiniteField(_LR,p);
  c9:= L[1];
  //can remove this later.
  assert IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and
  IsPrimitive(c9) and (not IsTensor(c9)) and
  ClassicalForms(c9)`formType eq "linear";
  return c9;
end function;


/****************************************************************/
//used for finding outer involution - very small group so no point 
//being clever

function GetInvol(group, kernel)
  invol:= Random(group);
  while (invol in kernel) or (not (Order(invol) eq 2)) do
    invol:= Random(group);
  end while;
  return invol;
end function;


/****************************************************************/

/* d eq 1 WhichGroup we have Out(PSL7(p)) = 2. 
    possible groups: PSL itself and Aut(PSL).
*/   

function Deq1WhichGroup(group, p)

  assert IsPrime(p) and Gcd(p-1, 7) eq 1;

  //first check whether PSL, else novelty C1s
  is_novelty:= #group eq (2*#SL(7, p));

  //single class of u33 if p equiv 1 mod 4
  has_u33:= (p mod 4) eq 1;

  return is_novelty, has_u33;
end function;


/* d eq 7 WhichGroup we have Out(PSL7(p)) = D_{2 x 7}
*/ 

function Deq7WhichGroup(group,soc,apsl,psl,p,homom)

  DT:= recformat<is_novelty:Booleans(),in_ker:Booleans(),
    in_stab:Booleans(),has_u33:Booleans(),invol>; 

  d7:= rec<DT|>;
 
  quot_order:= #group div #psl;

  if quot_order eq 2 then
    quot, proj:= quo<apsl|psl>;
    newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
    groupquot := sub< quot | [proj(g) : g in newgens] >; 
  end if;

  //first check whether subgroup of PGL.
  d7`is_novelty:= IsEven(quot_order);

  //action on all groups with more than one class has trivial kernel.
  d7`in_ker:= quot_order eq 1;

  //stabiliser of all groups with more than one class is involution
  d7`in_stab:= quot_order lt 3;
  if d7`in_stab and not d7`in_ker then
    d7`invol := GetInvol(groupquot, sub<groupquot|>)@@proj;
  end if;

  d7`has_u33:= ((p mod 4) eq 1) and d7`in_stab;

  return d7;

end function;


/****************************************************************/

//This makes maximal subgroups when Gcd(p-1, 7) = 1.

function Deq1Maximals(p, factor,  is_novelty, has_u33, Print)

  //PSL(7, 2) and PSL(7, 3) have already been done as special cases.
  assert p gt 3 and IsPrime(p);
  diag:= GL(7, p).1@factor;

  maximals:= [];
  
  if Print gt 1 then "getting reducibles"; end if;
  if not is_novelty then
    Append(~maximals,  (SLPointStab(7, p)@factor));
    for i in [2..6] do
      Append(~maximals,  (SLStabOfNSpace(7, p, i)@factor));
    end for;
  else 
    for i in [1..3] do
      Append(~maximals, (SLStabOfNSpaceMeetDual(7, p, i)@factor));
      Append(~maximals, (SLStabOfNSpaceMissDual(7, p, i)@factor));
    end for;
  end if;

  if Print gt 1 then "getting imprimitives"; end if;
  Append(~maximals, (ImprimsMeetSL(7, p, 7)@factor));
  
  if Print gt 1 then "getting superfields"; end if;
  Append(~maximals, (GammaLMeetSL(7, p, 7)@factor));

  if Print gt 1 then "getting orthogonal"; end if;
  so:= NormOfO(7, p, 0);
  Append(~maximals, so@factor);

  //finally the C9s.
  if has_u33 then
    if Print gt 1 then "getting U_3(3)"; end if;
    c9:= Getu33d7b(p);
    Append(~maximals, c9@factor);
  end if;

  return maximals;
end function;




/********************************************************************/
//makes maximals when (p-1, 7) = 7.
//d7 is all the data about where in the group we are, and hence what
//subgroups and conjugacy classes must be made. 
function Deq7Maximals(p, factor, psl, d7, Print)

  assert IsPrime(p);
  assert p mod 7 eq 1;
  diag:= GL(7, p).1@factor;

  maximals:= [];

  if Print gt 1 then "getting reducibles"; end if;
  if not d7`is_novelty then
    Append(~maximals,  (SLPointStab(7, p)@factor));
    for i in [2..6] do
      Append(~maximals, (SLStabOfNSpace(7, p, i)@factor));
    end for;
  else 
    for i in [1..3] do
      Append(~maximals, (SLStabOfNSpaceMeetDual(7, p, i)@factor));
      Append(~maximals, (SLStabOfNSpaceMissDual(7, p, i)@factor));
    end for;
  end if;

  if Print gt 1 then "getting imprimitives"; end if;
  Append(~maximals, (ImprimsMeetSL(7, p, 7)@factor));

  if Print gt 1 then "getting semilinears"; end if;
  Append(~maximals, (GammaLMeetSL(7, p, 7)@factor));

  if d7`in_stab then
    if Print gt 1 then "getting extraspecial groups"; end if;
    ext:= NormaliserOfExtraSpecialGroup(7, p);
    ext1:= sub<ext|[ext.i : i in [1..Ngens(ext)] | Determinant(ext.i)
      eq 1]>;
    if d7`in_ker then
      groups:= ImageCopies(ext1@factor,7,diag);
      maximals:= maximals cat groups;
    else
      Append(~maximals,SelectGroupFromSubset(psl,ext1@factor,diag,d7`invol,7));
    end if;

    if Print gt 1 then "getting orthogonal groups"; end if;
    so:= NormOfO(7, p, 0);
    if d7`in_ker then
      groups:= ImageCopies(so@factor,7,diag);
      maximals:= maximals cat groups;
    else 
      Append(~maximals, SelectGroupFromSubset(psl,so@factor,diag,d7`invol,7));
    end if;

  //and now the C9

    if d7`has_u33 then
      if Print gt 1 then "getting U3(3)"; end if;
      c9:= Getu33d7b(p);
      if d7`in_ker then
        groups:= ImageCopies(c9@factor,7,diag);
        maximals:= maximals cat groups;
      else
        grp:= SelectGroupFromSubset(psl,c9@factor,diag,d7`invol,7);
        Append(~maximals, grp);
      end if;
    end if;
  end if;

  return maximals;
end function;


/*****************************************************************/

/* The main function. 
 * Input: - a group isomorphic to an almost simple group with 
 *          socle PSL(7, p) for p prime,
 *        - the prime p;
 *        - a flag "max" (default true) to say whether we want 
 *          the maximals or just to do constructive recognition.
 *        - a Print level (default 0) if > 1 we print stuff.
 *
 * Output: - 5 things. 
 *           first is homom from standard PSL to the copy of Aut(PSL)
 *             where the maximals live.
 *           third is the maximal subgroups, 
 *           others are other maps.
 */


function L7pIdentify(group, p:  max:= true, Print:=0)
  fac:= Factorisation(p);
  assert #fac eq 1;
  assert p gt 3;
  d:= Gcd(p-1, 7);

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(7,p);
  sl := SL(7,p);
  apsl:= PGL2(7,p);
  AssertAttribute(apsl, "Order", (2*#GL(7,p) div (p-1))); 
  if Print gt 2 then "Making factor map"; end if;
  factor:= hom<gl->apsl|apsl.1, apsl.2>;
  if Print gt 2 then "Finding image of SL in perm rep"; end if;
  psl := sl @ factor;
  AssertAttribute(psl, "Order", (#SL(7,p) div Gcd(p-1,7)));

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 7, p, 1, psl, apsl, factor : Print:=0);

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psl | [ soc.i@homom : i in [1..Ngens(soc)]]>);

    if Print gt 2 then print "minimising generators"; end if; 
    //get apsl right
    ord_apsl:= Order(apsl);
    newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
    subapsl := sub< apsl | newgens >;
    RandomSchreier(subapsl);
    for g in Generators(apsl) do if not g in subapsl then
      Append(~newgens,g); subapsl := sub< apsl | newgens >;
      RandomSchreier(subapsl);
    end if; end for;
    apsl := sub<apsl|subapsl>;
    apsl`Order:= ord_apsl;

  if not max then
    return homom, apsl, [], F, phi;
  end if;

  if Print gt 1 then "Creating maximals"; end if;
  if d eq 1 then
    is_novelty, has_u33 := Deq1WhichGroup(group,p);
    if Print gt 1 then 
      "is novelty =", is_novelty, "has U_3(3) =", has_u33;
    end if; 
    maximals := Deq1Maximals(p, factor, is_novelty, has_u33, Print);
  elif d eq 7 then
    d7:= Deq7WhichGroup(group,soc,apsl,psl,p,homom);     
    if Print gt 1 then 
      "is novelty =", d7`is_novelty, "in kernel =", d7`in_kernel;
      "in stab =",d7`in_stab, "has U_3(3) =",d7`has_u33; 
    end if;
    maximals:=Deq7Maximals(p,factor,psl,d7,Print);
  end if;

  //return statement should also return F, phi when testing complete. 
  return homom, apsl, maximals, F, phi;

end function;







