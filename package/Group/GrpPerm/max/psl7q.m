freeze;
/*
This file contains functions called:
GetInvol(group,kernel)
Deq1WhichGroup(quot, groupquot, delta, phi)
Deq7WhichGroup(quot, groupquot, delta, phi, iota,p,e)
Deq1Maximals(p,e,factor,d7, Print)
Deq7Maximals(p,e,factor, psl, d7, Print)
L7qIdentify(group, q)
*/

import "reds.m": SLPointStab, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
SLStabOfNSpaceMissDual, SLStabOfHalfDim;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "normes.m":NormaliserOfExtraSpecialGroup;
import "select_conj.m": ImageCopies, SelectGroupFromSubset;
import "subfield.m" : SubfieldSL;
import "classicals.m" : NormOfSp, NormOfO, NormOfSU;
import "psl2q.m": MakeHomomGeneral;
import "gl2.m": PGammaL2;

DT:= recformat<is_novelty:Booleans(),in_ker:Booleans(),
      in_stab:Booleans(),has_c6:Booleans(),invol>; 

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
/* d eq 1 WhichGroup we have Out(PSL7(p^e)) = 2 x e. 
 */   

function Deq1WhichGroup(quot, groupquot, delta, phi)

  d7:= rec<DT|>;

  //check whether PSL, else novelty C1s
  d7`is_novelty:= not groupquot subset sub < quot | delta, phi >;
 
  return d7;
end function;


/* d eq 7 WhichGroup we have Out(PSL7(p^e)) = 7:e:2
 */ 

function Deq7WhichGroup(quot,groupquot,delta,phi,iota,proj,p,e)

  d7:= rec<DT|>;
 
  //first check for novelty reducibles
  d7`is_novelty:= not (groupquot subset sub<quot|delta,phi>);
    
  //for all irred geometric groups we get the same stabiliser and kernel
  //when there's 7 of them.
  d7`in_stab:= exists{i : i in [0..6] | groupquot subset 
     sub<quot|delta^7,phi,iota>^(delta^i)};
  if d7`in_stab then
    if (p mod 7) eq 1 then 
      ker:= sub<quot|delta^7, phi>;
    elif (p mod 7) in [2,4] then
      ker:= sub<quot|delta^7, phi^3>;
    elif (p mod 7) in [3,5] then
      ker:= sub<quot|delta^7, phi^6, iota*phi^3>;
    else
      assert (p mod 7) eq 6;
      ker:= sub<quot|delta^7,phi^2,iota^phi>;
    end if;
    d7`in_ker:= groupquot subset ker;
    if not d7`in_ker then
      d7`invol:= GetInvol(groupquot, ker)@@proj;
    end if;
  end if;

  //e must be odd and minimal subject to 7|(p^e-1),so e = 3.
  if (e eq 3) and ((p mod 7) in [2,4])  then 
    d7`has_c6:= true;
  end if;

  return d7;

end function;


/****************************************************************/

//This makes maximal subgroups when Gcd(q-1, 7) = 1.

function Deq1Maximals(p,e,factor,d7, Print)

  q:= p^e;

  diag:= GL(7, q).1@factor;

  maximals:= [];
  
  //1 conjugacy class of subfield for each prime divisor of e.
  if Print gt 1 then "getting subfields"; end if;
  fac_e:= Factorisation(e);
  for d in fac_e do
    f:= e div d[1];
    Append(~maximals, SubfieldSL(7, p, e, f)@factor);
  end for;     

  if IsOdd(q) then
    if Print gt 1 then "getting orthogonal"; end if;
    so:= NormOfO(7, q, 0);
    Append(~maximals, so@factor);
  end if; 

  if IsEven(e) then 
    if Print gt 1 then "getting unitary"; end if;
    half:= e div 2;
    su:= NormOfSU(7, p^half);
    Append(~maximals, su@factor);
  end if;

  return maximals;
end function;


/********************************************************************/
//makes maximals when (q-1, 7) = 7.
function Deq7Maximals(p,e,factor, psl, d7, Print)

  q:= p^e;
  diag:= GL(7, q).1@factor;

  maximals:= [];

  //first the subfield groups
  if Print gt 1 then "getting subfields"; end if;
  fac_e:= Factorisation(e);
  for d in fac_e do
    f:= e div d[1];
    copies:= ((q-1) div Lcm(p^f-1, (q-1) div 7));
    assert copies in [1,7];
    if copies eq 1 or d7`in_stab then
      subf:= SubfieldSL(7, p, e, f)@factor;  
      if copies eq 1 then 
        Append(~maximals, subf);
      elif d7`in_ker then
        grps:= ImageCopies(subf,7,diag);
      else
        Append(~maximals,SelectGroupFromSubset(psl,subf,diag,d7`invol,7));
      end if;
    end if;
  end for;     

  //now the extraspecial normalisers.
  if d7`has_c6 and d7`in_stab then
    if Print gt 1 then "getting extraspecial groups"; end if;
    ext:= NormaliserOfExtraSpecialGroup(7, q);
    ext1:= sub<ext|[ext.i : i in [1..Ngens(ext)] | Determinant(ext.i)
      eq 1]>@factor;
    if d7`in_ker then
      groups:= ImageCopies(ext1,7,diag);
      maximals:= maximals cat groups;
    else
      Append(~maximals,SelectGroupFromSubset(psl,ext1,diag,d7`invol,7));
    end if;
  end if;

  if d7`in_stab and IsOdd(q) then
    if Print gt 1 then "getting orthogonal groups"; end if;
    so:= NormOfO(7, q, 0)@factor;
    if d7`in_ker then
      groups:= ImageCopies(so,7,diag);
      maximals:= maximals cat groups;
    else 
      Append(~maximals, SelectGroupFromSubset(psl,so,diag,d7`invol,7));
    end if;
  end if;

  if IsEven(e) then
    half:= e div 2;
    su_copies:= (q-1) div Lcm((p^half) +1, (q-1) div 7);
    assert su_copies in [1,7];
    if su_copies eq 1 or d7`in_stab then
      if Print gt 1 then "getting unitary group"; end if;
      su:= NormOfSU(7,p^half)@factor;
      if su_copies eq 1 then
        Append(~maximals, su);
      elif d7`in_ker then
        groups:= ImageCopies(su,7,diag);
      else
        Append(~maximals, SelectGroupFromSubset(psl,su,diag,d7`invol,7));  
      end if;
    end if;
  end if;

  return maximals;
end function;


/*****************************************************************/

/* The main function. 
 * Input: - a group isomorphic to an almost simple group with 
 *          socle PSL(7, q) for q prime power,
 *        - the prime power q;
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


function L7qIdentify(group, q:  max:= true, Print:=0)
  fac:= Factorisation(q);
  assert #fac eq 1;
  e:= fac[1][2];
  assert e gt 1;
  p:= fac[1][1];
  assert q gt 3;
  d:= Gcd(q-1, 7);

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(7,q);
  sl := SL(7,q);
  apsl:= PGammaL2(7,q);
  AssertAttribute(apsl, "Order", (2*e*#GL(7,q) div (q-1))); 
  if Print gt 2 then "Making factor map"; end if;
  factor:= hom<gl->apsl|apsl.1, apsl.2>;
  if Print gt 2 then "Finding image of SL in perm rep"; end if;
  psl := sl @ factor;
  AssertAttribute(psl, "Order", (#SL(7,q) div Gcd(q-1,7)));

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 7, p, e, psl, apsl, factor : Print:=0);
  
  // Set up the subgroup of the outer automorphism group induced by group
  if max then
    if Print gt 1 then "d = ", d; end if;
    quot, proj:= quo<apsl|psl>;
    delta := proj(apsl.1); assert Order(delta) eq d; //diagonal aut.
    phia:= proj(apsl.3); assert Order(phia) eq e; //field aut
    iota := proj(apsl.4); assert Order(iota) eq 2;   //graph aut
    newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
    groupquot := sub< quot | [proj(g) : g in newgens] >; 
    if Print gt 1 then "Out aut group is", ChiefFactors(groupquot); end if;
  end if;

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psl | [ soc.i@homom : i in [1..Ngens(soc)]]>);

  //this restriction also in for testing purposes
  if Print gt 2 then print "minimising generators"; end if; 
  //get apsl right
  ord_apsl:= Order(apsl);
  newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
  subapsl := sub< apsl | newgens >;
  RandomSchreier(subapsl);
  for g in Generators(apsl) do 
    if not g in subapsl then
      Append(~newgens,g); 
      subapsl := sub< apsl | newgens >;
      RandomSchreier(subapsl);
    end if; 
  end for;
  apsl := sub<apsl|subapsl>;
  apsl`Order:= ord_apsl;

  if not max then
    return homom, apsl, [], F, phi;
  end if;

  if Print gt 1 then "Creating maximals"; end if;
  if d eq 1 then
    d7 := Deq1WhichGroup(quot, groupquot, delta, phia);
  elif d eq 7 then
    d7:= Deq7WhichGroup(quot, groupquot, delta, phia, iota,proj,p,e);
  end if;
  
  maximals:= [];

  if Print gt 1 then "getting reducibles"; end if;
  if not d7`is_novelty then
    Append(~maximals,  (SLPointStab(7, q)@factor));
    for i in [2..6] do
      Append(~maximals,  (SLStabOfNSpace(7, q, i)@factor));
    end for;
  else 
    for i in [1..3] do
      Append(~maximals, (SLStabOfNSpaceMeetDual(7, q, i)@factor));
      Append(~maximals, (SLStabOfNSpaceMissDual(7, q, i)@factor));
    end for;
  end if;

  if q gt 4 then
    if Print gt 1 then "getting imprimitives"; end if;
    Append(~maximals, (ImprimsMeetSL(7, q, 7)@factor));
  end if;
  
  if Print gt 1 then "getting semilinears"; end if;
  Append(~maximals, (GammaLMeetSL(7, q, 7)@factor));

  //now we make the maximals that depend on congruences of q.
  if d eq 1 then
    maximals:= maximals cat Deq1Maximals(p,e,factor,d7,Print);
  elif d eq 7 then
    maximals:= maximals cat Deq7Maximals(p,e,factor,psl,d7,Print);
  end if;

  return homom, apsl, maximals, F, phi;

end function;
