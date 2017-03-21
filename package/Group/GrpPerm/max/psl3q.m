freeze;
 
/*
 * This file will contain the functions to construct the maximal
 * subgroups of any almost simple group $G$ with $PSL(3, p^e) < G <
 * PGammaL2(3, p^e), with $e>2$. 
 */

/* 
function names in this file:
L3qReducts(q, is_novelty)
SubfieldSL(p, e, f)
NonCoprimeWhichGroup(group, p, e)
CoprimeMaximals(group, p, e)
NonCoprimeMaximals(group, p, e)
L3qMaximals(group, q)
*/

import "gl2.m": PGammaL2;
import "reds.m": SLPointStab, SLStabOfNSpace,
                 SLPointMeetHyperplane, SLPointUnmeetHyperplane;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "select_conj.m": ImageCopies, SelectGroupGeneral;
import "psl2q.m": MakeHomomGeneral;
import "subfield.m": SubfieldSL;

/******************************************************************/

function L3qReducts(q, is_novelty)
  groups:= [];
  if not is_novelty then
    Append(~groups,  SLPointStab(3, q));
    Append(~groups,  SLStabOfNSpace(3, q, 2));
  else 
    Append(~groups, SLPointMeetHyperplane(3, q));
    Append(~groups, SLPointUnmeetHyperplane(3, q));
  end if;
  return groups;
end function;

/*****************************************************************/

function CoprimeMaximals(soc, group, p, e, factor, Print)
  assert Gcd(p^e-1, 3) eq 1;

  soc:= Socle(group);
  out:= #group div (#PSL(3, p^e));

  if Print  gt 1 then "getting reducibles"; end if;
  reducts:= L3qReducts(p^e, IsEven(out));
  maximals:= [x@factor : x in reducts];
  if Print  gt 1 then "getting imprimitives"; end if;
  Append(~maximals, ImprimsMeetSL(3, p^e, 3)@factor);
  if Print  gt 1 then "getting superfields"; end if;
  Append(~maximals, GammaLMeetSL(3, p^e, 3)@factor);

  if Print  gt 1 then "getting subfields"; end if;
  indices:= Factorisation(e);
  for x in indices do
    f:= e div x[1];
    subf:= SubfieldSL(3, p, e, f);
    Append(~maximals, subf@factor);
  end for;
  
  if not IsEven(p) then  
    if Print  gt 1 then "getting orthogonal group"; end if;
    grp := SO(3, p^e);
    Append(~maximals, grp@factor);
  end if;

  if IsEven(e) then
    if Print  gt 1 then "getting unitary group"; end if;
    assert p eq 3;
    f:= e div 2;
    Append(~maximals, SU(3, p^f)@factor);
  end if;
  
  //no alt_6 as either p=3 or e is odd.
 
  return maximals;
end function;    

/***************************************************************/

function NonCoprimeMaximals(group, psl, homom, p, e, factor, Print)
  local apsl;
  assert IsPrime(p);
  assert e gt 2;
  assert Gcd(p^e -1, 3) eq 3; //else are coprime. 

  diag:= GL(3, p^e).1 @ factor;

//We now set 3 variables, which determine the types of maximal subgroups:
//1. A boolean novelty which is true if G/PSL \not\leq <\delta, \phi> and is
//   false otherwise. i.e. it's true if there's novelty reducible
//   subgroups.
//2. A number nmr_copies 0, 1, 3 which is:
//     3 if G/PSL \leq conjugate of <\phi> and p = 1(3).
//       if G/PSL \leq conjugate of <\phi^2, \phi\iota> and p = 2(3).
//     1 if G/PSL \leq conjugate of <\phi, \iota> and previous 2 cases are
//       false.
//     0 otherwise.
//This number is the number of copies of various subgroups that need
//to be created. 
//3. If nmr_copies = 1 then we're going to need the outer
//involution invol to feed to SelectGroupGeneral.

  if Print gt 1 then print "Identifying group"; end if;
  apsl := PGammaL2(3,p^e);
  quot, proj := quo<apsl|psl>;
  delta := proj(apsl.1); assert Order(delta) eq 3; //diagonal aut.
  phi := proj(apsl.3); assert Order(phi) eq e;   //field aut.
  iota := proj(apsl.4); assert Order(iota) eq 2;   //graph aut
  newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
  groupquot := sub< quot | [proj(g) : g in newgens] >;
  image := Image(homom);

  novelty := not groupquot subset sub < quot | delta, phi >;
  if delta in sub< quot | groupquot, phi^2 > then nmr_copies := 0;
  else
    comsub :=  sub < quot | phi^2, delta >;
    ngq := sub < quot | comsub, groupquot >;
    if p mod 3 eq 1 and ngq subset sub < quot | delta, phi > then
       nmr_copies := 3;
    elif p mod 3 eq 2 and ngq subset sub < quot | delta, phi^2, phi*iota > then
       nmr_copies := 3;
    else
       nmr_copies := 1;
       // have to choose outer involution carefully
       invol := Random(image);
       if Index(ngq,comsub) eq 2 then
         while proj(invol) in comsub do invol := Random(image); end while;
       else
         while not proj(invol)*iota in comsub do invol := Random(image);
         end while;
       end if;
    end if;
  end if;

  //print novelty, nmr_copies, #apsl;

  if Print  gt 1 then "getting reducibles"; end if;
  reducts:=  L3qReducts(p^e, novelty);
  maximals:= [x@factor : x in reducts];
  if Print  gt 1 then "getting imprimitives"; end if;
  Append(~maximals, ImprimsMeetSL(3, p^e, 3)@factor);
  if Print  gt 1 then "getting superfields"; end if;
  Append(~maximals, GammaLMeetSL(3, p^e, 3)@factor);

  if Print  gt 1 then "getting subfields"; end if;
  indices:= Factorisation(e);
  for x in indices do
    f:= e div x[1];
    cop:= (Gcd(x[1], 3)*3) div Gcd(p^f-1, 3);
    if not (cop eq 3 and nmr_copies eq 0) then
      subf:= SubfieldSL(3, p, e, f) @ factor;
      if cop eq 1 then
        Append(~maximals, subf);
      elif nmr_copies eq 3 then 
        subf:= ImageCopies(subf,3,diag);
        maximals:= maximals cat subf;
      else //we have to select one copy out of the three
        assert nmr_copies eq 1;
        subf:= SelectGroupGeneral(psl,subf,diag,invol);
        Append(~maximals, subf);
      end if;
    end if;
  end for;

  if nmr_copies eq 1 and IsOdd(p) then
    if Print  gt 1 then "getting orthogonal group"; end if;
    so:= SelectGroupGeneral(psl,SO(3, p^e)@factor,diag,invol);
    Append(~maximals, so);
  elif nmr_copies eq 3 and IsOdd(p) then
    if Print  gt 1 then "getting orthogonal groups"; end if;
    so:= ImageCopies(SO(3, p^e)@factor,3,diag);
    Append(~maximals, so@homom);
  end if;

  if IsEven(e) then
    max_su:= Gcd(p^(e div 2)-1, 3);
    if max_su eq 1 then
      if Print  gt 1 then "getting unitary group"; end if;
      Append(~maximals, SU(3, p^(e div 2))@factor);
    else
      assert max_su eq 3;
      if nmr_copies eq 1 then
        if Print  gt 1 then "getting unitary group using select group"; end if;
      su:= SelectGroupGeneral(psl,SU(3,p^(e div 2))@factor,diag,invol);
        Append(~maximals, su);
      elif nmr_copies eq 3 then
        if Print  gt 1 then "getting unitary groups"; end if;
        su:= ImageCopies(SU(3, p^(e div 2))@factor,3,diag);
        maximals:= maximals cat su;
      end if;
    end if;
  end if;
  //no alt_6.
  return  maximals;
end function;

/*****************************************************************/

function L3qIdentify(group, q:  max:= true, Print:=0)

  fac:= Factorisation(q);
  p:= fac[1][1]; e:= fac[1][2];
  assert e gt 2;

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(3,p^e);
  sl := SL(3,p^e);
  apsl := PGammaL2(3,p^e);
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;
  psl`Order := SimpleGroupOrder(<1, 2, q>);

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 3, p, e, psl, apsl, factor : Print:=0);

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psl | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);

  //get apsl right
  newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
  subapsl := sub< apsl | newgens >; 
  RandomSchreier(subapsl);
  for g in Generators(apsl) do if not g in subapsl then
     Append(~newgens,g); subapsl := sub< apsl | newgens >;
     RandomSchreier(subapsl);
  end if; end for;
  apsl := subapsl;

  if not max then
    return homom, apsl, [], F, phi;
  end if;

  d:= Gcd(q-1, 3);
  if d eq 1 then
    if Print gt 1 then "coprime case"; end if;
    maximals := CoprimeMaximals(soc, group, p, e, factor, Print);
  else
    if Print gt 1 then "non coprime case"; end if;
    maximals :=
         NonCoprimeMaximals(group, psl, homom, p, e, factor, Print);
  end if;

  return homom, apsl, maximals, F, phi;

end function;
