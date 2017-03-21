freeze;
/*
This file contains functions called:
GetInvol(group,kernel)
Deq2WhichGroup(quot,groupquot,delta,iota,p)
Deq6WhichGroup(quot,groupquot,delta,iota,p,proj)
Deq2Maximals(p, factor,  is_novelty, has_sl211, has_sl3q, Print)
Deq6Maximals(p, factor, psl, d6, Print)
L6pIdentify(group, p)
*/

import "reds.m": SLPointStab, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
SLStabOfNSpaceMissDual, SLStabOfHalfDim;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "select_conj.m": ImageCopies, SelectGroupFromSubset;
import "tensor.m": SLTensor;
import "classicals.m" : NormOfSp, NormOfO;
import "psl2q.m": MakeHomomGeneral;
import "gl2.m": PGammaL2; 
import "construct.m": ReduceOverFiniteField;

//files from DFH - slightly modified to return functions not 
//objects.

function Getsl211d6(p)
  c9lib := GetLibraryRoot() cat "/c9lattices/";
  _LRS := Read(c9lib cat "sl211d6");
  _LR := eval _LRS;
  L:= ReduceOverFiniteField(_LR,p);
  c9:= L[1];
  //can remove this later.
  assert IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and
  IsPrimitive(c9) and (not IsTensor(c9)) and
  ClassicalForms(c9)`formType eq "linear";
  return c9;
end function;

function Get6u43d6(p)
  c9lib := GetLibraryRoot() cat "/c9lattices/";
  _LRS := Read(c9lib cat "6au43d6");
  _LR := eval _LRS;
  L:= ReduceOverFiniteField(_LR,p);
  c9:= L[1];
  //can remove this later.
  assert IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and
  IsPrimitive(c9) and (not IsTensor(c9)) and
  ClassicalForms(c9)`formType eq "linear";
  return c9;
end function;

function Get6l34d6(p)
  c9lib := GetLibraryRoot() cat "/c9lattices/";
  _LRS := Read(c9lib cat "6l34d6");
  _LR := eval _LRS;
  L:= ReduceOverFiniteField(_LR,p);
  c9:= L[1];
  //can remove this later.
  assert IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and
  IsPrimitive(c9) and (not IsTensor(c9)) and
  ClassicalForms(c9)`formType eq "linear";
  return c9;
end function;

function Get6a7d6(p)
  c9lib := GetLibraryRoot() cat "/c9lattices/";
  _LRS := Read(c9lib cat "6a7d6");
  _LR := eval _LRS;
  L:= ReduceOverFiniteField(_LR,p);
  c9:= L[1];
  //can remove this later.
  assert IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and
  IsPrimitive(c9) and (not IsTensor(c9)) and
  ClassicalForms(c9)`formType eq "linear";
  return c9;
end function;

function Get6a6d6(p)
  c9lib := GetLibraryRoot() cat "/c9lattices/";
  _LRS := Read(c9lib cat "6a6d6");
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

/* d eq 2 WhichGroup we have Out(PSL6(p)) = 2^2. 
   5 possible groups: PSL itself, PGL, PSigmaL, PSL.2_3 and Aut(PSL).
*/   

function Deq2WhichGroup(quot, groupquot, delta, iota, p)
  //first check whether subgroup of PGL
  is_novelty:= not groupquot subset sub < quot | delta >;


  if (not (p eq 11)) and IsSquare(GF(p)!(-11)) then
    has_l211:= groupquot subset sub<quot|delta*iota>;
  else
    has_l211:= false;
  end if;

  if IsSquare(GF(p)!2) then
    has_sl3q:= groupquot subset sub<quot|iota>;
  else
    has_sl3q:= groupquot subset sub<quot|delta*iota>;
  end if;

  return is_novelty, has_l211, has_sl3q;
end function;


/* d eq 6 WhichGroup we have Out(PSL6(p)) = D_{2 x 6}
*/ 

function Deq6WhichGroup(quot,groupquot,delta,iota,p,proj)

  DT:= recformat<is_novelty:Booleans(),in_kernel:Booleans(),in_sp_stab:Booleans(),
    in_ominus_stab:Booleans(),in_u43_ker:Booleans(),in_u43_stab:Booleans(),
    in_l211_ker:Booleans(),in_l211_stab:Booleans(),in_l34_ker:Booleans(),
    in_l34_stab:Booleans(),in_a7_ker:Booleans(),in_a6_stab:Booleans(),
    in_l3p_ker:Booleans(),sp_invol,omin_invol,u43_invol,
    l211_invol,l34_invol,a6_invol>; 

  d6:= rec<DT|>;

  //first check whether subgroup of PGL.
  d6`is_novelty:= not groupquot subset sub < quot | delta >;

  //action on all classical groups has same kernel.
  kernel:= sub<quot|delta^3>;
  d6`in_kernel:= groupquot subset kernel;

  //stabiliser for Sp, O+, O- (p = 3(4)) is S3 from CUP text
  d6`in_sp_stab:= exists{i : i in [0..5] |
       groupquot subset sub<quot|delta^3, iota>^(delta^i)};

  //kernel for Sp, O+, O- (p = 3(4)) is K2 from CUP text.
  if d6`in_sp_stab and not d6`in_kernel then
    d6`sp_invol := GetInvol(groupquot, kernel)@@proj;
  end if;

  d6`in_ominus_stab:= d6`in_sp_stab;
  if (p mod 4) eq 1 then
    d6`in_ominus_stab:= exists{i : i in [0..5] |
       groupquot subset sub<quot|delta^3,iota*delta>^(delta^i)};
    if d6`in_ominus_stab and not d6`in_kernel then
      d6`omin_invol:= GetInvol(groupquot, kernel)@@proj;
    end if;
  end if;

  d6`in_u43_stab:= false;
  if (p mod 12) eq 1 then
    d6`in_u43_ker:= groupquot subset sub<quot|>;
    d6`in_u43_stab:= exists{i : i in [0..5] | groupquot subset
                         sub<quot|iota>^(delta^i)};
    if d6`in_u43_stab and not d6`in_u43_ker then
      d6`u43_invol:= GetInvol(groupquot, sub<quot|>)@@proj;
    end if;
  elif (p mod 12) eq 7 then
    d6`in_u43_ker:= groupquot subset sub<quot|delta^3>;
    d6`in_u43_stab:=not((delta in groupquot) or (delta^2 in groupquot));
    if d6`in_u43_stab and not d6`in_u43_ker then
      d6`u43_invol:= GetInvol(groupquot, sub<quot|delta^3>)@@proj;
    end if;
  end if;

  d6`in_l211_stab:= false;
  if IsSquare(GF(p)!(-11)) then
    d6`in_l211_ker:= groupquot subset sub<quot|>;
    d6`in_l211_stab:= exists{i : i in [0..5] | groupquot subset 
                         sub<quot|iota*delta>^(delta^i)};
    if d6`in_l211_stab and not d6`in_l211_ker then
      d6`l211_invol:= GetInvol(groupquot, sub<quot|>)@@proj;
    end if;
  end if;

  d6`in_l34_stab:= false;
  if (p mod 24) in [1,19] then
    d6`in_l34_ker:= groupquot subset sub<quot|>;
    d6`in_l34_stab:= exists{i : i in [0..5] | groupquot subset
                         sub<quot|iota>^(delta^i)};
    if d6`in_l34_stab and not d6`in_l34_ker then
      d6`l34_invol:= GetInvol(groupquot,sub<quot|>)@@proj;
    end if;
  elif (p mod 24) in [7,13] then
    //get novelties in this case. "kernel" means find three copies
    //later and "stab" means find one copy.
    d6`in_l34_ker:= groupquot eq sub<quot|delta^3>;
    //get 1 copy if have a nontrivial group
    d6`in_l34_stab:= d6`in_l34_ker or exists{i : i in [0..5] | groupquot eq
       sub<quot|delta*iota>^(delta^i)} or #groupquot eq 4;
    if d6`in_l34_stab and not d6`in_l34_ker then
      //both delta*iota and delta^2*iota fix same group, so any involution
      // other then delta^3
      d6`l34_invol:= GetInvol(groupquot,sub<quot|delta^3>)@@proj;
    end if;
  end if;


  //6A_7. 12 classes so regular representation.
  d6`in_a7_ker:=(((p mod 24) in [1,7]) and (groupquot eq sub<quot|>));

  //6A_6. usually contained in 6A_7 but two copies novelty under
  //duality*diag. only bother defining a "stab" here as there's a unique
  //conjugacy class of subgroups where anything happens. 
  d6`in_a6_stab:= ((p mod 24) in [1,7]) and
    exists{i : i in [0..5] | groupquot eq sub<quot|delta*iota>^(delta^i)};
  if d6`in_a6_stab then
    d6`a6_invol:= GetInvol(groupquot,sub<quot|>)@@proj;
  end if;

  //And finally, L3(p). 
  d6`in_l3p_ker:= (IsSquare(GF(p)!2) and groupquot subset 
      sub<quot|delta^2, iota>) or 
  ((not IsSquare(GF(p)!2)) and groupquot subset 
      sub<quot|delta^2,delta*iota>);

  return d6;

end function;


/****************************************************************/

//This makes maximal subgroups when Gcd(p-1, 6) = 2.

function Deq2Maximals(p, factor,  is_novelty, has_sl211, has_sl3q, Print)

  //there's some weird behaviour for small fields that we can ignore. 
  assert p gt 4 and IsPrime(p);
  diag:= GL(6, p).1@factor;

  maximals:= [];
  
  if Print gt 1 then "getting reducibles"; end if;
  if not is_novelty then
    Append(~maximals,  (SLPointStab(6, p)@factor));
    for i in [2, 4, 5] do
      Append(~maximals,  (SLStabOfNSpace(6, p, i)@factor));
    end for;
  else 
    Append(~maximals, (SLStabOfNSpaceMeetDual(6, p, 1)@factor));
    Append(~maximals, (SLStabOfNSpaceMissDual(6, p, 1)@factor));
    Append(~maximals, (SLStabOfNSpaceMeetDual(6, p, 2)@factor));
    Append(~maximals, (SLStabOfNSpaceMissDual(6, p, 2)@factor));
  end if;
  Append(~maximals, SLStabOfHalfDim(6, p)@factor);

  if Print gt 1 then "getting imprimitives"; end if;
  for k in [2, 3, 6] do
    Append(~maximals, (ImprimsMeetSL(6, p, k)@factor));
  end for;
  
  if Print gt 1 then "getting superfields"; end if;
  Append(~maximals, (GammaLMeetSL(6, p, 2)@factor));
  Append(~maximals, (GammaLMeetSL(6, p, 3)@factor));

  if Print gt 1 then "getting tensor"; end if;
  //single conjugacy class
  Append(~maximals, (SLTensor(2, 3, p)@factor));

  if Print gt 1 then "getting orthogonals"; end if;
  //single conjugacy class
  soplus:= NormOfO(6, p, +1);
  sominus:= NormOfO(6, p, -1);
  Append(~maximals, soplus@factor);
  Append(~maximals, sominus@factor);

  //single conjugacy class
  if Print gt 1 then "getting symplectic"; end if;
  Append(~maximals, (NormOfSp(6, p))@factor);

  //finally the C9s.
  if has_sl211 then
    if Print gt 1 then "getting SL_2(11)"; end if;
    sl:= Getsl211d6(p);
    Append(~maximals, sl@factor);
    Append(~maximals, (sl@factor)^diag);
  end if;

  if has_sl3q then
    if Print gt 1 then "getting SL_3(p)"; end if;
    sl:= MatrixGroup(SymmetricSquare(GModule(SL(3, p))));
    assert IsAbsolutelyIrreducible(sl) and (not IsSemiLinear(sl)) and
      IsPrimitive(sl) and (not IsTensor(sl)) and
      ClassicalForms(sl)`formType eq "linear"; 
    Append(~maximals, sl@factor);
    Append(~maximals, (sl@factor)^diag);  
  end if;  


  return maximals;
end function;




/********************************************************************/
//makes maximals when (p-1, 6) = 6.
//d6 is all the data about where in the group we are, and hence what
//subgroups and conjugacy classes must be made. 
function Deq6Maximals(p, factor, psl, d6, Print)

  assert IsPrime(p);
  assert p mod 6 eq 1;
  diag:= GL(6, p).1@factor;

  maximals:= [];

  if Print gt 1 then "getting reducibles"; end if;
  if not d6`is_novelty then
    Append(~maximals,  (SLPointStab(6, p)@factor));
    Append(~maximals,  (SLStabOfNSpace(6, p, 2)@factor));
    Append(~maximals,  (SLStabOfNSpace(6, p, 4)@factor));
    Append(~maximals,  (SLStabOfNSpace(6, p, 5)@factor));
  else 
    Append(~maximals, (SLStabOfNSpaceMeetDual(6, p, 1)@factor));
    Append(~maximals, (SLStabOfNSpaceMissDual(6, p, 1)@factor));
    Append(~maximals, (SLStabOfNSpaceMeetDual(6, p, 2)@factor));
    Append(~maximals, (SLStabOfNSpaceMissDual(6, p, 2)@factor));
  end if;
  Append(~maximals, SLStabOfHalfDim(6, p)@factor);

  if Print gt 1 then "getting imprimitives"; end if;
  Append(~maximals, (ImprimsMeetSL(6, p, 6)@factor));
  Append(~maximals, (ImprimsMeetSL(6, p, 3)@factor));
  Append(~maximals, (ImprimsMeetSL(6, p, 2)@factor));

  if Print gt 1 then "getting semilinears"; end if;
  Append(~maximals, (GammaLMeetSL(6, p, 2)@factor));
  Append(~maximals, (GammaLMeetSL(6, p, 3)@factor));

  if Print gt 1 then "getting tensors"; end if;
  Append(~maximals, (SLTensor(2, 3, p))@factor);

  if Print gt 1 then "getting classical groups"; end if;
  soplus:= NormOfO(6, p, +1);
  sominus:= NormOfO(6, p, -1);
  sp:= NormOfSp(6, p);
  if d6`in_kernel then
    for grp in [soplus, sominus, sp] do
      groups:= ImageCopies(grp@factor,3,diag);
      maximals:= maximals cat groups;
    end for;
  elif d6`in_sp_stab then
    grps:= [soplus, sp];
    if (p mod 4) eq 3 then Append(~grps, sominus); end if;
    for grp in grps do
      if grp eq soplus then "getting soplus"; 
      elif grp eq sominus then "getting sominus";
      elif grp eq sp then "getting sp";
      end if;
      Append(~maximals, SelectGroupFromSubset(psl,grp@factor,diag,d6`sp_invol,3));
    end for;   
  end if;
  if ((p mod 4) eq 1) and d6`in_ominus_stab and not d6`in_kernel then
    Append(~maximals,SelectGroupFromSubset(psl,sominus@factor,diag,d6`omin_invol,3));
  end if;


  //and now the C9s. many many of them

  //first deal with U4(3). always there, tho' number of copies and
  //stabiliser depend on congruences mod 12.

  if d6`in_u43_stab then
    if Print gt 1 then "getting U4(3)"; end if;
    c9:= Get6u43d6(p);
    if d6`in_u43_ker and (p mod 12) eq 1 then
      groups:= ImageCopies(c9@factor,6,diag);
      maximals:= maximals cat groups;
    elif d6`in_u43_ker and (p mod 12) eq 7 then
      groups:= ImageCopies(c9@factor,3,diag);
      maximals:= maximals cat groups;
    elif (p mod 12) eq 1 then
      grp1:= SelectGroupFromSubset(psl,c9@factor,diag,d6`u43_invol,6);
      Append(~maximals, grp1);
      Append(~maximals, grp1^(diag^3));
    elif (p mod 12) eq 7 then
      Append(~maximals, SelectGroupFromSubset(psl,c9@factor,diag,d6`u43_invol,3));
    end if;
  end if;

  //next SL(2, 11). There when (-11) is a square in GF(p), either
  //2 or 6 copies depending on whether in kernel or stabiliser.

  if d6`in_l211_stab then
    if Print gt 1 then "getting L2(11)"; end if;
    c9:= Getsl211d6(p);
    if d6`in_l211_ker then
      groups:= ImageCopies(c9@factor, 6, diag);
      maximals:= maximals cat groups;
    else
      grp1:= SelectGroupFromSubset(psl, c9@factor, diag, d6`l2_11invol,6);
      Append(~maximals, grp1);
      Append(~maximals, grp1^(diag^3));
    end if;
  end if;

  //novelty subgroup of SL^{\pm}, SL.<delta*iota> (and its conjugates)
  //SL.<delta^3,iota> (and its conjugates) when p = 7,13(24)
  //otherwise fairly well behaved.
  if d6`in_l34_stab then   
    if Print gt 1 then "getting 6L_3(4)"; end if;
    c9:= Get6l34d6(p);
    //just testing this for now, delete later.
    assert IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and
      IsPrimitive(c9) and (not IsTensor(c9)) and
      ClassicalForms(c9)`formType eq "linear";
    if (p mod 24) in [1,19] then c:= 6; else c:= 3; end if;
    if d6`in_l34_ker then
      groups:= ImageCopies(c9@factor, c, diag);
      maximals:= maximals cat groups;
    else
      grp1:= SelectGroupFromSubset(psl,c9@factor,diag,d6`l34_invol,c);
      Append(~maximals, grp1);
      if (p mod 24) in [1,19] then 
        Append(~maximals, grp1^(diag^3));
      end if;
    end if;
  end if;

  //now 6A7. 12 classes in PSL when p = 1,7(24), otherwise none.
  if d6`in_a7_ker then
    if Print gt 1 then "getting 6A_7"; end if;
    c9:=Get6a7d6(p);
    c92:= sub<GL(6,p)|[Transpose(c9.-i) : i in [1..Ngens(c9)]]>;
    groups1:= ImageCopies(c9@factor,6,diag);
    groups2:= ImageCopies((c92@factor),6,diag);
    maximals:= maximals cat groups1 cat groups2;
  end if;

  //now 6A6, which is a novelty maximal when out is a conjugate of 
  //<iota>, and p = 1,7(24). otherwise contianed in 6A7.
  if d6`in_a6_stab then
    if Print gt 1 then "getting 6A_6"; end if;
    c9:=Get6a6d6(p);
    grp1:= SelectGroupFromSubset(psl,c9@factor,diag,d6`a6_invol,6);
    Append(~maximals, grp1);
    Append(~maximals, grp1^(diag^3));
  end if;

  if d6`in_l3p_ker then
    if Print gt 1 then "getting SL_3(p)"; end if;
    c9:= MatrixGroup(SymmetricSquare(GModule(SL(3, p))));
    //just testing this for now, delete later.
    assert IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and
      IsPrimitive(c9) and (not IsTensor(c9)) and
      ClassicalForms(c9)`formType eq "linear";
    groups:= ImageCopies(c9@factor,2,diag);
    maximals:= maximals cat groups;
  end if;

  return maximals;
end function;


/*****************************************************************/

/* The main function. 
 * Input: - a group isomorphic to an almost simple group with 
 *          socle PSL(6, p) for p prime,
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


function L6pIdentify(group, p:  max:= true, Print:=0)
  fac:= Factorisation(p);
  assert #fac eq 1;
  assert p gt 3;

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(6,p);
  sl := SL(6,p);
  apsl := PGammaL2(6,p);
  assert Ngens(apsl) eq 3;
  AssertAttribute(apsl, "Order", (2*#GL(6,p) div (p-1))); 
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;
  AssertAttribute(psl, "Order", (#SL(6,p) div Gcd(p-1,6)));


  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 6, p, 1, psl, apsl, factor : Print:=0);

  // Set up the subgroup of the outer automorphism group induced by group
  if max then
    d:= Gcd(p-1, 6);
    if Print gt 1 then "d = ", d; end if;
    quot, proj:= quo<apsl|psl>;
    delta := proj(apsl.1); assert Order(delta) eq d; //diagonal aut.
    iota := proj(apsl.3); assert Order(iota) eq 2;   //graph aut
    newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
    groupquot := sub< quot | [proj(g) : g in newgens] >; 
    if Print gt 1 then "Out aut group is", ChiefFactors(groupquot); end if;
  end if;

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

  if d eq 2 then
    is_novelty, has_sl211, has_sl3q :=
       Deq2WhichGroup(quot,groupquot,delta, iota, p);
    if Print gt 1 then 
      "is novelty =", is_novelty, "has_sl211 =", has_sl211,
      "has_sl3q=", has_sl3q; 
    end if; 
    maximals := Deq2Maximals(p, factor, is_novelty, has_sl211,
    has_sl3q, Print);
  elif d eq 6 then
    d6:= Deq6WhichGroup(quot,groupquot,delta,iota,p, proj);
    if Print gt 1 then 
      "is novelty =", d6`is_novelty, "in kernel =", d6`in_kernel;
      "in sp stab =",d6`in_sp_stab, "in ominus stab =",d6`in_ominus_stab; 
      "in U_4(3) stab =", d6`in_u43_stab, "in SL_2(11) stab =",d6`in_l211_stab;
      "in L_3(4) stab =", d6`in_l34_stab, "in A_7 ker =",d6`in_a7_ker;
      "in A_6 stab =",d6`in_a6_stab,"in SL(3,p) ker =",d6`in_l3p_ker;
    end if;
    maximals:=Deq6Maximals(p,factor,psl,d6,Print);
  end if;

  return homom, apsl, maximals, F, phi;

end function;







