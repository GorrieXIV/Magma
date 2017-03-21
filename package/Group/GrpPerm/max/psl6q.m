freeze;
/*
This file contains functions called:
GetInvol(group,kernel)
GetEltOrder6(group,kernel)
Deq1WhichGroup(quot, groupquot, delta, phi, iota, e)
Deq2WhichGroup(quot, groupquot, delta,phi, iota, p,e)
Deq3WhichGroup(quot, groupquot,delta,phi,iota,e,proj)
Deq6WhichGroup(quot,groupquot,delta,phi,iota,p,e,proj)
Deq1Maximals(q, factor, d6, Print)
Deq2Maximals(q, factor, d6, Print)
Deq3Maximals(q, factor, psl, d6, Print)
Deq6Maximals(q, factor, psl, d6, Print)
L6qIdentify(group, q)
*/

import "reds.m": SLPointStab, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
SLStabOfNSpaceMissDual, SLStabOfHalfDim;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "select_conj.m": ImageCopies, SelectGroupFromSubset;
import "tensor.m": SLTensor;
import "subfield.m": SubfieldSL;
import "classicals.m" : NormOfSp, NormOfO, NormOfSU;
import "psl2q.m": MakeHomomGeneral;
import "gl2.m": PGammaL2; 
import "construct.m": ReduceOverFiniteField;

//files from DFH - slightly modified to return functions not 
//objects.
/*
load "~colva/maximals/code/construct.m";
load "~colva/maximals/code/psl6p/6a7d6";
load "~colva/maximals/code/psl6p/6a6d6";
*/

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



DT:= recformat<is_novelty:Booleans(),in_subfield_stab:Booleans(),
     in_ceq2_ker:Booleans(),in_ceq3_ker:Booleans(),in_ceq3_stab:Booleans(),
     in_ceq6_ker:Booleans(),in_ceq6_stab:Booleans(), 
     in_sp_ker:Booleans(),in_sp_stab:Booleans(),in_ominus_stab:Booleans(),
     in_a7_ker:Booleans(),in_a7_stab:Booleans(),in_a6_stab:Booleans(),
     in_l3q_ker:Booleans(),
     ceq3_invol,ceq6_invol,sp_invol,ominus_invol,a7_invol,a7_elt,a6_invol>; 

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

//this one will be used with quot not groupquot, as need something to 
//get us between the two sets of 6A7s, each of size 6, so we can find
//the 4 to normalise. 

function GetEltOrder6(group, kernel)
  elt:= Random(group);
  while (elt in kernel) or (not (Order(elt) eq 6)) do
    elt:= Random(group);
  end while;
  return elt;
end function;


/****************************************************************/

/*
 * When (q-1, 6) = 1 we have Out(PSL(6, p^e)) = e x 2.
 * We have p = 2 and e is odd.
 */

function Deq1WhichGroup(quot, groupquot, delta, phi, iota, e)

  //only get into this case with odd powers of 2.
  assert IsOdd(e) and e gt 1;

  d6:= rec<DT|>;

  //only need to check whether subgroup of PGammaL
  d6`is_novelty:= not groupquot subset sub < quot | delta, phi >;
  return d6;

end function;

/* When (p^e-1, 6) = 2 we have Out(PSL6(p^e)) = (2^2 x e), where e is odd
 * OR p = 3.
 */   

function Deq2WhichGroup(quot, groupquot, delta,phi, iota, p,e)

  q:= p^e;
  d6:= rec<DT|>;

  //first check whether subgroup of PGammaL
  d6`is_novelty:= not groupquot subset sub < quot | delta, phi >;

  //then check whether in stabiliser of any subfield groups
  d6`in_subfield_stab:= groupquot subset sub<quot|phi,iota>;

  d6`in_l3q_ker:= (IsSquare(GF(q)!2) and groupquot subset
  sub<quot|iota,phi>) or ((not IsSquare(GF(q)!2)) and groupquot subset
  sub<quot|delta*iota,phi>);

  return d6;
end function;

/* When (p^e-1, 6) = 3 we have p = 2 and e even, so 
 * Out(PSL(6, 2^e)) = 3:(e x 2)
 */

function Deq3WhichGroup(quot, groupquot,delta,phi,iota,e,proj)

  //only get into this case with even powers of 2
  assert IsEven(e);

  d6:= rec<DT|>;

  //first check whether subgroup of PGammaL
  d6`is_novelty:= not groupquot subset sub < quot | delta, phi >;

  //now sort out conjugacy of subfield and classical groups
  d6`in_sp_stab:= exists{i : i in [0..2] | groupquot subset
      sub<quot|phi, iota>^(delta^i)};
 
  kernel:= sub<quot|phi^2, iota*phi>;
  assert IsNormal(quot, kernel);

  //kernel is a normal subgroup!
  d6`in_sp_ker:= groupquot subset kernel;    

  if d6`in_sp_stab and not d6`in_sp_ker then
    d6`sp_invol:= GetInvol(groupquot, kernel)@@proj;
  end if;

  return d6;
end function;


/* When (p^e-1, 6) = 6 we have Out(PSL6(p)) = 6:e:2
 */ 

function Deq6WhichGroup(quot,groupquot,delta,phi,iota,p,e,proj)

  q:= p^e;

  d6:= rec<DT|>;
  
  //first check whether subgroup of PGammaL.
  d6`is_novelty:= not groupquot subset sub < quot | delta,phi >;

  //now need to do subfield and unitary groups. we need different stabilisers 
  //depending on how many classes.
  //stabiliser is S3 from CUP text, but that depends on number of 
  //classes. kernel is K1 (p = -1 (mod #classes)) or K2 (otherwise).
  //number of classes could be 1 (in which case nothing to do), 
  //or 2 or 3 or 6 (not sure if this last case can happen, but do it
  //anyway). if number of classes is 3 or 6 we need an outer
  //involution.  
  d6`in_ceq2_ker:= groupquot subset sub<quot|delta^2, phi, iota>;
  d6`in_ceq3_stab:= exists{i : i in [0..5] | groupquot subset
       sub<quot|delta^3, phi, iota>^(delta^i)};
  if d6`in_ceq3_stab then
    if (p mod 3) eq 1 then
      kernel:= sub<quot|delta^3, phi>;
    else
      assert (p mod 3) eq 2;
      kernel:= sub<quot|delta^3, phi^2, iota*phi>;
    end if;
    d6`in_ceq3_ker:= groupquot subset kernel;
    if not d6`in_ceq3_ker then
      d6`ceq3_invol:= GetInvol(groupquot, kernel);
    end if;
  end if;

  d6`in_ceq6_stab:= exists{i : i in [0..5] | groupquot subset
       sub<quot|delta^6, phi, iota>^(delta^i)};
  if d6`in_ceq6_stab then
    if (p mod 6) eq 1 then
      kernel:= sub<quot|delta^6, phi>;
    else
      assert (p mod 6) eq 5;
      kernel:= sub<quot|delta^6, phi^2, iota*phi>;
    end if;
    d6`in_ceq6_ker:= groupquot subset kernel;
    if not d6`in_ceq6_ker then
      d6`ceq6_invol:= GetInvol(groupquot, kernel);
    end if;
  end if;

  //stabiliser for Sp, O+, O- (q = 3(4)) is S3 from CUP text
  d6`in_sp_stab:= exists{i : i in [0..5] |
       groupquot subset sub<quot|delta^3,phi, iota>^(delta^i)};

  //kernel for Sp, O+, O- (q = 3(4)) is K2 from CUP text when p = 1(3)
  if d6`in_sp_stab and (p mod 3) eq 1 then
    kernel:= sub<quot|delta^3, phi>;
  //kernel for Sp, O+, O-(q = 3(4)) is K3 from CUP text when p = 2(3)
  elif d6`in_sp_stab and (p mod 3) eq 2 then
    kernel:= sub<quot|delta^3, phi^2,iota*phi>;  
  end if;
  d6`in_sp_ker:= groupquot subset kernel;
  if d6`in_sp_stab and not d6`in_sp_ker then 
    d6`sp_invol := GetInvol(groupquot, kernel)@@proj;
  end if;

  if q mod 4 eq 3 then
    d6`in_ominus_stab:= d6`in_sp_stab;
    d6`in_ominus_ker:= d6`in_sp_ker;
    if d6`in_ominus_stab and not d6`in_ominus_ker then
      d6`ominus_invol:= d6`sp_invol;
    end if;
  else
    //kernel S4 from CUP text
    d6`in_ominus_stab:= exists{i : i in [0..5] |
       groupquot subset sub<quot|delta^3,phi*delta^((p-1) div 2), 
                                            iota*delta^-1>^(delta^i)};
    if p mod 3 eq 1 then
      kernel:= sub<quot|delta^3, phi*delta^((p-1) div 2)>;
    else
      kernel:= sub<quot|delta^3, phi^2, iota*phi>;
    end if;
    d6`in_ominus_ker:= groupquot subset kernel;
    if d6`in_ominus_stab and not d6`in_ominus_ker then
      d6`ominus_invol:= GetInvol(groupquot, kernel)@@proj;
    end if;
  end if;

  //6A_7.
  if ((p mod 24) in [5,11,13,19]) and (e eq 2) then
    if (p mod 6) eq 1 then
      d6`in_a7_stab:= exists{i : i in [0..5] | groupquot subset
         sub<quot|phi*iota>^delta^i};
    elif (p mod 6) eq 5 then
      d6`in_a7_stab:= exists{i : i in [0..5] | groupquot subset
         sub<quot|phi>^delta^i};
    end if;
    d6`in_a7_ker:= groupquot eq sub<quot|>;
    if d6`in_a7_stab and not d6`in_a7_ker then
       d6`a7_invol:= GetInvol(groupquot, sub<quot|>)@@proj;
       d6`a7_elt:= GetEltOrder6(groupquot,sub<groupquot|delta>)@@proj;
    end if;
  end if;

  //6A_6. usually contained in 6A_7 but two copies novelty under
  //duality. only bother defining a "stab" here as there's a unique
  //conjugacy class of subgroups where anything happens. 
  if ((p mod 24) in [5, 11, 13, 19]) and (e eq 2) then
    if (p mod 6) eq 1 then 
       d6`in_a6_stab:= exists{i : i in [0..5] | 
               groupquot eq sub<quot|phi>^(delta^i)};
    elif (p mod 6) eq 5 then
       d6`in_a6_stab:= exists{i : i in [0..5]| groupquot eq
               sub<quot|phi*iota>^(delta^i)};
    end if;
    if d6`in_a6_stab then
      d6`a6_invol:= GetInvol(groupquot,sub<quot|>)@@proj;
    end if;
  end if;

  //And finally, L3(q). 
  d6`in_l3q_ker:= (IsSquare(GF(q)!2) and groupquot subset 
   sub<quot|delta^2,phi, iota>) or 
  ((not IsSquare(GF(p)!2)) and groupquot subset 
   sub<quot|delta^2,phi,delta*iota>);

  return d6;

end function;

//end of the functions to determine which conjugacy classes must
//be constructed.
/******************************************************************/
//beginning of the functions that make the maximals whose 
//existence/conjugacy depends on congruence of q mod 6.

//makes remaining maximal subgroups when (q-1, 6)=1;

function Deq1Maximals(q, factor, d6, Print)

  assert IsEven(q);
  assert q gt 4;
  fac:= Factorisation(q);
  assert #fac eq 1;
  p:= fac[1][1]; assert p eq 2;
  e:= fac[1][2]; assert IsOdd(e);
  diag:= GL(6, q).1@factor;

  maximals:= [];
  
  //single conjugacy class of subfields for each prime divisor of 
  //e.
  if Print gt 1 then "getting subfields"; end if;
  fac_e:= Factorisation(e);
  for d in fac_e do
    f:= e div d[1];
    Append(~maximals, SubfieldSL(6, 2, e, f)@factor);
  end for;     

  //single conjugacy class of symplectics
  if Print gt 1 then "getting symplectic"; end if;
  Append(~maximals, NormOfSp(6, q)@factor);

  //no unitary groups as e odd.
  //no C9s

  return maximals;
end function;


/****************************************************************/

//This makes maximal subgroups when Gcd(p-1, 6) = 2.

function Deq2Maximals(q, factor, d6, Print)

  fac:= Factorisation(q);
  assert #fac eq 1;
  p:= fac[1][1]; assert IsOdd(p);
  e:= fac[1][2]; assert (IsOdd(e) or p eq 3);
  diag:= GL(6, q).1@factor;

  maximals:= [];
    
  if Print gt 1 then "getting subfields"; end if;
  fac_e:= Factorisation(e);
  for d in fac_e do
    f:= e div d[1];
    copies:= Gcd(6, (q-1) div (p^f-1));
    subfield:=  SubfieldSL(6, p, e, f);
    if copies eq 1 then 
      Append(~maximals, subfield@factor);
    else
      assert copies eq 2;
      if d6`in_subfield_stab then
        groups:= ImageCopies(subfield@factor,2,diag);
        maximals:= maximals cat groups;
      end if;
    end if;
  end for;     


  if Print gt 1 then "getting orthogonals"; end if;
  //single conjugacy class
  soplus:= NormOfO(6, q, +1);
  Append(~maximals, soplus@factor);
  sominus:= NormOfO(6, q, -1);
  Append(~maximals, sominus@factor);

  //single conjugacy class
  if Print gt 1 then "getting symplectic"; end if;
  Append(~maximals, NormOfSp(6, q)@factor);

  //get one unitary group when p = 3 (so e might be even)
  if IsEven(e) and d6`in_subfield_stab then
    if Print gt 1 then "getting SU_3(q)"; end if;
    half:= e div 2;
    su:= NormOfSU(6, p^half)@factor;
    groups:= ImageCopies(su,2,diag);
    maximals:= maximals cat groups;
  end if;

  if d6`in_l3q_ker then
    if Print gt 1 then "getting SL_3(q)"; end if;
    sl:= MatrixGroup(SymmetricSquare(GModule(SL(3, q))));
    assert IsAbsolutelyIrreducible(sl) and (not IsSemiLinear(sl)) and
      IsPrimitive(sl) and (not IsTensor(sl)) and
      ClassicalForms(sl)`formType eq "linear"; 
    Append(~maximals, sl@factor);
    Append(~maximals, (sl@factor)^diag);  
  end if;

  return maximals;
end function;

/****************************************************************/

//This makes maximal subgroups when Gcd(q-1, 6) = 3.

function Deq3Maximals(q, factor, psl, d6, Print)

  fac:= Factorisation(q);
  assert #fac eq 1;
  p:= fac[1][1]; assert p eq 2; 
  e:= fac[1][2]; assert IsEven(e);
  diag:= GL(6, q).1@factor;

  maximals:= [];
  
  //first the subfields. number of classes depends on divisor of 
  //e.
  if Print gt 1 then "getting subfields"; end if;
  fac_e:= Factorisation(e);
  for d in fac_e do
    f:= e div d[1];
    copies:= Gcd(6, (2^e-1) div (2^f-1));
    subfield:=  SubfieldSL(6, 2, e, f);
    if copies eq 1 then 
      Append(~maximals, subfield@factor);
    else
      assert copies eq 3;
      if d6`in_sp_ker then
        groups:= ImageCopies(subfield@factor,3,diag);
        maximals:= maximals cat groups;
      elif d6`in_sp_stab then
        Append(~maximals, SelectGroupFromSubset(psl,subfield@factor,
                  diag,d6`sp_invol,3));
      end if;
    end if;
  end for;     

  if d6`in_sp_stab then
    if Print gt 1 then "getting symplectic"; end if;
    grp:= NormOfSp(6, q)@factor;
    if d6`in_sp_ker then
      groups:= ImageCopies(grp,3,diag);
      maximals:= maximals cat groups;
    else
      Append(~maximals,SelectGroupFromSubset(psl,grp,diag,
                                                d6`sp_invol,3));
    end if;
  end if;

  half:= e div 2;
  //if half is odd then single copy of unitary, else 3.
  if IsOdd(half) then
    if Print gt 1 then "getting unitary"; end if;
    Append(~maximals, NormOfSU(6, 2^half)@factor);
  elif d6`in_sp_stab then
    if Print gt 1 then "getting unitary"; end if;
    su:= NormOfSU(6, 2^half)@factor;
    if d6`in_sp_ker then 
      groups:= ImageCopies(su,3,diag);
      maximals:= maximals cat groups;
    else
      Append(~maximals,SelectGroupFromSubset(psl,su,diag,d6`sp_invol,3));
    end if;
  end if;
      
  return maximals;
end function;

/********************************************************************/
//makes maximals when (q-1, 6) = 6.
//d6 is all the data about where in the group we are, and hence what
//subgroups and conjugacy classes must be made. 
function Deq6Maximals(q, factor, psl, d6, Print)

  assert q gt 11;
  fac:= Factorisation(q); 
  assert #fac eq 1;
  p:= fac[1][1];
  e:= fac[1][2];

  assert q mod 6 eq 1;
  diag:= GL(6, q).1@factor;

  maximals:= [];

  //first the subfield groups
  if Print gt 1 then "getting subfields"; end if;
  fac_e:= Factorisation(e);
  for d in fac_e do
    f:= e div d[1];
    copies:= Gcd(6, (p^e-1) div (p^f-1));
    if (copies eq 1) or (copies eq 2 and d6`in_c2_ker) or
       (copies eq 3 and d6`in_c3_stab) or (copies eq 6 and
       d6`in_c6_stab) then
      subfield:=  SubfieldSL(6, p, e, f)@factor;
      if copies eq 1 then 
        Append(~maximals, subfield);
      elif copies eq 2 then
        groups:= ImageCopies(subfield,2,diag);
        maximals:= maximals cat groups;
      elif copies eq 3 and d6`in_c3_ker then
        groups:= ImageCopies(subfield,3,diag);
        maximals:= maximals cat groups;
      elif copies eq 3 then
        Append(~groups,SelectGroupFromSubset(psl,subfield,diag,
               d6`c3_invol,3));
      elif copies eq 6 and d6`in_c6_ker then
        groups:= ImageCopies(subfield,6,diag);
      else
        assert copies eq 6;
        grp:= SelectGroupFromSubset(psl,subfield,diag,d6`c3_invol,6);
        Append(~maximals,grp);
        Append(~maximals,grp^(diag^3));
      end if;
    end if;
  end for;     


  if d6`in_sp_stab then
    if Print gt 1 then "getting symplectic"; end if;
    sp:= NormOfSp(6,q)@factor;    
    if d6`in_sp_ker then
      groups:= ImageCopies(sp,3,diag);
      maximals:= maximals cat groups;
    else
      Append(~maximals,SelectGroupFromSubset(psl,sp,diag,d6`sp_invol,3));
    end if;

    if Print gt 1 then "getting SOPlus"; end if;
    oplus:= NormOfO(6,q,+1)@factor;    
    if d6`in_sp_ker then
      groups:= ImageCopies(oplus,3,diag);
      maximals:= maximals cat groups;
    else
      Append(~maximals,SelectGroupFromSubset(psl,oplus,diag,d6`sp_invol,3));
    end if;
  end if;

  if d6`in_ominus_stab then
    if Print gt 1 then "getting SOMinus"; end if;
    ominus:= NormOfO(6,q,-1)@factor;
    if d6`in_ominus_ker then
      groups:= ImageCopies(ominus@factor,3,diag);
      maximals:= maximals cat groups;
    else
      Append(~maximals,SelectGroupFromSubset(psl,ominus,diag,d6`omin_invol,3));
    end if;
  end if;
   
  if IsEven(e) then
    half:= e div 2;
    q_0:= p^half;
    classes:= Gcd(q_0-1, 6);
    if (classes eq 2 and d6`in_c2_stab) or (classes eq 6 and
      d6`in_c6_stab) then
      if Print gt 1 then "getting SU"; end if;
      su:= NormOfSU(6, q_0)@factor;
      if (classes eq 2) or (classes eq 6 and d6`in_c6_ker) then
        groups:= ImageCopies(su,classes,diag);
        maximals:= maximals cat groups;
      else
        grp:= SelectGroupFromSubset(psl,su,diag,d6`c6_invol,6);
        Append(~maximals, grp);
        Append(~maximals, grp^(diag^3));
      end if;
    end if;
  end if;

  //and now the C9s

  //now 6A7. 12 classes in PSL(6,p^2) when (p mod 24) in [5,11,13,19]
  if d6`in_a7_stab then
    if Print gt 1 then "getting 6A_7"; end if;
    c9:=Get6a7d6(q);
    if d6`in_a6_ker then
      c92:= sub<GL(6,q)|[Transpose(c9.-i) : i in [1..Ngens(c9)]]>;
      groups1:= ImageCopies(c9@factor,6,diag);
      groups2:= ImageCopies(c92@factor,6,diag);
      maximals:= maximals cat groups1 cat groups2;
    else
      c9:= c9@factor;
      grp:= SelectGroupFromSubset(psl,c9,diag,d6`a7_invol,6);
      Append(~maximals,grp);
      Append(~maximals, grp^(diag^3));
      grp2:= c9^(d6`a7_elt);
      grp3:= SelectGroupFromSubset(psl,grp2,diag,d6`a7_invol,6);
      Append(~maximals,grp3);
      Append(~maximals,grp3^(diag^3));      
    end if;
  end if;

  //now 6A6, which is a novelty maximal when out is a conjugate of 
  //<frob> ( p  = 1(6)) or <frob*iota> (p = 5(6)), and p mod 24 
  //in [ 5,11,13,19]. otherwise contained in 6A7.
  if d6`in_a6_stab then
    if Print gt 1 then "getting 6A_6"; end if;
    c9:=Get6a6d6(q);
    grp1:= SelectGroupFromSubset(psl,c9@factor,diag,d6`a6_invol,6);
    Append(~maximals, grp1);
    Append(~maximals, grp1^(diag^3));
  end if;

  if d6`in_l3q_ker then
    if Print gt 1 then "getting SL_3(q)"; end if;
    c9:= MatrixGroup(SymmetricSquare(GModule(SL(3, q))));
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
 *          socle PSL(6, q) for q prime power,
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


function L6qIdentify(group, q:  max:= true, Print:=0)

  fac:= Factorisation(q);
  assert #fac eq 1;
  e:= fac[1][2];
  assert e gt 1;
  p:= fac[1][1];


  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(6,q);
  sl := SL(6,q);
  apsl := PGammaL2(6,q);
  AssertAttribute(apsl, "Order", (2*e*#GL(6,q) div (q-1))); 
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;
  AssertAttribute(psl, "Order", (#SL(6,q) div Gcd(6, q-1)));

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 6, p, e, psl, apsl, factor : Print:=0);

  // Set up the subgroup of the outer automorphism group induced by group
  if max then
    d:= Gcd(q-1, 6);
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
    assert p eq 2;
    d6:= Deq1WhichGroup(quot,groupquot,delta,phia, iota, e);
  elif d eq 2 then
    d6 := Deq2WhichGroup(quot,groupquot,delta,phia, iota, p, e);
  elif d eq 3 then
    assert p eq 2;
    d6 := Deq3WhichGroup(quot,groupquot,delta,phia,iota,e,proj); 
  elif d eq 6 then
    d6:= Deq6WhichGroup(quot,groupquot,delta,phia,iota,p,e,proj);
  end if;

  maximals:= [];

  if Print gt 1 then "getting reducibles"; end if;
  if not d6`is_novelty then
    Append(~maximals,  (SLPointStab(6, q)@factor));
    Append(~maximals,  (SLStabOfNSpace(6, q, 2)@factor));
    Append(~maximals,  (SLStabOfNSpace(6, q, 4)@factor));
    Append(~maximals,  (SLStabOfNSpace(6, q, 5)@factor));
  else 
    Append(~maximals, (SLStabOfNSpaceMeetDual(6, q, 1)@factor));
    Append(~maximals, (SLStabOfNSpaceMissDual(6, q, 1)@factor));
    Append(~maximals, (SLStabOfNSpaceMeetDual(6, q, 2)@factor));
    Append(~maximals, (SLStabOfNSpaceMissDual(6, q, 2)@factor));
  end if;
  Append(~maximals, SLStabOfHalfDim(6, q)@factor);

  if Print gt 1 then "getting imprimitives"; end if;
  if q gt 4 then
    Append(~maximals, (ImprimsMeetSL(6, q, 6)@factor));
  end if;
  Append(~maximals, (ImprimsMeetSL(6, q, 3)@factor));
  Append(~maximals, (ImprimsMeetSL(6, q, 2)@factor));

  if Print gt 1 then "getting semilinears"; end if;
  Append(~maximals, (GammaLMeetSL(6, q, 2)@factor));
  Append(~maximals, (GammaLMeetSL(6, q, 3)@factor));

  if Print gt 1 then "getting tensors"; end if;
  Append(~maximals, (SLTensor(2, 3, q))@factor);

  if d eq 1 then
    maximals:= maximals cat Deq1Maximals(q, factor, d6, Print);
  elif d eq 2 then
    maximals:= maximals cat Deq2Maximals(q, factor, d6, Print);
  elif d eq 3 then
    maximals:= maximals cat Deq3Maximals(q, factor,psl, d6, Print);
  elif d eq 6 then
    maximals:= maximals cat Deq6Maximals(q, factor,psl, d6, Print);
  end if;

  return homom, apsl, maximals, F, phi;

end function;







