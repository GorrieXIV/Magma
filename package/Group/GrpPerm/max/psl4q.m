freeze;
 
/*
 * This file will contain the functions to construct the maximal
 * subgroups of any almost simple group $G$ with $PSL(4, p^e) < G <
 * PGammaL2(4, p^e), with $e>2$.
 */

/* function names in this file:
CoprimeWhichGroup(group, p)
NonCoprimeWhichGroup(group, p)
A7(p)
U4_2(p)
AandB(p)
NormOfOMinus(p)
NormOfOPlus(p)
CoprimeMaximals(p, factor, homom, type)
NonCoprimeMaximals(group, p, factor, homom, type, soc)
L4pMaximals(group, p)
*/


import "gl2.m": PGammaL2;
import "reds.m": SLPointStab, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
                 SLStabOfNSpaceMissDual, SLStabOfHalfDim;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "select_conj.m": ImageCopies, SelectGroupGeneral;
import "psl2q.m": MakeHomomGeneral;
import "subfield.m": SubfieldSL;


/****************************************************************/
//The following three functions still have to be written..

/* input: almost simple group socle PSL(4, 2^e). 
   output: socle, and boolean which is true iff group has novelty 
   reducible subgroups (i.e. if group \not\leq PSigmaL(4, p^e).
 */

function CoprimeWhichGroup(quot,groupquot,phi)
  is_novelty:= not groupquot subset sub < quot | phi >;
  return is_novelty;
end function;

/*
  input: almost simple group with socle PSL(4, p^e) where (p^e-1, 4) = 2.
  output: socle and two booleans. The first is true iff the group
  has novelty reducible subgroups (i.e. if group \not\leq PGammaL(4,
  p^e)). the second is true iff the group has two copies of each
  possible subgroup i.e. if group/PSL \leq <\phi, \iota>.
*/

function Deq2WhichGroup(quot,groupquot,delta,phi,iota)
  is_novelty:= not groupquot subset sub < quot | delta, phi >;
  in_stab:= groupquot subset sub < quot | phi,iota >;
  return is_novelty, in_stab;
end function;

/*
input: almost simple group with socle PSL(4, p^e) where (p^e-1, 4) = 4.

output: socle, 5 booleans and (maybe) outer involution. 
The first is true iff the group has novelty reducible 
subgroups (i.e. if group \not\leq PGammaL(4, p^e). 

if p = 1 mod 4 then the second is true iff group \leq 
PSigmaL(4, p) (which i think is normal?)
if p = 3 mod 4 then the second is true iff group/PSL \leq a conjugate
of <\phi^2, \iota.\phi> (which is probably also normal)
in either case the group may have 4 copies of a subfield group
and/or 4 copies of a unitary group.

the third boolean is true iff group/PSL \leq a conjugate of
<\phi, \iota>. This implies has two classes of subfield groups 
(out of up to 4), and has two classes of unitary groups (out of up to 4).

the fourth boolean is true iff group/PSL \leq a conjugate of <\delta^2, \phi,
\iota>. This implies that the group has two copies of subfield
groups if the maximum possible is two, has two copies of Sp(4, q)
and two copies of PSO^+(4, q). The group also has two copies of the
unitary subgroup *iff* the maximum possible is two (i.e. if
(p^(e/2)-1, 4) = 2).

the final, fifth boolean is true iff
p = 1 mod 4 and group /PSL \leq a conjgate of
        <\delta^2, \phi, \iota\delta> OR
p = 3 mod 4 and group/PSL \leq a conjgate of
        <\delta^2, \phi\delta, \iota\delta>.
This implies that has two classes of PSO^-(4, q). 

*if* the third boolean is true, and the second isn't, then we need
an outer involution that lies in the relevant conjugate of
<\phi, \iota>\setminus<\phi> if p = 1 mod 4 and in 
the relevant conjugate of  <\phi, \iota>\setminus<\phi^2,
\iota\phi> if p = 3 (4). 

If the second boolean is true, then the third and fourth must be,
if the third is true then the fourth must be.

*/

function Deq4WhichGroup(quot,groupquot,delta,phi,iota,p)
  is_novelty:= not groupquot subset sub< quot | delta, phi >;
  in_kernel:= p mod 4 eq 1 select groupquot subset sub< quot | phi >
                    else  groupquot subset sub < quot | phi^2, iota*phi >;
  stab_4:= groupquot subset sub< quot | phi, iota > or
                 groupquot subset sub< quot | phi, iota >^delta;
  stab_2:= groupquot subset sub< quot | delta^2, phi, iota >;
  two_orthminus:= p mod 4 eq 1 
       select groupquot subset sub< quot | delta^2, phi, iota*delta >
       else groupquot subset sub< quot | delta^2, phi*delta, iota*delta >;
  if stab_4 and not in_kernel then
    invol := Random(groupquot);
    while (p mod 4 eq 1 and invol in sub< quot | phi, delta^2 >) or
          (p mod 4 eq 3 and invol in
                 sub< quot | phi^2, iota*phi, delta^2 >) do
       invol := Random(groupquot);
    end while;
  else invol:= Id(groupquot);
  end if;

  return is_novelty, in_kernel, stab_4, stab_2, two_orthminus, invol;
end function;

/*********************************************************************/

/*
 * The elements a and b of GF(q) are needed to make the 
 * normaliser in SL of O^-(4, q). They satisfy a^2+b^2 = z. 
 * See Kleidman + Liebeck, p39 for details.
 */ 

function AandB(q)
  z:= PrimitiveElement(GF(q));
  for b in GF(q) do
    bool, a:= IsSquare(z-GF(q)!b^2);
    if bool then
      return a, b;
    end if;
  end for;
  "couldn't find a and b in GF(", q, ")";
  return false, _;
end function;

/*******************************************************************/
//Makes the normaliser of SOMinus(4, q) in SL(4,q): only designed for
//p=3 mod 4,
function NormOfOMinus(p)
  g1:= SOMinus(4, p);
  bool, type, form:= OrthogonalForm(g1);
  mat2:= GL(4, p)!CorrectForm(form, 4, p, "orth-");
  a, b:= AandB(p);
  z:= PrimitiveElement(GF(p)); 
  norm_mat:= GL(4, p)![a, b, 0, 0,
                     b, -a, 0, 0,
                     0, 0, 0, 1,
                     0, 0, z, 0];
  if p mod 4 eq 3 then
    norm_mat:= (norm_mat^((p-1) div 2))^(mat2^-1);
  else
    norm_mat:= ((norm_mat^((p-1) div 4))^(mat2^-1))*GOMinus(4, p).4;
  end if;
  assert not norm_mat in g1;
  assert Determinant(norm_mat) eq 1;
  group:= sub<SL(4, p)|g1, norm_mat>;
  return group;
end function;

/***************************************************************/
//Makes the normaliser in SL(4, q) of SOPlus(4, q): only for q =
//1(4). 
function NormOfOPlus(q)
  g1:= SOPlus(4, q);
  bool, type, form:= OrthogonalForm(g1);
  mat1:= CorrectForm(form, 4, q, "orth+");
  norm1:= GL(4, q)!DiagonalMatrix([-1, 1, 1,1]);
  norm1:= norm1^(mat1^-1);
  z:= PrimitiveElement(GF(q));
  norm2:= GL(4, q)!DiagonalMatrix([1, 1, z, z]);
  norm2:= norm2^((q -1) div 4);
  group:= sub<SL(4, q)|g1, norm1*norm2>;
  return group;
end function;

/***************************************************************/
function NormOfSU(p, e)
  i:= GL(4, p^e)!DiagonalMatrix([1, 1, -1, -1]);
  if p^(e div 2) mod 4 eq 3 then
    su:= sub<SL(4, p^e)| SU(4, p^(e div 2)), i>;
  else
    x1:= GU(4, p^(e div 2)).1; 
    elt:= PrimitiveElement(GF(p^e))^((p^(e div 2) -1) div 4);
    su:= sub<SL(4, p^e)|SU(4, p^(e div 2)), x1*ScalarMatrix(4, elt)>;
  end if; 
  return su;
end function;

/********************************************************************/
//This makes those maximal subgroups which behave differently when 
//d = 1 (i.e. q is even)

function CoprimeMaximals(p, e, factor, is_novelty, Print)
  assert p eq 2;
  q:= 2^e; 

  maximals:= [];

  if Print gt 1 then "getting reducibles"; end if;
  if not is_novelty then
    Append(~maximals,  SLPointStab(4, q)@factor);
    Append(~maximals,  SLStabOfNSpace(4, q, 3)@factor);
  else 
    Append(~maximals, SLStabOfNSpaceMeetDual(4, q, 1)@factor);
    Append(~maximals, SLStabOfNSpaceMissDual(4, q, 1)@factor);
  end if;
  Append(~maximals, SLStabOfHalfDim(4, q)@factor);

  if Print gt 1 then "getting imprimitives"; end if;
  if q gt 4 then
    Append(~maximals, ImprimsMeetSL(4, q, 4)@factor);
  end if;
  Append(~maximals, ImprimsMeetSL(4, q, 2)@factor);

  if Print gt 1 then "getting semilinears"; end if;
  Append(~maximals, GammaLMeetSL(4, q, 2)@factor);

  if Print gt 1 then "getting subfields"; end if;
  fac:= Factorisation(e);
  for x in fac do
    f:= e div x[1];
    Append(~maximals, sub<SL(4, q)|Eltseq(SL(4, 2^f).1), 
              Eltseq(SL(4, 2^f).2)>@factor);
  end for;

  if Print gt 1 then "getting classicals"; end if;
  sp:= sub<SL(4, q)|Sp(4, q)>;
  Append(~maximals, sp@factor);

  if IsEven(e) then
    Append(~maximals, SU(4, 2^(e div 2))@factor);
  end if;

  return maximals;
end function;

/********************************************************************/
//Those maximal subgroups which behave differently when p=1 mod 4.
function D_eq_2_Maximals(p, e, factor, is_novelty, in_stab, Print)
  assert p^e mod 4 eq 3;
  q:= p^e;  
is_novelty, in_stab;

  diag:= GL(4, q).1 @ factor;

  maximals:= [];

  if Print gt 1 then "getting reducibles"; end if;
  if not is_novelty then
    Append(~maximals,  SLPointStab(4, q)@factor);
    Append(~maximals,  SLStabOfNSpace(4, q, 3)@factor);
  else 
    Append(~maximals, SLStabOfNSpaceMeetDual(4, q, 1)@factor);
    Append(~maximals, SLStabOfNSpaceMissDual(4, q, 1)@factor);
  end if;
  Append(~maximals, SLStabOfHalfDim(4, q)@factor);

  if Print gt 1 then "getting imprimitives"; end if;
  Append(~maximals, ImprimsMeetSL(4, q, 4)@factor);
  Append(~maximals, ImprimsMeetSL(4, q, 2)@factor);

  if Print gt 1 then "getting semilinear"; end if;
  Append(~maximals, GammaLMeetSL(4, q, 2)@factor);

  if Print gt 1 then "getting subfield groups"; end if;
  fac:= Factorisation(e);
  for x in fac do
    f:= e div x[1];
    c:= (q-1)div Lcm(p^f-1, (q-1) div 2); //d eq 2;
c;
    assert (c eq 1 or c eq 2);
    if c eq 1 then
      Append(~maximals, SubfieldSL(4, p, e, f)@factor);
    elif in_stab then
      subf:= SubfieldSL(p, e, f) @ factor;
      groups:= ImageCopies(subf,2,diag);
      maximals:= maximals cat groups;
    end if;
  end for;
 
  i:= SL(4, q)!DiagonalMatrix([1, 1, -1, -1]);
 
  if in_stab then
   if Print gt 1 then "getting symplectic group"; end if;
    sp:= sub<SL(4, q)|Sp(4, q), i> @ factor;
    groups:= ImageCopies(sp,2,diag);
    maximals:= maximals cat groups;
  end if;
 
  if Print gt 1 then "getting orthogonal groups"; end if;
  oplus:= sub<SL(4, q)|SOPlus(4, q), i>;
  Append(~maximals, oplus@factor);
  ominus:= NormOfOMinus(q);
  Append(~maximals, ominus@factor);

  if IsEven(e) and in_stab then
    if Print gt 1 then "getting unitary groups"; end if;
    su:= NormOfSU(p, e) @ factor;
    groups:= ImageCopies(su,2,diag);
    maximals:= maximals cat groups;
  end if;

  return maximals;
end function;


/******************************************************************/

function D_eq_4_Maximals(p, e, factor, psl,
         is_novelty, in_kernel, stab_4, stab_2, two_orthminus, invol, Print)

  assert IsPrime(p);
  assert Gcd(p^e-1, 4) eq 4;
  q:= p^e;

  diag:= GL(4, q).1 @ factor;

  maximals:= [];

  if Print gt 1 then "getting reducibles"; end if;
  if not is_novelty then
    Append(~maximals,  SLPointStab(4, q)@factor);
    Append(~maximals,  SLStabOfNSpace(4, q, 3)@factor);
  else 
    Append(~maximals, SLStabOfNSpaceMeetDual(4, q, 1)@factor);
    Append(~maximals, SLStabOfNSpaceMissDual(4, q, 1)@factor);
  end if;
  Append(~maximals, SLStabOfHalfDim(4, q)@factor);

  if Print gt 1 then "getting imprimitive groups"; end if;
  Append(~maximals, ImprimsMeetSL(4,q,4)@factor);
  Append(~maximals, ImprimsMeetSL(4,q,2)@factor);

  if Print gt 1 then "getting superfield group"; end if;
  Append(~maximals, GammaLMeetSL(4, q, 2)@factor);

  fac:= Factorisation(e);
  for x in fac do
    f:= e div x[1];
    c:= (q-1)div Lcm(p^f-1, (q-1) div 4); //d eq 4;
    assert (c eq 1 or c eq 2 or c eq 4);
    subf:= SubfieldSL(4, p, e, f) @ factor;
    if c eq 1 then
      if Print gt 1 then "getting subfield group"; end if;
      Append(~maximals, subf@factor);
    elif c eq 2 and stab_2 then
      if Print gt 1 then "getting subfield groups"; end if;
      groups:= ImageCopies(subf,2,diag);
      maximals:= maximals cat groups;
    elif c eq 4 and in_kernel then
      if Print gt 1 then "getting subfield groups"; end if;
      groups:= ImageCopies(subf,4,diag);
      maximals:= maximals cat groups;
    elif c eq 4 and stab_4 then
      if Print gt 1 then "getting subfield groups";; end if;
      subf:= SelectGroupGeneral(psl,subf,diag,invol);
      Append(~maximals, subf);
      Append(~maximals, subf^(diag^2));
    end if;
  end for;

  if stab_2 then
    if Print gt 1 then "getting symplectic groups"; end if;
    i:= SL(4, q)!DiagonalMatrix([1, 1, -1, -1]);
    sp:= sub<SL(4, q)|Sp(4, q), i> @ factor;
    groups:= ImageCopies(sp,2,diag);
    maximals:= maximals cat groups;
    if Print gt 1 then "getting orthogonal plus groups"; end if;
    oplus:= NormOfOPlus(q) @ factor;
    groups:=  ImageCopies(oplus,2,diag);
    maximals:= maximals cat groups;
  end if;

  if two_orthminus then
    if Print gt 1 then "getting orthogonal minus groups"; end if;
    grp_ominus:= NormOfOMinus(q) @ factor;
    groups:= ImageCopies(grp_ominus,2,diag);
    maximals:= maximals cat groups;
  end if;

  if IsEven(e) then
    su:= NormOfSU(p, e) @ factor;
    c:= Gcd(p^(e div 2) - 1, 4);
    assert (c eq 2 or c eq 4);
    if c eq 2 and stab_2 then
      if Print gt 1 then "getting unitary groups"; end if;
      groups:= ImageCopies(su,2,diag);
      maximals:= maximals cat groups;
    elif c eq 4 and in_kernel then
      if Print gt 1 then "getting unitary groups"; end if;
      groups:= ImageCopies(su,4,diag);
      maximals:= maximals cat groups;
    elif c eq 4 and stab_4 then
      if Print gt 1 then "getting unitary groups"; end if;
      su:= SelectGroupGeneral(psl,su,diag,invol);
      Append(~maximals, su);
      Append(~maximals, su^(diag^2));
    end if;
  end if;

  return maximals;
end function;

/*****************************************************************/
function L4qIdentify(group, q:  max:= true, Print:=0)
  fac:= Factorisation(q);
  assert #fac eq 1;
  p:= fac[1][1];
  e:= fac[1][2];
  assert e gt 1;

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(4,p^e);
  sl := SL(4,p^e);
  apsl := PGammaL2(4,p^e);
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;


  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 4, p, e, psl, apsl, factor : Print:=0);

  // Set up the subgroup of the outer automorphism group induced by group
  if max then
    d:= Gcd(q-1, 4);
    quot, proj := quo<apsl|psl>;
    delta := proj(apsl.1); assert Order(delta) eq d; //diagonal aut.
    phia := proj(apsl.3); assert Order(phia) eq e;     //field aut.
      //had used phi twice!
    iota := proj(apsl.4); assert Order(iota) eq 2;   //graph aut
    newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
    groupquot := sub< quot | [proj(g) : g in newgens] >; 
  end if;

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psl | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);

  //get apsl right
  newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
  subapsl := sub< apsl | newgens >;
  for g in Generators(apsl) do if not g in subapsl then
     Append(~newgens,g); subapsl := sub< apsl | newgens >;
  end if; end for;
  apsl := subapsl;

  if not max then
    return homom, apsl, [], F, phi;
  end if;

  if d eq 1 then
    assert p eq 2;
    is_novelty := CoprimeWhichGroup(quot,groupquot,phia);
    maximals := CoprimeMaximals(p, e, factor, is_novelty, Print);
  elif d eq 2 then
    is_novelty, in_stab := Deq2WhichGroup(quot,groupquot,delta,phia,iota);
    maximals := D_eq_2_Maximals(p, e, factor, is_novelty, in_stab, Print);
  elif d eq 4 then
    is_novelty, in_kernel, stab_4, stab_2, two_orthminus, invol :=
        Deq4WhichGroup(quot,groupquot,delta,phia,iota,p);
    invol := invol @@ proj;
    maximals := D_eq_4_Maximals(p, e, factor, psl,
         is_novelty, in_kernel, stab_4, stab_2, two_orthminus, invol, Print);
  end if;

  return homom, apsl, maximals, F, phi;

end function;
