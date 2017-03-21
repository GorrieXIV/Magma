freeze;
 
/* function names in this file:
Getsl27d4
A7(p)
U4_2(p)
AandB(p)
NormOfOMinus(p)
NormOfOPlus(p)
CoprimeMaximals(p, factor, type,Print)
NonCoprimeMaximals(group, p, factor, type, psl, soc,Print)
L4pIdentify(group, p)
*/


import "gl2.m": PGammaL2;
import "reds.m": SLPointStab, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
                 SLStabOfNSpaceMissDual, SLStabOfHalfDim;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "normes.m": NormaliserOfSymplecticGroup;
import "select_conj.m": ImageCopies, SelectGroupGeneral;
import "psl2q.m": MakeHomomGeneral;
import "construct.m": ReduceOverFiniteField;

Getsl27d4:= function(p)

_LR := rec < recformat< F: GrpFP, AI: SeqEnum, G: GrpMat > |
      F := FreeGroup(2) >;
_LR`AI := [ [a^-1, b^-1] ] where a is (_LR`F).1 where b is (_LR`F).2;
//two constituents interchanged by _LR`AI[1][1]

_LR`G := sub<GL(8,Integers()) |
    \[ 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 
    0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 
    0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0 ],
    \[ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 
    0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0 ] >;

L:=  ReduceOverFiniteField(_LR, p);
c9:=L[1];
//just testing this for now, delete later.
assert IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and
      IsPrimitive(c9) and (not IsTensor(c9)) and
      ClassicalForms(c9)`formType eq "linear";
return c9;
end function;


/*******************************************************************
* 2.Alt(7) is a maximal C_9 group of SL(4, p) for p gt 7 and       *
* b7 in GF(p). has been tested on all primes p s.t. 8 lt p lt 1000 *
*******************************************************************/

function A7(p)
  assert IsPrime(p) and p gt 7;
  sl:= SL(4, p);
  i7:= SquareRoot(GF(p)!(-7));
  b7 := GF(p)!((-1+i7)/2);
  x := GF(p)!((i7+3)/4);
  y := GF(p)!(b7/2);
  C := sl![0,0,1,0, 0,0,0,1, -1,0,-1,0, 0,-1,0,-1];
  D := sl![0,-x,x,-y, -y,y,-y,0, -y,0,(-i7-1)/2,-x, 0,-y,y,y];
  G := sub<sl|C,D>;
  return G;
end function;

/* 
 * We find a maximal C_9 subgroup isomorphic to U_(4, 2) = Sp(4, 3)
 * whenever the field has order divisible by 3. This actually 
 * creates 2.Sp(4, 3) \leq SL(4, p), hence derived subgroup at the end.
 */

function U4_2(p)
  assert (p-1) mod 3 eq 0;
  z:= PrimitiveElement(GF(p));
  omega:= z^((p-1) div 3);
  omegab:= omega^2;
  g1:= GF(p)!((2 + omega)/3);
  g2:= GF(p)!((1 - omega)/3);
  f1:= GF(p)!((1 + 2*omegab)/3);
  f2:= GF(p)!((1 - omegab)/3);
  a:= GL(4, p)!DiagonalMatrix([1, 1, omega, 1]);
  b:= GL(4, p)!
  [ 1,  0,  0,  0,
    0, f1, f2, f2, 
    0, f2, f1, f2, 
    0, f2, f2, f1];
  c:= GL(4, p)!
  [ g1, 0, -g2, g2,
     0, 1,   0,  0,
   -g2, 0,  g1, g2,
    g2, 0,  g2, g1];
  grp:= sub<GL(4,p)|a, b, c>;
  return DerivedSubgroup(grp);
end function;

/*
 * The elements a and b of GF(p) are needed to make the 
 * normaliser in SL of O^-(4, p). They satisfy a^2+b^2 = z. 
 * See Kleidman + Liebeck, p39 for details.
 */ 

function AandB(p)
  z:= PrimitiveElement(GF(p));
  for b in [1..p-1] do
    bool, a:= IsSquare(z-GF(p)!b^2);
    if bool then
      return a, b;
    end if;
  end for;
  "couldn't find a and b in GF(", p, ")";
  return false, _;
end function;

/*******************************************************************/
//Makes the normaliser of SOMinus(4, p) in SL(4,p): only designed for
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
//Makes the normaliser in SL(4, p) of SOPlus(4, p): only 
//designed for p=1 mod 4.
function NormOfOPlus(p)
  g1:= SOPlus(4, p);
  bool, type, form:= OrthogonalForm(g1);
  mat1:= CorrectForm(form, 4, p, "orth+");
  norm1:= GL(4, p)!DiagonalMatrix([-1, 1, 1,1]);
  norm1:= norm1^(mat1^-1);
  z:= PrimitiveElement(GF(p));
  norm2:= GL(4, p)!DiagonalMatrix([1, 1, z, z]);
  norm2:= norm2^((p -1) div 4);
  group:= sub<SL(4, p)|g1, norm1*norm2>;
  return group;
end function;

/********************************************************************/
//This makes those maximal subgroups which behave differently when p=3
//mod 4 from the general case.
function CoprimeMaximals(p, factor, type, Print)

  maximals:= [];

  diag := (GL(4, p).1) @ factor;
  ominus:= NormOfOMinus(p);
  Append(~maximals, ominus@factor);

  //C_9s.
  if Print gt 1 then print "getting C_9's"; end if;
  if type in {"psl", "psl.2_2"} then
    if not (p mod 7) eq 0 and IsSquare(GF(7)!p) then
      alt7:= A7(p) @ factor;
      maximals:= maximals cat ImageCopies(alt7, 2, diag);
    end if;
    if p mod 6 eq 1 then
      u4_2:= U4_2(p) @ factor;
      maximals:= maximals cat ImageCopies(u4_2, 2, diag);
    end if;
  end if;
  if not (p mod 7) eq 0 and IsSquare(GF(7)!p) then
    if (((p mod 8) eq 7) and type eq "psl.2_2") or 
       (((p mod 8) eq 3) and type eq "psl.2_3") then
      c9:= Getsl27d4(p) @ factor;
      maximals:= maximals cat ImageCopies(c9, 2, diag);
    end if;
  end if;

  return maximals;
end function;

/********************************************************************/
//Those maximal subgroups which behave differently when p=1 mod 4.
function NonCoprimeMaximals(p, factor, type, soc, psl, invol, Print)

  maximals:= [];

  /* 
   * Extraspecials: We have 4 conjugate classes of 2^4:Sym_6 if p=1
   * \mod 8 and type = "psl", Two of these extend in "psl.2_2",
   * otherwise they fuse (pairwise or in 4s..).
   * if p = 5 mod 8 we have 2 conjugate 2^4:\Alt_6 which extend in
   * psl.2_1, psl.2_2 and psl.12, but fuse elsewhere.
   */
  diag := (GL(4, p).1) @ factor;
  if type in {"psl", "psl.2_1", "psl.2_2", "psl.12"} then
    if (p mod 8 eq 1) and type in {"psl", "psl.2_2"} then
      extraspec:= NormaliserOfSymplecticGroup(4, p);
      if type cmpeq "psl" then
        if Print gt 1 then print "getting extraspecials"; end if;
        maximals:= maximals cat ImageCopies(extraspec@factor, 4, diag);
      elif type cmpeq "psl.2_2" then
        if Print gt 1 then print "getting extraspecials"; end if;
        extraspec:= SelectGroupGeneral(psl,extraspec@factor,diag,invol);
        Append(~maximals,extraspec);
        Append(~maximals,extraspec^(diag^2));
      end if;
    elif p mod 8 eq 5 then
      if Print gt 1 then print "getting extraspecials"; end if;
      ext:= NormaliserOfSymplecticGroup(4, p);
      ext1:= sub<ext|[ext.i : i in [1..Ngens(ext)]| Determinant(ext.i)
                    eq 1]>;
      maximals:= maximals cat ImageCopies(ext1@factor, 2, diag);
    end if;
  end if;

  if type in {"psl", "psl.2_1", "psl.2_3", "psl.13"} then
    if Print gt 1 then print "getting OMinus(4,p)"; end if;
    ominus:= NormOfOMinus(p) @ factor;
    maximals:= maximals cat ImageCopies(ominus,2,diag);
  end if;

  //C_9s
  if Print gt 1 then print "getting C_9's"; end if;
  if type cmpeq "psl" or type cmpeq "psl.2_2" then
    if not (p eq 7) and (IsSquare(GF(7)!p)) then
      alt7:= A7(p) @ factor;
      if type cmpeq "psl" then
        maximals:= maximals cat ImageCopies(alt7, 4, diag);
      elif type cmpeq "psl.2_2" then
        alt7:= SelectGroupGeneral(psl,alt7,diag,invol);
        Append(~maximals,alt7);
        Append(~maximals,alt7^(diag^2));
      end if;
    end if;
    if p mod 6 eq 1 then
      u4_2:= U4_2(p) @ factor;
      if type cmpeq "psl" then
        maximals:= maximals cat ImageCopies(u4_2, 4, diag);
      else
        u4_2:= SelectGroupGeneral(psl,u4_2,diag,invol);
        Append(~maximals,u4_2);
        Append(~maximals,u4_2^(diag^2));
      end if;
    end if;
  end if;
  //novelty L_2(7)s
  if ((not (p eq 7)) and (IsSquare(GF(7)!p)) and type in {"psl.2_2", 
          "psl.2_3"}) then 
    if (((p mod 8) eq 1) and type eq "psl.2_2") or 
     (((p mod 8) eq 5) and type eq "psl.2_3")  then
      l27:= Getsl27d4(p)@factor;
      l27:= SelectGroupGeneral(psl,l27,diag,invol);
      Append(~maximals,l27);
      Append(~maximals,l27^(diag^2));
    end if;
  end if;


  return maximals;
end function;

/******************************************************************/
/*
 The main function. This works out the type of group and whether 
 or not we're coprime (i.e. whether or not p=3 mod 4). It then
 computes the maximal subgroups which don't depend so much 
 on whether or not we're in the coprime case, before calling 
 and NonCoprimeMaximals to get the rest.
 */

function L4pIdentify(group, p: max:= true, Print:=0)

  assert IsPrime(p);
  assert p gt 3; //PSL(4, 2) and PSL(4, 3) are special cases.

  if p mod 4 eq 3 then
    coprime:= true;
  else
    coprime:= false;
  end if;

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(4,p);
  sl := SL(4,p);
  apsl := PGammaL2(4,p);
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;

  diag:= GL(4, p).1 @ factor;

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 4, p, 1, psl, apsl, factor : Print:=0);

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi :=
      FPGroupStrong(sub< psl | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);
  
  if Print gt 1 then print "Identifying group"; end if;
  // Also get the generators of apsl correct
  newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
  image := Image(homom);
  invol := apsl.3;
  if image eq psl then type := "psl";
    apsl := sub< apsl | newgens  cat [apsl.1,apsl.3] >;
  elif image eq apsl then type := "aut_psl";
    apsl := sub< apsl | newgens >;
  elif coprime then
    //when coprime the outer automorphism group is 2^2
    if image eq sub<apsl|apsl.1,apsl.2> then type := "pgl";
      apsl := sub< apsl | newgens cat [apsl.3] >;
    elif image eq sub<apsl|apsl.1^2,apsl.2,apsl.3> then type := "psl.2_2"; 
      apsl := sub< apsl | newgens cat [apsl.1] >;
    else assert image eq sub<apsl|apsl.1^2,apsl.2,apsl.1*apsl.3>;
           type := "psl.2_3";
      apsl := sub< apsl | newgens cat [apsl.3] >;
    end if;
    //now the outer aut group is D_{2 x 4}
  elif image eq sub<apsl|apsl.1,apsl.2> then type := "pgl";
      apsl := sub< apsl | newgens cat [apsl.3] >;
  elif image eq sub<apsl|apsl.1^2,apsl.2,apsl.3> then type := "psl.12";
      //outer aut of order 4: diag^2, duality, product.
      apsl := sub< apsl | newgens cat [apsl.1] >;
  elif image eq sub<apsl|apsl.1^2,apsl.2,apsl.1*apsl.3> then type := "psl.13";
      //outer aut of order 4: diag^2, duality*diag, product.
      apsl := sub< apsl | newgens cat [apsl.3] >;
  elif image eq sub<apsl|apsl.1^2,apsl.2> then type := "psl.2_1";
      //outer aut of order 2, diag^2 (central)
      apsl := sub< apsl | newgens cat [apsl.1,apsl.3] >;
  elif image eq sub<apsl|apsl.1^4,apsl.2,apsl.3> or
   image eq sub<apsl|apsl.1^4,apsl.2,apsl.1^2*apsl.3>  then type := "psl.2_2";
      //outer aut of order 2, either duality or duality*diag^2 (these are
      //conjugate in Out(PSL))
      apsl := sub< apsl | newgens cat [apsl.1] >;
      invol := group.(Ngens(group)) @ homom;
  else assert image eq sub<apsl|apsl.1^4,apsl.2,apsl.1*apsl.3> or
   image eq sub<apsl|apsl.1^4,apsl.2,apsl.1^3*apsl.3>; type := "psl.2_3";
      //outer aut of order 2, either duality*diag or duality*diag^2 
      //(these are conjugate in Out(PSL)) 
      apsl := sub< apsl | newgens cat [apsl.1] >;
      invol := group.(Ngens(group)) @ homom;
  end if;
  if Print gt 1 then print "Type = ",type; end if;

  maximals:= [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "getting reducibles"; end if;
  if type in {"psl", "psl.2_1", "pgl"} then
    Append(~maximals,  SLPointStab(4, p)@factor);
    Append(~maximals,  SLStabOfNSpace(4, p, 3)@factor);
  else 
    Append(~maximals, SLStabOfNSpaceMeetDual(4, p, 1)@factor);
    Append(~maximals, SLStabOfNSpaceMissDual(4, p, 1)@factor);
  end if;
  Append(~maximals, SLStabOfHalfDim(4, p)@factor);

  if Print gt 1 then print "getting imprimitives"; end if;
  if p gt 5 or type in {"pgl", "psl.13", "psl.2_3"}then
    Append(~maximals, ImprimsMeetSL(4,p,4)@factor);
  end if;
  Append(~maximals, ImprimsMeetSL(4,p,2)@factor);

  if Print gt 1 then print "getting semilinears"; end if;
  Append(~maximals, GammaLMeetSL(4, p, 2)@factor);

  //Sp(4, p): 2 copies if exists: coprime PSL. PSL.2_2.
  i:= SL(4, p)!DiagonalMatrix([1, 1, -1, -1]);
  if type in {"psl", "psl.2_1", "psl.2_2", "psl.12"} then
    if Print gt 1 then print "getting Sp(4,p)"; end if;
    symp:= sub<SL(4, p)|Sp(4, p), i> @ factor;
    maximals:= maximals cat ImageCopies(symp,2,diag);
  end if;
    
  if coprime then
    if Print gt 1 then print "getting SOPlus(4,p)"; end if;
    oplus:= sub<SL(4, p)|SOPlus(4, p), i>;
    Append(~maximals, oplus@factor);
  elif type in {"psl", "psl.2_1", "psl.2_2", "psl.12"} then 
    if Print gt 1 then print "getting OPlus(4,p)"; end if;
    oplus:= NormOfOPlus(p)@factor;
    maximals:= maximals cat ImageCopies(oplus,2,diag);
  end if;

  if coprime then
    maximals:= maximals cat CoprimeMaximals(p, factor, type, Print);
  else maximals:= maximals cat
          NonCoprimeMaximals(p, factor, type, soc, psl, invol, Print);
  end if;

  return homom, apsl, maximals, F, phi;
end function;
