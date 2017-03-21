freeze;
 
/*
functions in this file are:
SubfieldSL(p)
A6(q)
L3p2Maximals(group, p)
*/

import "gl2.m": PGammaL2;
import "reds.m": SLPointStab, SLStabOfNSpace,
                 SLPointMeetHyperplane, SLPointUnmeetHyperplane;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "select_conj.m": ImageCopies, SelectGroupGeneral;
import "psl2q.m": MakeHomomGeneral;

/******************************************************************/

function SubfieldSL(p)
  gens:= SetToSequence(Generators(SL(3, p)));
  newgens:= [];
  for i in [1..#gens] do
     Append(~newgens, SL(3, p^2)!Eltseq(gens[i]));
  end for;
  return sub<SL(3, p^2)|newgens>;
end function;
/*************************************************************/

function A6(q)
  assert #Factorisation(q) eq 1;
  assert IsSquare(GF(q)!5);
  r5:= SquareRoot(GF(q)!5);
  b5:= GF(q)!((-1 + r5)/2);
  z:= PrimitiveElement(GF(q));
  omega:= z^((q-1) div 3);
  h_2:= GF(q)!(omega - b5)*(2^-1);
  hbar_2:= GF(q)!(omega^2 - b5)*(2^-1);  
  half := GF(q)!(2^-1);
group:= sub<GL(3, q) | DiagonalMatrix([1, -1, -1]),
  [ 0,   1,   0, 
    0,   0,   1, 
    1,   0,   0],
   [-1,  0,   0,
     0,  0,  -1,
     0, -1,   0],
 [half,-half,-h_2,
 -half, half,-h_2,
hbar_2, hbar_2, 0] >;
  return group;
end function;

function L3p2Identify(group, q: max:= true, Print:=0)

  fac := Factorisation(q);
  p := fac[1][1];
  assert p gt 2;
  assert fac[1][2] eq 2;

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(3,p^2);
  sl := SL(3,p^2);
  apsl := PGammaL2(3,p^2);
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;
  pgl := gl @ factor;
  pgammal := sub<apsl|apsl.1,apsl.2,apsl.3>;

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 3, p, 2, psl, apsl, factor : Print:=0);

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psl | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);

  if Print gt 1 then print "Identifying group"; end if;
  // Also get the generators of apsl correct
  newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
  image := Image(homom);
  if image eq psl then type := "psl";
    apsl := sub< apsl | newgens  cat [apsl.1,apsl.3,apsl.4] >;
  elif image eq apsl then type := "aut_psl";
    apsl := sub< apsl | newgens >;
  elif image eq sub<apsl|apsl.1,apsl.2> then type := "pgl";
    apsl := sub< apsl | newgens cat [apsl.3,apsl.4] >;
  elif image eq pgammal then type := "pgammal";
    apsl := sub< apsl | newgens cat [apsl.4] >;
  elif #image eq 6 * #psl then type := "psl.3+";
    apsl := sub< apsl | newgens cat [apsl.4] >;
  elif #image eq 4 * #psl then type := "psl.2^2";
    apsl := sub< apsl | newgens cat [apsl.1] >;
    //want invol in coset of apsl.4
    invol := Random(Image(homom));
    while not invol*apsl.4 in pgl do invol := Random(Image(homom)); end while;
  else assert #image eq 2 * #psl;
    if sub<apsl | newgens cat [apsl.1] > eq sub<apsl | apsl.1,apsl.2,apsl.3>
      then type := "psl.2_G";
           apsl := sub< apsl | newgens cat [apsl.1,apsl.4] >;
           invol := group.(Ngens(group)) @ homom;
    elif sub<apsl | newgens cat [apsl.1] > eq sub<apsl | apsl.1,apsl.2,apsl.4>
      then type := "psl.2_A";
           apsl := sub< apsl | newgens cat [apsl.1,apsl.3] >;
           invol := group.(Ngens(group)) @ homom;
    else assert sub<apsl | newgens cat [apsl.1] > eq
                     sub<apsl | apsl.1,apsl.2,apsl.3*apsl.4>;
      type := "psl.2_AG";
           apsl := sub< apsl | newgens cat [apsl.1,apsl.4] >;
           invol := group.(Ngens(group)) @ homom;
    end if;
  end if;
  if Print gt 1 then "type =", type; end if;

  diag:= GL(3, p^2).1 @ factor;

  maximals:= [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  /*
   * Reducible - if we have psl then we get 2 classes, conjugate under
   * inverse transpose. Otherwise, we get two novelties, intersections 
   * are point with line containing it and point with line not
   * containing it. In both cases the two groups are returned as matrix
   * groups, so we factor by the centre before applying homom.
   */

  if Print gt 1 then "getting reducibles"; end if;
  if type in {"psl", "pgl", "psl.2_G", "pgammal"} then
    Append(~maximals,  SLPointStab(3, p^2)@factor);
    Append(~maximals,  SLStabOfNSpace(3, p^2, 1)@factor);
  else 
    Append(~maximals, SLPointMeetHyperplane(3, p^2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(3, p^2)@factor);
  end if;

  if Print gt 1 then "getting imprimitives"; end if;
  Append(~maximals, ImprimsMeetSL(3, p^2, 3)@factor);

  if Print gt 1 then "getting semilinears"; end if;
  Append(~maximals, GammaLMeetSL(3, p^2, 3)@factor);

  if Print gt 1 then "getting subfields"; end if;
  subf:= SubfieldSL(p) @ factor;
  if p mod 3 eq 2 then
    if type in {"psl", "psl.2_AG"} then
      groups:= ImageCopies(subf,3,diag);
      maximals:= maximals cat groups;
    elif type in {"psl.2_A", "psl.2_G", "psl.2^2"} then
      subf:= SelectGroupGeneral(psl,subf,diag,invol);
      Append(~maximals,subf);
    end if;
  else
    Append(~maximals, subf);
  end if;

  if Print gt 1 then "getting classicals"; end if;
  so3:= SO(3, p^2) @ factor;
  if type eq "psl" or (p mod 3 eq 1 and type eq "psl.2_G") or (p mod 3
  eq 2 and type eq "psl.2_AG") then
    groups:= ImageCopies(so3,3,diag);
    maximals:= maximals cat groups;
  elif type in {"psl.2_A", "psl.2_G", "psl.2_AG", "psl.2^2"} then
    so3:= SelectGroupGeneral(psl,so3,diag,invol);
    Append(~maximals,so3);
  end if;

  if p mod 3 eq 2 then
    Append(~maximals, SU(3, p)@factor);
  elif type in {"psl", "psl.2_G"} then
    groups:= ImageCopies(SU(3,p)@factor,3,diag);
    maximals:= maximals cat groups;
  elif type in {"psl.2_A", "psl.2_AG", "psl.2^2"} then
    su:= SelectGroupGeneral(psl,SU(3,p)@factor,diag,invol);
    Append(~maximals,su);
  end if;

  if Print gt 1 then "getting C_9s"; end if;
  if p mod 15 in {7, 13} then
    a6:= A6(p^2) @ factor;
    if type in {"psl", "psl.2_G"} then 
      groups:= ImageCopies(a6,3,diag);
      maximals:= maximals cat groups;
    elif type in {"psl.2_A", "psl.2_AG", "psl.2^2"} then
      a6:= SelectGroupGeneral(psl,a6,diag,invol);
      Append(~maximals,a6);
    end if;
  elif p mod 15 in {2, 8} then
    a6:= A6(p^2) @ factor;
    if type in {"psl", "psl.2_AG"} then
      groups:= ImageCopies(a6,3,diag);
      maximals:= maximals cat groups;
    elif type in {"psl.2_A", "psl.2_G", "psl.2^2"} then
      a6:= SelectGroupGeneral(psl,a6,diag,invol);
      Append(~maximals,a6);
    end if;
  end if;

  return homom, apsl, maximals, F, phi;
end function;

