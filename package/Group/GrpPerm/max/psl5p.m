freeze;
 
/*
This file contains functions called:
PSL2_11(p)
U4_2(p)
M11()
L5pIdentify(group, p)
*/

import "gl2.m": PGammaL2;
import "reds.m": SLPointStab, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
                 SLStabOfNSpaceMissDual;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "normes.m": NormaliserOfExtraSpecialGroup;
import "select_conj.m": ImageCopies, SelectGroupGeneral;
import "psl2q.m": MakeHomomGeneral;


/****************************************************************/
// makes a C_9 group whenever (-11) is square mod p.
function PSL2_11(p)
  bool, i11:= IsSquare(GF(p)!(-11));
  if not bool then
    "error: -11 not square in GF(", p, ")";
    return false;
  end if;   
 
  b11 := (-1+i11)/2;
  A := Matrix(GF(p), 5, 5, [
		1,0,0,0,0,
		1,-1,b11,0,0,
		0,0,1,0,0,
		-1,0,-1,-1,b11,
		0,0,0,0,1]);
   B := Matrix(GF(p), 5, 5, [
		b11,-b11,-1,b11+1,2,
		0,-1,-1,0,0,
		0,1,0,0,0,
		1,0,0,0,0,
		1,-b11-1,0,2,-b11]);
   psl2_11:= sub<SL(5, p)| A, B>;
	
   return psl2_11;
end function;

/****************************************************************/
//makes C_9 group U(4, 2) whenever cube root of unity exists.
function U4_2(p)
  assert p mod 6 eq 1;
  z:= PrimitiveElement(GF(p));
  w:= z^((p-1) div 3);
  a:= GL(5, p)![ 1, -w^2, 0, -w^2,  1,
                -w,    1, 0,   -1,  w,
                 0,    0, 2,    0,  0,
                -w,   -1, 0,    1,  w,
                 1,  w^2, 0,  w^2,  1];
  b:= GL(5, p)![1,  0,  1, -w, -w,
                0,  2,  0,  0,  0,
                1,  0,  1,  w,  w,
             -w^2,  0,w^2,  1, -1,
             -w^2,  0,w^2,  -1, 1];
  c:= GL(5, p)![2,  0, 0,  0, 0,
                0,  1,-w, -w,-1,
                0,-w^2,1, -1,-w^2,
                0,-w^2,-1, 1,-w^2,
                0, -1,-w, -w, 1];
  d1:= GL(5, p)!DiagonalMatrix([-1, 1, 1, 1, 1]);
  d2:= GL(5, p)!DiagonalMatrix([1, -1, 1, 1, 1]);
  d3:= GL(5, p)!DiagonalMatrix([1, 1, -1, 1, 1]);
  d4:= GL(5, p)!DiagonalMatrix([1, 1, 1, -1, 1]);
  d5:= GL(5, p)!DiagonalMatrix([1, 1, 1, 1, -1]);
  
  g:= sub<GL(5, p)|a, b, c, d1, d2, d3, d4, d5>;
  return DerivedSubgroup(g);
end function;

/***********************************************************/
//Makes M_11 \leq SL(5, 3).
function M11()
  a:= GL(5, 3)![0,2,1,0,0,
                2,1,1,2,2,
                0,1,1,2,2,
                1,0,2,2,1,
                1,2,2,2,0];
  b:= GL(5, 3)![0,0,2,0,2,
                1,1,2,2,0,
                2,2,2,2,2,
                1,2,1,1,0,
                2,2,0,2,1];
  return sub<SL(5, 3)|a, b>;
end function;

/***************************************************************
 *
 * Now the main function; I haven't bothered splitting it into
 * Coprime and Noncoprime as the behaviour of the subgroups is
 * not enormously complicated in any case.
 */

function L5pIdentify(group, p: max:= true, Print:=0)
  assert IsPrime(p);
 
  if p mod 5 eq 1 then
    coprime:= false;
  else
    coprime:= true;
  end if;

  o:= Order(group);

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(5,p);
  sl := SL(5,p);
  apsl := PGammaL2(5,p);
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;
  diag := GL(5,p).1 @ factor;

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group :=
      MakeHomomGeneral(group, 5, p, 1, psl, apsl, factor : Print:=0);

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psl | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);
  if Print gt 1 then print "Identifying group"; end if;
  // Also get the generators of apsl correct
  newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];

  image := Image(homom);
  invol := apsl.3;
  if coprime then
    if image eq psl then type := "psl";
      apsl := sub< apsl | newgens  cat [apsl.3] >;
    else assert image eq apsl; type := "psl.2";
      apsl := sub< apsl | newgens >;
    end if;
  elif image eq psl then type := "psl";
      apsl := sub< apsl | newgens  cat [apsl.1,apsl.3] >;
  elif #image eq 2* #psl then type := "psl.2";
      apsl := sub< apsl | newgens  cat [apsl.1] >;
      invol := group.(Ngens(group)) @ homom;
  elif #image eq 5* #psl then type := "psl.5";
      apsl := sub< apsl | newgens  cat [apsl.3] >;
  else  assert image eq apsl; type := "aut_psl";
   apsl := sub< apsl | newgens >;
  end if;
  if Print gt 1 then print "Type = ",type; end if;

  maximals:= [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  /*
   * Reducible - if we have psl or psl.5 then we get 4
   * classes of point stabiliser, conjugate in pairs under
   * inverse transpose. Otherwise, we get 4 novelties. 
   */
  if Print gt 1 then print "getting reducibles"; end if;
  if type in {"psl", "psl.5"} then
    Append(~maximals,  SLPointStab(5, p)@factor);
    for i in [2, 3, 4] do 
      Append(~maximals,SLStabOfNSpace(5,p,i)@factor);
    end for;
  else 
    for i in [1, 2] do
      Append(~maximals,SLStabOfNSpaceMeetDual(5, p, i)@factor);
      Append(~maximals,SLStabOfNSpaceMissDual(5, p, i)@factor);
    end for;
  end if;

  if p gt 3 then
    if Print gt 1 then print "getting imprimitives"; end if;
    Append(~maximals, ImprimsMeetSL(5, p, 5)@factor);
  end if;

  if Print gt 1 then print "getting semilinears"; end if;
  Append(~maximals, GammaLMeetSL(5, p, 5)@factor);

  if not coprime then
     ext:= NormaliserOfExtraSpecialGroup(5, p);
     ext1:= sub<ext|[ext.i : i in [1..Ngens(ext)]| Determinant(ext.i)eq 1]>;

    //ext1:= NormaliserOfExtraSpecialGroupSL(5, p);
    if type eq "psl" then
      if Print gt 1 then print "getting extraspecials"; end if;
      maximals:= maximals cat ImageCopies(ext1@factor,5,diag);
    elif type eq "psl.2" then
      if Print gt 1 then print "getting extraspecials"; end if;
      ext1:= SelectGroupGeneral(psl,ext1@factor,diag,invol);
      Append(~maximals, ext1);
    end if;
  end if;

  if p gt 2 then
    so5:= SO(5, p) @ factor;
    if coprime then
      if Print gt 1 then print "getting orthogonals"; end if;
      Append(~maximals, so5);
    elif type eq "psl" then
      if Print gt 1 then print "getting orthogonals"; end if;
      maximals:= maximals cat ImageCopies(so5,5,diag);
    elif type eq "psl.2" then 
      if Print gt 1 then print "getting orthogonals"; end if;
      so5:= SelectGroupGeneral(psl,so5,diag,invol);
      Append(~maximals, so5); 
    end if;
  end if;

  if Print gt 1 then print "getting C_9s"; end if;
  if p gt 3 and not p eq 11 and IsSquare(GF(11)!p) then
    l2_11:= PSL2_11(p)@factor;
    if coprime then
      Append(~maximals, l2_11);
    elif type eq "psl" then
      maximals:= maximals cat ImageCopies(l2_11,5,diag);
    elif type eq "psl.2" then 
      l2_11 := SelectGroupGeneral(psl,l2_11,diag,invol);
      Append(~maximals, l2_11); 
    end if;
  end if;

  if p gt 2 and p mod 6 eq 1 then 
    u42:= U4_2(p)@factor;
    if coprime then
      Append(~maximals, u42);
    elif type eq "psl" then
      maximals:= maximals cat ImageCopies(u42,5,diag);
    elif type eq "psl.2" then 
      u42 := SelectGroupGeneral(psl,u42,diag,invol);
      Append(~maximals, u42); 
    end if;
  end if;

  if p eq 3 and type eq "psl" then
    m11:= M11();
    Append(~maximals, m11@factor);
    Append(~maximals,
            sub<SL(5,p)|Transpose(m11.-1), Transpose(m11.-2)>@factor );  
  end if;

  if p eq 3 and type eq "psl.2" then  //NOVELTY!!!
    if Print gt 1 then print "getting novelty"; end if;
    Append(~maximals, PSL2_11(3)@factor);
  end if;

  return homom, apsl, maximals, F, phi;
end function;

