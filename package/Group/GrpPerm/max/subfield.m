freeze;

import "spinor.m": InOmega;
import "classicals.m":  NormSpMinusSp, SOMinusOmega, GOMinusSO, NormGOMinusGO;


function SubfieldSL(d, p, e, f : general:=false )
  assert IsPrime(p);
  assert e mod f eq 0;
  assert IsPrime(e div f);

  //first we make the basic group. 
  newgens:= general select [GL(d, p^e)!GL(d, p^f).i : i in [1, 2]]
                      else [GL(d, p^e)!SL(d, p^f).i : i in [1, 2]];

  z:= PrimitiveElement(GF(p^e));
  if general then
    return sub< GL(d,p^e) | newgens, ScalarMatrix(d,z) >;
  end if;

  divisor:= Gcd(p^e-1, d);
  c:= (divisor*Lcm(p^f-1, (p^e-1) div divisor)) div (p^e-1);
  prim_scal:= ScalarMatrix(d, z^((p^e-1) div divisor));
  if c mod Gcd(p^f-1, d) eq 0 then 
    return sub<SL(d, p^e)|newgens, prim_scal>;
  end if;

  mat := Matrix(Integers(),2,1,[d,p^e-1]);
  vec := RSpace(Integers(),1)![c*(p^e-1) div (p^f-1)];
  isc, sol := IsConsistent(mat,vec);
  assert isc;
/*
  assert exists(t){x: x in [1..(p^e-1)div divisor] | ((d div divisor)*x
  - ((p^e-1) div ((Gcd(p^f-1, (p^e-1) div divisor) * divisor)))) mod ((p^e
  - 1) div divisor) eq 0};
  new_scal:= ScalarMatrix(d, z^-t);
*/

  new_scal:= ScalarMatrix(d, z^-sol[1]);
  new_gen := new_scal *
          DiagonalMatrix([z^((p^e-1) div (p^f-1))] cat [1: i in [2..d]])^c;
  assert Determinant(new_gen) eq 1;
  return sub<GL(d, p^e)|newgens, prim_scal, new_gen>;
 
end function;


/********************************************************************/

function SubfieldSp(d, p, e, f : normaliser:=false )
  assert IsPrime(p);
  assert e mod f eq 0;

  newgens:= [GL(d,p^e)!Sp(d, p^f).i : i in [1, 2]];

  z:= PrimitiveElement(GF(p^e));
  norms := GL(d,p^e)!NormSpMinusSp(d,p^f);
  if normaliser then
    return sub<GL(d, p^e) | newgens, norms, ScalarMatrix(d,z) >; 
  end if;

  if IsEven(p) or IsOdd(e div f) then
    return sub<GL(d, p^e)|newgens>;
  end if;
  
  power:= (p^e-1) div (p^f-1);
  assert IsEven(power);
  norm := NormSpMinusSp(d,p^e);
  delta:= norm^power;
  scal_power:= power div 2;
  Append(~newgens, delta*GL(d, p^e)!ScalarMatrix(d, z^-scal_power));
  return sub<GL(d, p^e)|newgens>;
end function; 

/*********************************************************************/

function getextSU(d, p, e, f)
 return ((p^e+1)*Gcd(p^f+1, d)) div (Lcm(p^f+1, (p^e+1) div
  Gcd(p^e+1, d))*Gcd(p^e+1, d));
end function;

/*********************************************************************/

function SubfieldSU(d, p, e, f : general:=false, normaliser:=false)
  assert IsPrime(p);
  assert e mod f eq 0;
  assert IsPrime(e div f);
  assert not IsEven(e div f);//otherwise not a subgroup!

  if normaliser then general:=true; end if;
  //first we make the basic group. 
  newgens:= general select [GL(d, p^(2*e))!GU(d, p^f).i : i in [1, 2]]
             else [SL(d, p^(2*e))!SU(d, p^f).i : i in [1, 2]];

  z:= PrimitiveElement(GF(p^(2*e)));
  if normaliser then
    return sub< GL(d,p^(2*e)) | newgens, ScalarMatrix(d,z) >;
  elif general then
    return sub< GL(d,p^(2*e)) | newgens, ScalarMatrix( d, z^(p^e-1) ) >;
  end if;

  divisor:= Gcd(p^e+1, d);
  c:= (divisor*Lcm(p^f+1, (p^e+1) div divisor)) div (p^e+1);
  //"c mod (p^f+1, d) = ", c mod Gcd(p^f+1, d);

  prim_scal:= ScalarMatrix(d, z^((p^(2*e)-1) div divisor));
  Append(~newgens,prim_scal);

  if c mod Gcd(p^f+1, d) ne 0 then
    mat := Matrix(Integers(),2,1,[d,p^e+1]);
    vec := RSpace(Integers(),1)![c*(p^e+1) div (p^f+1)];
    isc, sol := IsConsistent(mat,vec);
    assert isc;

/*
    assert exists(t){x: x in [1..(p^e+1) div divisor] | (d div divisor)*x
    - ((p^e+1) div (Gcd(p^f+1, (p^e+1) div divisor) * divisor)) mod ((p^e
           + 1) div divisor) eq 0};
    new_scal:= ScalarMatrix(d, z^(t*(p^e-1)));
    new_diag := GL(d, p^(2*e))!(GU(d, p^f).1)^c; 
*/
    new_scal:= ScalarMatrix(d, z^(sol[1] * (p^e-1)) );
    new_gen := new_scal * GL(d, p^(2*e))!(GU(d, p^f).1)^c;
    assert Determinant(new_gen) eq 1;
    Append(~newgens,new_gen);
  end if;

  return sub<SL(d, p^(2*e)) | newgens >;
end function;


/********************************************************************/


function SpInSU(d, q : general:=false, normaliser:=false)
  assert IsEven(d);
  //DFH: corrected bug in defn of norm_elt, 25/10/12
  if normaliser then general:=true; end if;
  z:= PrimitiveElement(GF(q^2));
  
  newgens:= [GL(d, q^2)!Eltseq(Sp(d, q).1), GL(d, q^2)!Eltseq(Sp(d, q).2)];

  /* if IsOdd(q) and (general or (Gcd(q+1, d div 2) eq Gcd(q+1, d)) ) then
    pow :=  (q+1) div 2;
    norm_elt:= Gcd(q+1, d div 2) eq Gcd(q+1, d) select
                 GL(d, q^2)!DiagonalMatrix([z^pow: i in [1..d div 2]]
                                       cat [-z^-pow: i in [1..d div 2]]) else
                 GL(d, q^2)!DiagonalMatrix([z: i in [1..d div 2]]
                                       cat [z^-q: i in [1..d div 2]]);
    Append(~newgens, norm_elt);
   end if; */

  pow :=  (q+1) div GCD(q+1, d div 2);
  norm_elt := general select
                 GL(d, q^2)!DiagonalMatrix([z: i in [1..d div 2]]
                                       cat [z^-q: i in [1..d div 2]]) else
                 GL(d, q^2)!DiagonalMatrix([z^pow: i in [1..d div 2]]
                                       cat [z^(-q*pow): i in [1..d div 2]]);
  Append(~newgens, norm_elt);


  if general then
    grp := sub< GL(d,q^2) | newgens >;
    cmat := TransformForm(grp);
    if normaliser then
      Append( ~newgens, ScalarMatrix(d,z) );
      grp := sub< GL(d,q^2) | newgens >;
    end if;
    return grp^cmat;
  end if;

/* don't need this if we always include norm_elt
  if Gcd(q+1, d) gt 2 then
    m:= Gcd(q+1, d);
    Append(~newgens, ScalarMatrix(d, z^((q^2-1) div m)));
  end if;
*/

  grp:= sub<GL(d, q^2)|newgens>;
 
  if IsEven(q) then
    return grp;
  end if;

  // in the following, f1 is the matrix of the unitary form preserved
  // by Sp, should be able to prove this directly from K+L.
  // f2 is the unitary form preserved by standard SU in magma.
  power:= (q+1) div 2;
  bool, f1:= UnitaryForm(grp);
  f2:= Matrix(GF(q^2), d, d, [<i, d-i+1, 1> : i in [1..d]]);

  mat1:= CorrectForm(f1, d, q^2, "unitary");
  mat2:= CorrectForm(f2, d, q^2, "unitary");
  
  return grp^(mat1*(mat2^-1));
end function;

/*********************************************************************/
//This function makes matrix entries that are needed for the
//normaliser of GO^{+/-}(d, q).
function GetAandB(q)
  z:= PrimitiveElement(GF(q));
  for a in GF(q) do
    bool, b:= IsSquare(z - a^2);
    if bool then
      return a, b;
    end if;
  end for;
end function;

function OrthsInSU(d, q : general:=false, normaliser:=false)   
  //KL have q odd? o.w. normalises symplectic type group
  assert IsOdd(q) or IsEven(d); //o.w. orthogonal group reducible
  if normaliser then general:=true; end if;
  z:= PrimitiveElement(GF(q^2));
  zz := PrimitiveElement(GF(q));
  prim_scal_su:= GL(d, q^2)!ScalarMatrix(d, z^((q^2 - 1) div Gcd(q+1,d) ) );
  prim_scal_gu:= GL(d, q^2)!ScalarMatrix(d, z^(q-1) );
  prim_scal:= GL(d, q^2)!ScalarMatrix(d, z);
  zc := z;
  if zc^(1+q) ne zz then
    isit, zc:=NormEquation(GF(q^2),zz); assert isit; assert zc^(1+q) eq zz;
  end if;
  prim_scal_min:= GL(d, q^2)!ScalarMatrix(d, zc);

  if IsOdd(d) then
    newgens:= [GL(d, q^2)!Eltseq(SO(d, q).1), GL(d, q^2)!Eltseq(SO(d, q).2)]; 
    newgrp := sub<GL(d, q^2)|newgens>;
    isit, form1:= UnitaryForm(newgrp);
    assert isit;
    if normaliser then
      newgrp:= sub< GL(d,q^2) | newgens, prim_scal >;
    elif general then
      newgrp:= sub< GL(d,q^2) | newgens, prim_scal_gu >;
    else
      newgrp:= sub< GL(d,q^2) | newgens, prim_scal_su >;
    end if;
    form2:= Matrix(GF(q^2), d, d, [<i, d-i+1, 1>: i in [1..d]]);
    mat1:= CorrectForm(form1, d, q^2, "unitary");
    mat2:= CorrectForm(form2, d, q^2, "unitary");
    return newgrp^(mat1*mat2^-1);
  end if;

  newgens1:= general select
             [GL(d, q^2)!Eltseq(GOPlus(d, q).i): 
                        i in [1..Ngens(GOPlus(d, q))]] else
             [GL(d, q^2)!Eltseq(SOPlus(d, q).i): 
                        i in [1..Ngens(SOPlus(d, q))]];
  newgens2:= general select
             [GL(d, q^2)!Eltseq(GOMinus(d, q).i) : 
                        i in [1..Ngens(GOMinus(d, q))]] else
             [GL(d, q^2)!Eltseq(SOMinus(d, q).i) : 
                        i in [1..Ngens(SOMinus(d, q))]];

  if IsEven(q) then
    return sub<SL(d, q^2)|newgens1>, sub<SL(d, q^2)|newgens2>;
  end if;

  isit, type, form_minus:= OrthogonalForm(GOMinus(d, q));
  assert isit and type eq "orth-";
  //this will conjugate the group so that it is in the form
  //assumed by Kleidman and Liebeck.
  mat_minus:= CorrectForm(form_minus, d, q, "orth-");
  gominus:= GOMinus(d, q)^mat_minus;
  isit, type, form:= OrthogonalForm(gominus);
  assert isit and type eq "orth-";
  mat_minus:= GL(d,q^2)!mat_minus;
  newgens2:= [g^mat_minus : g in newgens2 ];

  //we need the discriminant to compute the element \delta for minus
  //type groups.
  form :=form[1][1]^-1 * form;
  if form[d][d] eq 1 then
    disc_minus:= "square";
    assert not IsEven((q-1)*d div 4);
  else
    disc_minus:= "nonsquare";
    assert IsEven((q-1)*d div 4);
  end if;

  delta_plus:= (GL(d, q)!DiagonalMatrix([z^(q+1) : i in [1..d div
    2]] cat [1 : i in [1..d div 2]]));
  delta_plus:= GL(d, q^2)!delta_plus;

  a, b:= GetAandB(q);  
  if disc_minus eq "square" then
    delta_minus:= GL(d, q^2)!Matrix(GF(q^2), d, d,
        &cat[[<2*i+1, 2*i+1, a>, <2*i+1, 2*i+2, b>,
         <2*i+2, 2*i+1, b>, <2*i+2, 2*i+2, -a>] : i in [0..((d div 2)-1)]]);
  else
    delta_minus:= GL(d, q^2)!Matrix(GF(q^2), d, d,
       &cat[[<2*i+1, 2*i+1, a>, <2*i+1, 2*i+2, b>,
       <2*i+2, 2*i+1, b>, <2*i+2, 2*i+2, -a>] : i in [0..((d div 2)-2)]]
       cat [<d-1, d, 1>, <d, d-1, zz>]);
  end if;

  y_plus:= delta_plus*prim_scal^-1;
  assert UnitaryForm(sub<GL(d, q^2)|newgens1, y_plus>);
  y_minus:= delta_minus*prim_scal_min^-1;
  assert UnitaryForm(sub<GL(d, q^2)|newgens2, y_minus>);

  if general then
    Append(~newgens1, y_plus);
  elif exists(power_for_y_plus){i : i in [1..q+1] | 
      Determinant(y_plus) eq Determinant(prim_scal^(i*(q-1)))} then
    final_plus:= y_plus*prim_scal^(-power_for_y_plus*(q-1));
    Append(~newgens1, final_plus);
  elif exists(power_for_y_plus){i : i in [1..q^2-1] | 
     Determinant(y_plus*GL(d, q^2)!GOPlus(d, q).4) eq 
                            Determinant(prim_scal^(i*(q-1)))} then
     final_plus:= y_plus*GL(d, q^2)!GOPlus(d, q).4*
                 prim_scal^(-(q-1)*power_for_y_plus);
     Append(~newgens1, final_plus);
  else
    assert exists(power_for_y_plus){i : i in [1..q+1] |
      Determinant(prim_scal^(i*(q-1))) eq GF(q^2)!Determinant(GOPlus(4, q).4)};
    final_plus:= GL(d, q^2)!GOPlus(d, q).4*
                                       prim_scal^(-(q-1)*power_for_y_plus);
    Append(~newgens1, final_plus);
  end if;
    
  if general then
    Append(~newgens2, y_minus);
  elif exists(power_for_y_minus){i : i in [1..q+1] | 
      Determinant(y_minus) eq Determinant(prim_scal^(i*(q-1)))} then
    final_minus:= y_minus*prim_scal^(-power_for_y_minus*(q-1));
    Append(~newgens2, final_minus);
  elif exists(power_for_y_minus){i : i in [1..q^2-1] | 
     Determinant(y_minus*GL(d, q^2)!gominus.4) eq 
                            Determinant(prim_scal^(i*(q-1)))} then
     final_minus:= y_minus*GL(d, q^2)!gominus.4*
                 prim_scal^(-(q-1)*power_for_y_minus);
     Append(~newgens2, final_minus);
  else
    assert exists(power_for_y_minus){i : i in [1..q+1] |
    Determinant(prim_scal^(i*(q-1))) eq GF(q^2)!Determinant(gominus.4)};
    final_minus:= GL(d, q^2)!gominus.4*
                 prim_scal^(-(q-1)*power_for_y_minus);
    Append(~newgens2, final_minus);
  end if;
      
  grp2:= sub<GL(d, q^2)|newgens2>;
  bool, f:= UnitaryForm(grp2);
  assert bool;
  bool, f2:= UnitaryForm(GU(d, q));
  assert bool;
  m1:= GL(d, q^2)!CorrectForm(f, d, q^2, "unitary");
  m2:= GL(d, q^2)!CorrectForm(f2, d, q^2, "unitary");
  if normaliser then
    grp1:= sub< GL(d,q^2) | newgens1, prim_scal >;
    grp2:= sub< GL(d,q^2) | newgens2, prim_scal >;
  elif general then
    grp1:= sub< GL(d,q^2) | newgens1, prim_scal_gu >;
    grp2:= sub< GL(d,q^2) | newgens2, prim_scal_gu >;
  else
    grp1:= sub< GL(d,q^2) | newgens1, prim_scal_su >;
    grp2:= sub< GL(d,q^2) | newgens2, prim_scal_su >;
  end if;

  grp2:= grp2^(m1*m2^-1);
    
  return grp1, grp2;
end function;

function SubfieldOdimOdd(d, p, e, f :
                       special:=false, general:=false, normaliser:=false)
  assert IsPrime(p);
  assert e mod f eq 0;
  assert IsPrime(e div f);
  assert IsOdd(d) and IsOdd(p);

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  x := general select GO(d,p^f) else
      (special or e div f eq 2) select SO(d,p^f) else Omega(d,p^f);

  gens := [GL(d,p^e)!x.i : i in [1..Ngens(x)]];

  if normaliser then
    Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(p^e)) ) );
  end if;

  return sub< GL(d,p^e) | gens >;

  //if e/f = 2, c=2, so; o.w. c=1
end function;

function SubfieldOdimEven(d, p, e, f, sign1 :
                       special:=false, general:=false, normaliser:=false)
  local r, grp, grp1, mat, ggl, gol, w;
  assert IsPrime(p);
  assert e mod f eq 0;
  assert IsPrime(e div f);
  assert sign1 in {-1,1};
  assert IsEven(d);

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  r := e div f;
  z := PrimitiveElement(GF(p^e));
  if IsOdd(r) or p eq 2 then
    if general then
      grp := sign1 eq 1 select GOPlus(d,p^f) else GOMinus(d,p^f);
    elif special then
      grp := sign1 eq 1 select SOPlus(d,p^f) else SOMinus(d,p^f);
    else
      grp := sign1 eq 1 select OmegaPlus(d,p^f) else OmegaMinus(d,p^f);
    end if;
    grp1 := sub< GL(d,p^e) | [GL(d,p^e)!grp.i : i in [1..Ngens(grp)]] >;
    mat := TransformForm(grp1);
    if normaliser then
      if IsOdd(p) then
        grp1 := sub< GL(d,p^e) | grp1, GL(d,p^e)!NormGOMinusGO(d,p^f,sign1) >;
      end if;
      grp1 := sub< GL(d,p^e) | grp1, ScalarMatrix(d,z) >;
    end if;
    return grp1^mat;
  end if;

  q := p^f;
  if general then
    grp := sign1 eq 1 select GOPlus(d,q) else GOMinus(d,q);
  else
    grp := sign1 eq 1 select SOPlus(d,q) else SOMinus(d,q);
  end if;
  grp1 := sub< GL(d,p^e) | [GL(d,p^e)!grp.i : i in [1..Ngens(grp)]] >;
  mat := TransformForm(grp1);
  grp1 := grp1^mat;
  if  not special and
     ( (d mod 4 eq 0 and sign1 eq -1) or
       (d mod 4 eq 2 and
       ((q mod 4 eq 1 and sign1 eq 1) or (q mod 4 eq 3 and sign1 eq -1)))) then
    return grp1;
  end if;

  //otherwise adjoin element from NGO-GO
  ggl := (GL(d,p^e)!GOMinusSO(d, q, sign1))^mat;
  gol := (GL(d,p^e)!NormGOMinusGO(d, q, sign1))^mat;
  //multiply by scalars to fix form
  w := GF(p^e)!PrimitiveElement(GF(q));
  gol *:= GL(d,p^e)!ScalarMatrix(GF(p^e), d, Root(w,2)^-1);
  if Determinant(gol) ne 1 then gol *:= ggl; end if;
  assert special or InOmega(gol, d, p^e, 1);
  if normaliser then
    return sub< GL(d,p^e) | grp1, gol, ScalarMatrix(d,z) >;
  end if;
  return sub< GL(d,p^e) | grp1, gol >;

  //if e/f odd or p=2,  c=1
  //o.w. 4|d, sign1 = -1 or d=2 mod 4 and
  //          (q mod 4 = 1, sign1=1 or q mod 4 = 3, sign1 = -1) c=2, ngo-go,
  //o.w. c=4, so + ngo-go
end function;
