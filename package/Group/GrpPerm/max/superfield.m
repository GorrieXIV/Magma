freeze;

import "imp_and_gamma.m" : GammaL1;
import "spinor.m": InOmega;
import "classicals.m": NormSpMinusSp, SOMinusOmega, GOMinusSO, NormGOMinusGO;

MatToQ := function(A,q)
// raise every element of matrix A to q-th power
  local B;
  B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
  for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
    B[i][j] := A[i][j]^q;
  end for; end for;
  return B;
end function;

function mylog(z,x)
  if x eq 0 then
    return -1;
  else 
    return Log(z,x);
  end if;
end function;

/*****************************************************************/
//This makes a block matrix, with all blocks either zero or powers of
//block_matrix, where the (i, j)-th block is block_matrix^i iff
//source_matrix[i][j] = z^i.

function BlockPowers(block_matrix, source_matrix, pow : prim := false)
  dim:= Nrows(source_matrix);
  zero:= Matrix(BaseRing(block_matrix), Nrows(block_matrix),
         Nrows(block_matrix), []);
  mats:= [* *];

  K := BaseRing(source_matrix);
  if prim then
    z := PrimitiveElement(K);
  else
    mp := MinimalPolynomial(block_matrix);
    mpp := PolynomialRing(K)!mp;
    z := Roots(mpp)[1][1];
  end if;
  for i in [1..dim] do
    for j in [1..dim] do
      power:= mylog(z,source_matrix[i][j]);
      if power eq -1 then Append(~mats, zero); 
      else Append(~mats, block_matrix^(power*pow));
      end if;
    end for;
  end for;

  for i in [1..dim] do
      rowmat:= mats[(i-1)*dim + 1];
    for j in [2..dim] do
      rowmat:= HorizontalJoin(rowmat, mats[(i-1)*dim + j]);
    end for;
    if i eq 1 then
      final:= rowmat;
    else
      final:= VerticalJoin(final, rowmat);
    end if;
  end for;

  return final;
end function;

/***************************************************************/
//Makes Sp(d/s, q^s).s \leq Sp(d, q).

function GammaSp(d, q, s : normaliser:=false )
  assert d mod s eq 0;
  dim:= d div s;
  assert IsEven(dim);  //else Sp(dim, q^s) does not exist.

  gammal1:= GammaL1(s, q);
  singer:= gammal1.1;
  frob:= gammal1.2;
  sp1:= Sp(dim, q^s).1;
  sp2:= Sp(dim, q^s).2; 

  //"putting singer cycle as block into gens for Sp(dim, p)";
  //we use the fact that Sp(d, q).1 is Diag[z, 1, \ldots, z^-1]
  A:= BlockPowers(singer, sp1, 1);
  B:= BlockPowers(singer, sp2, 1);
  C:= DiagonalJoin([frob: i in [1..dim]]);
  grp:=  sub<SL(d, q)|A, B, C>;

  bool, form:= SymplecticForm(grp);
  assert bool;
  mat:= CorrectForm(form, d, q, "symplectic");
  if normaliser then
    grp := sub< GL(d,q) | grp, NormSpMinusSp(d, q) >;
  end if;
  return grp^mat;
end function;

/**************************************************************/

function GammaUMeetSp(d, q : normaliser:=false)
  //assert IsOdd(q); orthogonal
  half:= d div 2;
  gammal1:= GammaL1(2, q);
  epsilon:= gammal1.1;
  frob:= gammal1.2;
  //"frob is", frob;
  zero:= Matrix(GF(q), 2, 2, []);
  
  gu1:= GU(half, q).1;
  gu2:= GU(half, q).2;

  //first we make a group isomorphic to GU(half, q).
  A:= GL(d, q)!BlockPowers(epsilon, gu1, 1);
  B:= GL(d, q)!BlockPowers(epsilon, gu2, 1);
  gu:= sub<GL(d, q)|A, B>;

  //now we want to extend by the field automorphism x->x^q,
  //multiplied by whatever power of epsilon will give it 
  //determinant 1, as an element of GL(2, q).
  frob_diag:= DiagonalJoin([frob : i in [1..half]]);
  //we have to multiply the frobenius thingy by a "scalar" to get 
  //it to have determinant 1 on each block.
  fac:= Factorisation(q+1);
  if IsOdd(q) then
    two_power:= 2^fac[1][2]; //safe because q must be odd.
  else two_power:= 1;
  end if;
  power:= (q^2 - 1) div (two_power*2);
  mock_scalar:= epsilon^power;
  //"mock_scalar is", mock_scalar;
  frob_scal:= DiagonalJoin([mock_scalar : i in [1..half]]); 
  C:= frob_diag*frob_scal;
  //following assertion is only in for testing purposes.
  //assert not C in gu;

  grp:=  sub<GL(d, q)|gu, C>;

  bool, f:= SymplecticForm(grp);
  assert bool;
  //"original form is", f;
  conjmat:= GL(d, q)!CorrectForm(f, d, q, "symplectic");
  if normaliser then
    z:= PrimitiveElement(GF(q^2));
    sc := ScalarMatrix(half,z);
    grp := sub< GL(d,q) | grp, GL(d, q)!BlockPowers(epsilon, sc, 1) >;
  end if;
  return grp^conjmat;  

end function;

/**********************************************************************/
function ConjIntoSU(grp, d, q)
  bool, f:= UnitaryForm(grp);
  assert bool;
  //"f =", f;
  mat1:= CorrectForm(f, d, q^2, "unitary");
  bool, f2:= UnitaryForm(SU(d, q));
  mat2:= CorrectForm(f2, d, q^2, "unitary");
  return GL(d, q^2)!mat1*GL(d, q^2)!mat2^-1;
end function;

/***********************************************************************/

function GammaSU(d, q, s : general:=false, normaliser:=false)
  fac:= Factorisation(q);
  assert #fac eq 1;
  assert d gt 2;
  assert d mod s eq 0;
  assert not s eq 2; //o.w. don't get subgroup 
  if not IsPrime(s) then
    "warning: this function was designed for PRIME field extensions";
  end if;
  if normaliser then general:=true; end if;
 
  dim:= d div s;

  gammal1:= GammaL1(s, q^2);
  singer:= gammal1.1;
  singerGU:= singer^(q^s-1); //has order (q^s+1).
  //"Order(Det(singerGU))=", Order(Determinant(singerGU));
  singerSU:= singerGU^(q+1); //|Det(GU)| = q+1;
  //"Order singer SU = ", Order(singerSU);

  frob:= gammal1.2;

  if dim eq 1 then
     grp:= general select sub<GL(d, q^2)|singerGU, frob>
                     else sub<GL(d, q^2)|singerSU, frob>;
     mat:= ConjIntoSU(grp, d, q);
     if normaliser then
       z:=PrimitiveElement(GF(q^2)); sc:=ScalarMatrix(d,z);
       grp := sub< GL(d,q^2) | grp, sc >;
     end if;
     return grp^mat; 
  end if;

  su1:= SU(dim, q^s).1;
  su2:= SU(dim, q^s).2;
  gu1:= GU(dim, q^s).1; 

  sugen1:= BlockPowers(singer, su1, 1);
  sugen2:= BlockPowers(singer, su2, 1);
  detmat:= general select BlockPowers(singer, gu1, 1)
                     else BlockPowers(singer, gu1, q+1);
  frobmat:= DiagonalJoin([frob : i in [1..dim]]);

  grp:= sub<GL(d, q^2)|sugen1, sugen2, detmat, frobmat>;
  mat:= ConjIntoSU(grp, d, q);
  if normaliser then
    z:=PrimitiveElement(GF(q^2)); sc:=ScalarMatrix(d,z);
    grp := sub< GL(d,q^2) | grp, sc >;
  end if;
  return grp^mat;  
end function;

/***************************************************************/
//Make O^e(d/s, q^s).s \leq O^e(d, q).
//It is convenient to split into various cases.

function GammaOsOdd(d, q, s, sign :
                     special:=false, general:=false, normaliser:=false)
  assert d mod s eq 0;
  assert (IsOdd(d) and sign eq 0) or (IsEven(d) and sign in {-1,1});
  assert IsEven(d) or IsOdd(q);
  assert IsOdd(s);

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  dim:= d div s;
  assert dim gt 1;
  sign1 := IsEven(dim) select sign else 0;

  go1 := sign1 eq 0 select GO(dim,q^s) else
         sign1 eq 1 select GOPlus(dim,q^s) else GOMinus(dim,q^s);
  so1 := sign1 eq 0 select SO(dim,q^s) else
         sign1 eq 1 select SOPlus(dim,q^s) else SOMinus(dim,q^s);
  om1 := sign1 eq 0 select Omega(dim,q^s) else
         sign1 eq 1 select OmegaPlus(dim,q^s) else OmegaMinus(dim,q^s);

  //In the minus case we need to conjugate to get the form fixed to be in the
  //subfield
  if sign eq -1 then 
    if IsEven(q) then
      isf, form1 := QuadraticForm(go1);
      isf, forms := QuadraticForm(GOMinus(dim,q));
      forms := MatrixAlgebra(GF(q^s),dim)!forms;
    else
      isf, form1 := SymmetricBilinearForm(go1);
      isf, forms := SymmetricBilinearForm(GOMinus(dim,q));
      forms := MatrixAlgebra(GF(q^s),dim)!forms;
    end if;
    cmat1 := CorrectForm(form1,dim,q^s,"orth-");
    cmat2 := CorrectForm(forms,dim,q^s,"orth-");
    tmat := GL(dim,q^s)!(cmat1*cmat2^-1);
    go1 := go1^tmat;
    so1 := so1^tmat;
    om1 := om1^tmat;
  end if;

  gammal1:= GammaL1(s, q);
  singer:= gammal1.1;
  frob:= gammal1.2;

  gens := [ BlockPowers(singer, om1.i, 1) : i in [1..Ngens(om1)] ];
  sgens := [ BlockPowers(singer, so1.i, 1) : i in [1..Ngens(so1)] ];
  ggens := [ BlockPowers(singer, go1.i, 1) : i in [1..Ngens(go1)] ];
  frobgen:= DiagonalJoin([frob: i in [1..dim]]);
  grp:=  sub<SL(d, q)| gens, frobgen>;
  sgrp:=  sub<SL(d, q)| sgens, frobgen>;
  ggrp:=  sub<GL(d, q)| ggens, frobgen>;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(ggrp);
  if normaliser then
    if IsEven(d) and IsOdd(q) then
      ngo1 := GL(dim,q^s)!NormGOMinusGO(dim,q,sign);
      ggrp := sub<GL(d,q) | ggrp, BlockPowers(singer,ngo1,1) >;
    elif q gt 3 then
      z := PrimitiveElement(GF(q));
      ggrp := sub<GL(d,q) | ggrp, ScalarMatrix(d,z)>;
    end if;
  end if;
  if general then return ggrp^tmat; end if;
  if special then return sgrp^tmat; end if;
  return grp^tmat;

end function;

function GammaOdimOdd(d, q, sign :
                     special:=false, general:=false, normaliser:=false)
  assert IsEven(d) and sign in {-1,1};
  assert IsOdd(q);
  s := 2;
  dim:= d div s;
  assert IsOdd(dim);

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  sign1 := 0;

  absirred := (sign eq 1 and q mod 4 eq 1) or (sign eq -1 and q mod 4 eq 3);
  //in these cases group constructed will be absolutely irreducible
  //equivalent to D = square (KL).

  go1 := GO(dim,q^s);
  so1 := SO(dim,q^s);
  om1 :=  Omega(dim,q^s);

  gammal1:= GammaL1(s, q);
  singer:= gammal1.1;
  frob:= gammal1.2;

  gens := [ GL(d,q) | BlockPowers(singer, om1.i, 1) : i in [1..Ngens(om1)] ];
  frobgen:= DiagonalJoin([frob: i in [1..dim]]); //det = -1
  scal := ScalarMatrix( GF(q^2), dim, PrimitiveElement(GF(q^2)) );
  if absirred then
    //frobgen has determinant -1, so we need to multiply by a scalar in GF(q^2)
    scal2 := BlockPowers(singer, scal, 1);
    det := Determinant(scal2);
    scal2 := scal2^(Order(det) div 2);
    frobgen := frobgen*scal2;
    //get rid of any odd parts of frobgen
    ord := Order(frobgen);
    assert fac[1][1]^fac[1][2] eq 4 where fac := Factorisation(ord);
    frobgen := frobgen^(ord div 4);
  end if;
  ggrp:=  sub<GL(d, q)| gens, frobgen>;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(ggrp);
  gens := [g^tmat : g in gens];

  //locate an element in SO(dim,q^2) - Omega(dim,q^2).
  gsl := SOMinusOmega(dim, q^2, sign1);
  gsl2 := GL(d,q)!BlockPowers(singer, gsl, 1);
  gsl2 := gsl2^tmat;
  frobgen := (GL(d,q)!frobgen)^tmat;
  if absirred then
    if not InOmega(frobgen,d,q,sign) then
      //"adjusted frobgen";
      frobgen *:= gsl2;
    end if;
    assert InOmega(frobgen,d,q,sign);
    Append(~gens,frobgen);
    if special then Append(~gens,gsl2); end if;
  else
    m1 := ScalarMatrix(d, GF(q)!(-1));
    if not InOmega(gsl2,d,q,sign) then
      //"sign wrong";
      gsl2 := m1 * gsl2;
    end if;
    assert InOmega(gsl2,d,q,sign);
    Append(~gens,gsl2);
    if special then Append(~gens, m1); end if;
    if general then Append(~gens, frobgen); end if;
  end if;
  if normaliser then
    ngo := BlockPowers(singer, scal, 1);
    ngo := (GL(d,q)!ngo)^tmat;
    ngo := ngo ^ ((q+1) div 2);
    Append(~gens, ngo);
  end if;

  return sub< GL(d,q) | gens >;
  //if abs irred then c=2, go; o.w. c=1.

end function;

function GammaOdimEven(d, q, sign :
                     special:=false, general:=false, normaliser:=false)
  assert IsEven(d) and sign in {-1,1};

  s := 2;
  dim:= d div s;
  assert IsEven(dim);

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  sign1 := sign;

  biggp1 := sign1 eq 1 select GOPlus(dim,q^s) else GOMinus(dim,q^s);
  gp1 := sign1 eq 1 select OmegaPlus(dim,q^s) else OmegaMinus(dim,q^s);

  //In the -1 case, the field automorphism will change the form, so
  //we will need to conjugate it back.
  if sign eq -1 then
    if IsEven(q) then
      isf, form := QuadraticForm(biggp1);
    else
      isf, form := SymmetricBilinearForm(biggp1);
    end if;
    cform := MatToQ(form,q);
    cmat1 := TransformForm(cform,"orth-");
  end if;
  
  //We need elements of ggl, gsl in sl-omega
  gsl := SOMinusOmega(dim, q^2, sign1);
  if IsOdd(q) then
    ggl := GOMinusSO(dim, q^2, sign1);
  end if;

  gammal1:= GammaL1(s, q);
  singer:= gammal1.1;
  frob:= gammal1.2;

  gens := [ GL(d,q) | BlockPowers(singer, gp1.i, 1 ) :
                                                    i in [1..Ngens(gp1)] ];
  biggens := [ BlockPowers(singer, biggp1.i, 1 ) :
                                               i in [1..Ngens(biggp1)] ];
  gsl2 := GL(d,q)!BlockPowers(singer, gsl, 1 );
  if IsOdd(q) then
    ggl2 := GL(d,q)!BlockPowers(singer, ggl, 1 );
  end if;
  frobgen:= GL(d,q)!DiagonalJoin([frob: i in [1..dim]]);
  if sign eq -1 then
    frobgen := frobgen * GL(d,q)!BlockPowers(singer, cmat1, 1 );
    assert Determinant(frobgen) eq GF(q)!(-1);
    // not really why that works - must be just the way TransformForm works.
  end if;
  biggrp:=  sub<GL(d, q)| biggens, frobgen>;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(biggrp);
  cgens := [ g^tmat : g in gens ];

  gsl2 := gsl2^tmat;
  //find extra generator in Omega
  if IsOdd(q) then
    ggl2 := ggl2^tmat;
    if InOmega(ggl2,d,q,sign) then
      Append(~cgens,ggl2);
    else assert InOmega(ggl2*gsl2,d,q,sign);
      Append(~cgens,ggl2*gsl2);
    end if;
    if special then
      Append(~cgens,gsl2);
    end if;
  else assert InOmega(gsl2,d,q,sign);
      Append(~cgens,gsl2);
  end if;
  frobgen := frobgen^tmat;
  if sign eq 1 then
    //need Frobenius generator also
    if InOmega(frobgen,d,q,sign) then
      Append(~cgens,frobgen);
    else assert InOmega(frobgen*gsl2,d,q,sign);
      Append(~cgens,frobgen*gsl2);
    end if;
  elif general or (special and IsEven(q)) then
    Append(~cgens,frobgen);
  end if;

  if normaliser then
    if IsOdd(q) then
      scal := ScalarMatrix( GF(q^2), dim, PrimitiveElement(GF(q^2)) );
      ngo := BlockPowers(singer, scal, 1);
      ngo := (GL(d,q)!ngo)^tmat;
      ngo := ngo ^ ((q+1) div 2);
      Append(~cgens,ngo);
    elif q gt 2 then
      z := PrimitiveElement(GF(q));
      Append(~cgens, ScalarMatrix(d,z));
    end if;
  end if;

  return sub<GL(d, q)| cgens >;
  //if sign=1, c=2, so (q even) or go (q odd); o.w. c=1.

end function;


/* Here is a function to compute the field automorphism of OmegaMinus(d,q^2)
 * May need it some time.
FFSOM := function(d,q)
  local Om, cmat1, cmat2, isf, form, formt, cOm, cOmT, tmat;
  Om := OmegaMinus(d,q^2);
  if IsEven(q) then
    isf, form := QuadraticForm(Om);
  else
    isf, form := SymmetricBilinearForm(Om);
  end if;
  cmat1 := CorrectForm(form,d,q^2,"orth-");
  cOm := Om^cmat1;
  cOmT :=  sub< GL(d,q^2) | [MatToQ(cOm.i, q) : i in [1..Ngens(cOm)]] >;
  if IsEven(q) then
    isf, formt := QuadraticForm(cOmT);
  else
    isf, formt := SymmetricBilinearForm(cOmT);
  end if;
  cmat2 := CorrectForm(formt,d,q^2,"orth-");
  tmat := cmat2*cmat1^-1;
  return hom< Om -> Om |
             [ tmat^-1*MatToQ(cOm.i, q)*tmat : i in [1..Ngens(Om)]] >;
end function;
*/

/**************************************************************/

function GammaUMeetOmega(d, q :
                     special:=false, general:=false, normaliser:=false)
  assert IsEven(d);

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  half:= d div 2;
  sign := IsEven(half) select 1 else -1;
  gammal1:= GammaL1(2, q);
  epsilon:= gammal1.1;
  frob:= gammal1.2;
  zero:= Matrix(GF(q), 2, 2, []);

  gu1:= GU(half, q).1;  //generates GU mod SU
  su1:= SU(half, q).1;
  su2:= SU(half, q).2;

  gu1e:= GL(d, q)!BlockPowers(epsilon, gu1, 1);
  su1e:= GL(d, q)!BlockPowers(epsilon, su1, 1);
  su2e:= GL(d, q)!BlockPowers(epsilon, su2, 1);
  //all of the above have determinant 1

  //now we want to extend by the field automorphism x->x^q,
  frob_diag:= GL(d,q)!DiagonalJoin([frob : i in [1..half]]);
  //This already seems to fix the right type of form - it has determinant
  //-1 (or is in SO-Omega when q=2) when half is odd. 
  grp := sub<GL(d, q)|gu1e, su1e, su2e, frob_diag>;
  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(grp);

  //Now just need to intersect with Omega.
  gens := [ g^tmat : g in [su1e, su2e] ];
  x := gu1e^tmat;
  assert Determinant(x) eq 1;
  if special then
    Append(~gens,x);
  elif InOmega(x,d,q,sign) then
    assert IsEven(q);
    Append(~gens,x);
  else assert(InOmega(x^2,d,q,sign));
    assert IsOdd(q);
    Append(~gens,x^2);
  end if;

  frob_diag := frob_diag^tmat;
  if sign eq 1 then
    if special or InOmega(frob_diag,d,q,sign) then
      Append(~gens,frob_diag);
    else assert(InOmega(x*frob_diag,d,q,sign));
      Append(~gens,frob_diag*x);
    end if;
  elif (general and IsOdd(q)) or (special and IsEven(q)) then
    Append(~gens,frob_diag);
  end if;
  if normaliser then
    gun:= ScalarMatrix(half, PrimitiveElement(GF(q^2)) );
    gune:= GL(d, q)!BlockPowers(epsilon, gun, 1);
    Append(~gens,gune^tmat);
  end if;

  return sub< GL(d,q) | gens >;
  //if sign=1 (i.e. half even), c=2 so(q even ) go(q odd); o.w. c=1.
end function;
