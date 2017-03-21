freeze;

import "classicals.m": SOMinusOmega, GOMinusSO, NormGOMinusGO;
import "spinor.m": InOmega;

function IsotropicStabOmega(d, q, k, sign : special:=false, general:=false,
                                            normaliser:=false )
/*
 * Here we stabilise <e_1, \ldots, e_k>, k \leq d/2;
 */
  local t,u,v,x,y,z,go;
  assert d gt 2;
  assert (IsOdd(d) and sign eq 0) or (IsEven(d) and sign in {-1,1});
  assert IsEven(d) or IsOdd(q);
  assert 2*k le d;
  assert sign ne -1 or 2*k ne d;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  if IsOdd(d) then Om := Omega;
  elif sign eq 1 then Om := OmegaPlus;
  else Om := OmegaMinus;
  end if;

  if d - 2*k gt 1 then
    //We need an element go in SO(d-2*k,q) - Omega.
    go := SOMinusOmega(d-2*k, q, sign);
  end if;

  if IsOdd(d) then //Magma's form is not scalar antidiagonal for some reason!
    mr := (d+1) div 2;
    ourform := Matrix(GF(q), d, d, [<i, d-i+1, 1> : i in [1..d]]);
    isf, type, magform := OrthogonalForm(Om(d,q));
    ce := magform[1][d]/magform[mr][mr];
  end if;

  if sign eq -1 then
    hd := d div 2;
    isf, magform := QuadraticForm(Om(d,q));
    magform *:= magform[1][d]^-1;
    t:=magform[hd][hd]; u:=magform[hd][hd+1]; v:=magform[hd+1][hd+1];
  end if;

  z:= PrimitiveElement(GF(q));
  form:= GL(k,q)!Matrix(GF(q), k, k, [<i, k-i+1, 1> : i in [1..k]]);
  diag:= [<i,i,1>: i in [1..d]];
  gens := [GL(d,q)|];
 
  //GL(k, q) on <e_1..e_k>, balanced on <f_k..f_1>.
  gens := [GL(d,q)| ];
  for i in [1..Ngens(GL(k,q))] do
    gen := GL(k,q).i;
    elt := DiagonalJoin(< gen, IdentityMatrix(GF(q),d-2*k),
                                  form*Transpose(gen^-1)*form > );
    if IsEven(q) or ( IsOdd(q) and IsSquare(Determinant(gen)) or
            InOmega(elt,d,q,sign) or special ) then
      Append(~gens, elt);
      continue;
    end if;
    if d - 2*k gt 1 then
      elt := DiagonalJoin(< gen, go, form*Transpose(gen^-1)*form > );
      Append(~gens, elt );
    elif elt^2 ne elt^0 then
      Append(~gens, elt^2 );
    elif i ne Ngens(GL(k,q)) then //only for case q=3, k>1
      gen := (GL(k,q).(i+1))^gen;
      elt := DiagonalJoin(< gen, IdentityMatrix(GF(q),d-2*k),
                                    form*Transpose(gen^-1)*form > );
      Append(~gens, elt );
    end if;
  end for;

  if d - 2*k gt 1 then
    //the orthogonal group acting on a (d-2k) space.
    gens cat:=
       [ DiagonalJoin(<IdentityMatrix(GF(q), k), Om(d-2*k, q).i,
             IdentityMatrix(GF(q), k)>) : i in [1..Ngens(Om(d-2*k, q))] ];
    if special then
       Append( ~gens, DiagonalJoin(<IdentityMatrix(GF(q), k),
             SOMinusOmega(d-2*k, q, sign), IdentityMatrix(GF(q), k)>) );
    end if;
    if general and IsOdd(q) then
       Append( ~gens, DiagonalJoin(<IdentityMatrix(GF(q), k),
             GOMinusSO(d-2*k, q, sign), IdentityMatrix(GF(q), k)>) );
    end if;
  end if;

  if d - 2*k eq 1 and general and IsOdd(q) then
       Append( ~gens, DiagonalJoin(<IdentityMatrix(GF(q), k),
           Matrix(GF(q),1,1,[-1]) , IdentityMatrix(GF(q), k)>)  );
  end if;
  
  if k gt 1 then
    Append(~gens,
       GL(d, q)!Matrix(GF(q), d, d, [<d-1,1,1>, <d,2,-1>] cat diag) );
  end if;
  if (d gt 2*k+2) or (d eq 2*k+2 and sign eq 1) then
    Append(~gens,
     GL(d, q)!Matrix(GF(q), d, d, [<k+1, 1, 1>, <d, d-k, -1>] cat diag) );
    if d eq 2*k+2 and sign eq 1 then
      Append(~gens,
       GL(d, q)!Matrix(GF(q), d, d, [<k+2, 1, 1>, <d, d-k-1, -1>] cat diag) );
    end if;
  elif d eq 2*k+1 then 
    Append(~gens,
     GL(d, q)!Matrix(GF(q), d, d,
         [<k+1, 1, 1>, <d, d-k, -ce>, <d, 1, -ce/2> ] cat diag) );
  elif d eq 2*k+2 and sign eq -1 then
    y := 2*v/(u^2-4*v*t); x := -u/(u^2-4*v*t);
    Append(~gens,
     GL(d, q)!Matrix(GF(q), d, d,
         [<k+1, 1, 1>, <d, k+1, y >, <d, k+2, x >,
            <d, 1, -y^2*t - y*u*x - x^2*v> ] cat diag) );
  end if;

  if normaliser then
    if IsOdd(q) and IsEven(d) and d ne 2*k then
       Append( ~gens, DiagonalJoin(<ScalarMatrix(k, z),
             NormGOMinusGO(d-2*k, q, sign), IdentityMatrix(GF(q), k)>) );
    elif IsOdd(q) and d eq 2*k then
      Append(~gens, NormGOMinusGO(d,q,sign) );
    elif q gt 3 then
      Append(~gens, ScalarMatrix(d,z) );
    end if; 
  end if;

  return sub<GL(d, q)| gens >;
  //sign=1, k = d/2, c=2, so (q even), go-so ( q odd); o.w. c=1. 
end function;

function NSPointStabOmega(d, q, sign : special:=false, normaliser:=false )
  local QF,c,u,v,w,z,U,V,W,isf,qf,bf,gens,sp,ims,mat,eqns,cmat;
  assert IsEven(d) and IsEven(q) and d gt 2 and sign in {-1,1};

  QF := func< v,qf | (Matrix(v) * qf * Transpose(Matrix(v)))[1][1] >;

  if normaliser then special:=true; end if;

  Omdq := sign eq 1 select OmegaPlus(d,q) else OmegaMinus(d,q);
  isf, qf := QuadraticForm(Omdq);
  isf, bf := SymmetricBilinearForm(Omdq);
  //normalize qf and bf
  qf := qf[1][d]^-1 * qf;
  bf := bf[1][d]^-1 * bf;
  V := VectorSpace(GF(q),d);
  U := VectorSpace(GF(q),d-2);
  W := VectorSpace(GF(q),d-1);
  v := V!([1] cat [0:i in [1..d-2]] cat [1]);
  assert QF(v,qf) eq 1;

  cmat := GL(d,q)!Matrix(GF(q),d,d,
             [<1,d,1>, <d,1,1>] cat [ <i,i,1> : i in [2..d-1] ] );
  //Element of group to be constructed that is outside of Omega
  gens := [GL(d,q)|];
  sp := Sp(d-2,q);
  // Now we calculate embedding of sp into G.
  //Unfortunately bf is not always just antidiagonal 1, so need to transform
  //generators
  mat := GL(d-2,q)!DiagonalMatrix(GF(q),
         [bf[i][d+1-i]^-1 : i in [2..d div 2] ] cat [1 : i in [2..d div 2] ] );
  for gen in [(sp.i)^mat : i in [1..Ngens(sp)] ] do
    ims := [V|];
    for i in [1..d-2] do
      w := V!([0] cat Eltseq(U.i^gen) cat [0]);
      c := (QF(V.(i+1),qf) + QF(w,qf))^(q div 2); //^(q div 2) = sqrt.
      w := w + c*v; //image of V.(i+1) under generator
      assert QF(w,qf) eq QF(V.(i+1),qf);
      Append(~ims,w);
    end for;
    eqns := Transpose(Matrix(ims cat [v]));
    z := Solution(bf*eqns,W.(d-1));
    P := PolynomialRing(GF(q)); x := P.1;
    rts := Roots(x^2+x+QF(z,qf));
    if rts eq [] then error "Cannot solve quadratic"; end if;
    z := z + rts[1][1]*v;
    newgen := GL(d,q)!Matrix([z] cat ims cat [z+v]);
    if not special and not InOmega(newgen,d,q,sign) then
      newgen *:= cmat;
    end if;
    Append(~gens, newgen );
  end for;
  if special then Append(~gens, cmat); end if;
  if normaliser and q gt 2  then
    Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
  end if;

  return sub<GL(d,q) | gens >;
  //c=1.
end function;

NonDegenStabOmega := function(d, q, sign, k, sign1: special:=false,
                         general:=false, normaliser:=false, ipn:=false )
/* Construct stabilizer of nondenerate space of dimension k,
 * of type Omega^sign1(k,q) + Omega^sign2(d-k,q) in Omega^sign(d,q),
 * where sign2 is to be calculated.
 */
  local  Omdq, sign2, type, isf, gp1, gp2, gens, gen, newgen, tmat, ex,
         gsl1, ggl1, gsl2, ggl2, cmat1, cmat2, cmat3, cmat4, cmat5,
         w, form, form1, form2, formt;
  assert d gt 2;
  assert (IsEven(d) and IsEven(k)) or IsOdd(q);
  assert (IsOdd(d) and sign eq 0) or (IsEven(d) and sign in {-1,1});
  assert (IsOdd(k) and sign1 eq 0) or (IsEven(k) and sign1 in {-1,1});
  assert k lt d ;
  assert IsEven(d) or sign1 ne 0; //o.w. sign2 would be ambiguous
  assert sign1 ne -1 or sign ne -1; //instead use sign2 = 1, k = d-k
  assert k gt 1; //instead use k = d-1

  if ipn then normaliser:=true; end if;
  if normaliser then general:=true; end if;
  if general then special:=true; end if;
  //ipn is used only to compute imprimitive normaliser when k=d/2 is odd,
  //and components are non-isometric.

  type := sign eq 0 select "orth" else
          sign eq 1 select "orth+" else "orth-";

  sign2 := sign eq 1 select sign1 else
           sign eq -1 and sign1 eq 1 select -1 else
           sign eq -1 and sign1 eq 0 select  0 else
           0; //sign eq 0
  /* legal values for (sign1,sign2,sign) are
   * (+,+,+), (-,-,+), (+,-,-), (0,0,+) (k>1), (0,0,-) (k>1), (+,0,0), (-,0,0).
   */

  gp1 :=  sign1 eq 0 select GO(k,q) else
          sign1 eq 1 select GOPlus(k,q) else GOMinus(k,q);
  
  gp2 :=  d-k eq 1 select sub<GL(1,q) | [-1] > else
          sign2 eq 0 select GO(d-k,q) else
          sign2 eq 1 select GOPlus(d-k,q) else GOMinus(d-k,q);

  //Note that we use GO  (rather than SO, Omega) to calculate the forms
  //to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEven(q) then
    if q eq 2 and k eq 2 and sign1 eq 1 then
      form1 := Matrix(GF(q),2,2,[0,1,0,0]);
    else isf, form1 := QuadraticForm(gp1);
    end if;
    //note d-k=1 cannot occur for even q.
    if q eq 2 and d-k eq 2 and sign2 eq 1 then
      form2 := Matrix(GF(q),2,2,[0,1,0,0]);
    else isf, form2 := QuadraticForm(gp2);
    end if;
  else
    if q eq 3 and k eq 2 and sign1 eq 1 then
      form1 := Matrix(GF(q),2,2,[0,1,1,0]);
    else isf, form1 := SymmetricBilinearForm(gp1);
    end if;
    if d-k gt 1 then
      if q eq 3 and d-k eq 2 and sign2 eq 1 then
        form2 := Matrix(GF(q),2,2,[0,1,1,0]);
      else isf, form2 := SymmetricBilinearForm(gp2);
      end if;
    else form2 := Matrix(GF(q),1,1,[1]);
    end if;
  end if;

  //We need elements of ggl1/2, gsl1/2 in sl-omega (d-k>1) and gl-sl(p odd) 
  gsl1 := SOMinusOmega(k, q, sign1);
  if d - k gt 1 then
    gsl2 := SOMinusOmega(d-k, q, sign2);
  end if;
  if IsOdd(q) then
    ggl1 := GOMinusSO(k, q, sign1);
    ggl2 := GOMinusSO(d-k, q, sign2);
  end if;
  
  //now redefine gp1, gp2 to include generators of Omega + gsl, ggl 
  
  gp1 :=  sign1 eq 0 select Omega(k,q) else
          sign1 eq 1 select OmegaPlus(k,q) else OmegaMinus(k,q);
  gp1 := sub < GL(k,q) | gp1, gsl1 >;
  if IsOdd(q) then
    gp1 := d-k gt 1 select sub < GL(k,q) | gp1, ggl1 >
                      else sub < GL(k,q) | gp1, ggl1, ggl1*gsl1 >;
    //this difference is because we have fewer adjusting elements in gp2 when
    //d-k=1.
  end if;

  if d-k gt 1 then
    gp2 :=  sign2 eq 0 select Omega(d-k,q) else
            sign2 eq 1 select OmegaPlus(d-k,q) else OmegaMinus(d-k,q);
    gp2 := sub < GL(d-k,q) | gp2, gsl2 >;
    //we don't need to put ggl2 into gp2 - ggl2 is needed to "adjust"
    //ggl1 only.
  end if;

  //In case (o,o,+-) we need to make sure the forms are of correct type
  if sign1 eq 0 then
    //Plus-type form is identity except when d = 2 mod 4, q = 3 mod 4.
    w := PrimitiveElement(GF(q));
    ex := d mod 4 eq 2 and q mod 4 eq 3;
    formt := (sign eq 1 and not ex) or (sign eq -1 and ex)
             select MatrixAlgebra(GF(q),k)!1 //IdentityMatrix(GF(q),k)
             else DiagonalMatrix(GF(q),k,[1:i in [1..k-1]] cat [w]);
    cmat1 := CorrectForm(form1,k,q,"orth"); 
    cmat2 := CorrectForm(formt,k,q,"orth"); 
    gp1 := gp1^(cmat1*cmat2^-1);
    form1 := formt;
    if d-k gt 1 then //form2 should always be of + type
      formt := MatrixAlgebra(GF(q),d-k)!1; //IdentityMatrix(GF(q),d-k);
      cmat3 := CorrectForm(form2,d-k,q,"orth"); 
      cmat4 := CorrectForm(formt,d-k,q,"orth"); 
      gp2 := gp2^(cmat3*cmat4^-1);
      form2 := formt;
      //also transform elements gsl2, ggl2 used to adjust elements of gp1.
      gsl2 := gsl2^(cmat3*cmat4^-1);
      if IsOdd(q) then ggl2 := ggl2^(cmat3*cmat4^-1); end if;
    end if;
    if ipn and k eq d div 2 and form1[k][k] eq w then
      //find element in normaliser interchanging the two spaces
      ipelt := KroneckerProduct(Matrix(GF(q),2,2,[0,1,1,0]), GL(k,q).0);
      cmat5 := cmat2*cmat4^-1;
      //cmat5 * form1 * cmat5^T = t form2 - find t.
      t := (cmat5 * form1 * Transpose(cmat5))[1][1] / form2[1][1];
      cmat5s := ScalarMatrix(k,t^-1) * cmat5;
      ipelt := GL(d,q)!(DiagonalJoin(cmat5s,cmat5^-1) * ipelt);
    end if;
  end if;

  //We will need to transform our generators to fix Magma's quadratic form.
  tmat := TransformForm(DiagonalJoin(form1,form2), type);

  //Now we can start constructing the generators
  gens := [GL(d,q)|];

  for gen in [gp1.i : i in [1..Ngens(gp1)]] do
    if Determinant(gen) ne 1 then
      if general then
        newgen := GL(d,q)!DiagonalJoin(gen,Id(gp2))^tmat;
        Append(~gens,newgen);
      end if;
      //use ggl2 to adjust it and make determinant 1
      newgen := GL(d,q)!DiagonalJoin(gen,ggl2)^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif d-k gt 1 then
        //adjust again using gsl2.
        newgen := GL(d,q)!DiagonalJoin(gen,ggl2*gsl2)^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    else
      newgen := GL(d,q)!DiagonalJoin(gen,IdentityMatrix(GF(q),d-k))^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      elif d-k gt 1 then
        //adjust using gsl2.
        newgen := GL(d,q)!DiagonalJoin(gen,gsl2)^tmat;
        assert InOmega(newgen,d,q,sign);
        Append(~gens,newgen);
      end if;
    end if;
  end for;

  if d-k gt 1 then
    for gen in [gp2.i : i in [1..Ngens(gp2)]] do
      newgen := GL(d,q)!DiagonalJoin(IdentityMatrix(GF(q),k),gen)^tmat;
      if special or InOmega(newgen,d,q,sign) then
        Append(~gens,newgen);
      end if;
    end for;
  end if;

  if normaliser then
    if IsOdd(q) and IsEven(d) and IsEven(k) then
      gnl1 := NormGOMinusGO(k, q, sign1);
      gnl2 := NormGOMinusGO(d-k, q, sign2);
      newgen := (GL(d,q)!DiagonalJoin(gnl1,gnl2))^tmat;
      Append(~gens,newgen);
    elif q gt 3 then
      Append(~gens, ScalarMatrix(d, PrimitiveElement(GF(q))) );
    end if;
  end if;

  if ipn and k eq d div 2 and form1[k][k] eq w then
    Append(~gens, ipelt^tmat);
  end if;

  return sub<GL(d,q) | gens>;
  // q, k, d-k odd, c=2, normgo-go, o.w. c=1.
end function;

function OrthogonalReducibles(d, q, sign)
  assert d gt 2;
  assert (IsOdd(d) and sign eq 0) or (IsEven(d) and sign in {-1,1});
  list:= [];
  half := d div 2;
  for i in [1..half] do 
    if sign ne -1 or i ne half then
      Append(~list, IsotropicStabOmega(d, q, i, sign));
    end if;
  end for;

  if IsOdd(d) then
    for i in [2..d-1 by 2] do
      Append(~list, NonDegenStabOmega(d, q, sign, i, 1));
      Append(~list, NonDegenStabOmega(d, q, sign, i, -1));
    end for;
  else //d even
    for i in [1..half] do
      if IsEven(i) then
        if sign eq 1 then
          Append(~list, NonDegenStabOmega(d, q, sign, i, 1));
          Append(~list, NonDegenStabOmega(d, q, sign, i, -1));
        else //sign = -1
          Append(~list, NonDegenStabOmega(d, q, sign, i, 1));
          if i ne half then
            Append(~list, NonDegenStabOmega(d, q, sign, d-i, 1));
          end if;
        end if;
      else //i odd
        if IsOdd(q) then
          Append(~list, NonDegenStabOmega(d, q, sign, d-i, 0));
        end if;
      end if;
    end for;
  end if;

  if IsEven(d) and IsEven(q) then
    Append(~list, NSPointStabOmega(d, q, sign));
  end if;

  return list;
end function;
