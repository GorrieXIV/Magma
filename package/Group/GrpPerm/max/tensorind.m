freeze;

import "spinor.m": InOmega;
import "classicals.m": SOMinusOmega, GOMinusSO, NormGOMinusGO, NormSpMinusSp;


function SpTensorInd(m, t, q : normaliser:=false )
  
  assert IsEven(m) and t gt 1;
  assert IsOdd(t*q); // KL - q or t even orthogonal form
  //assert not (<m, q> eq <2, 3>); KL
  main:= TensorWreathProduct(Sp(m, q), Sym(t));

  //z:= PrimitiveElement(GF(q));
  //diag:= GL(m, q)!DiagonalMatrix([z: i in [1..m div 2]] cat [1 : i in
  //[1..m div 2]]);
  diag := NormSpMinusSp(m,q);

  if normaliser then
    invol := diag;
    for i in [2..t] do
      invol:= KroneckerProduct(invol, GL(m, q).0);
    end for;
  else
    invol:= KroneckerProduct(diag, diag^-1);
    for i in [3..t] do
      invol:= KroneckerProduct(invol, GL(m, q).0);
    end for;
  end if;

  grp:= sub<GL(m^t, q)|main, invol>;

  bool, f:= SymplecticForm(main);
  assert bool;
  mat:= CorrectForm(f, m^t, q, "symplectic");

  return grp^(mat^-1);

end function;

/*********************************************************************/ 

function SLTensorInd(m, t, q : general:=false )
  //assert m gt 2; KL - otherwise orthogonal
  assert t gt 1;

  if general then
    return TensorWreathProduct(GL(m, q), Sym(t));
  end if;

  d:= m^t;
  z:= PrimitiveElement(GF(q));
  diag:= GL(m, q)!DiagonalMatrix([z] cat [1 : i in [1..m-1]]);

  if (m eq 2) and (t eq 2) and (q mod 4 eq 1) then
   //kludge, but not maximal for m=2 anyway
    return TensorWreathProduct(GL(m, q), Sym(t)) meet SL(4,q);
  end if;

  if ((t eq 2) and (m mod 4 eq 2) and (q mod 4 eq 3)) then 
    gens:= [KroneckerProduct(SL(m, q).i, SL(m, q).0) : i in [1, 2]]
    cat [KroneckerProduct(SL(m, q).0, SL(m, q).i) : i in [1,2]];
  else
    main:= TensorWreathProduct(SL(m, q), Sym(t));
    gens:= [];
    for x in Generators(main) do
      if Determinant(x) eq 1 then
        Append(~gens, SL(d, q)!x);
      else
        //det = -1 for odd permutation
        if IsOdd(m) then
          Append(~gens, SL(d, q)!(x*ScalarMatrix(d, GF(q)!(-1))));
        else
          assert t eq 2 and m mod 4 eq 2 and q mod 4 eq 1;
          diag4:= diag^((q-1) div 4); //has fourth root of 1
          d42 := KroneckerProduct(diag4, SL(m, q).0);
          Append(~gens, SL(d, q)!(x*d42) );
        end if;
      end if;
    end for;
  end if;

  out:= KroneckerProduct(diag, diag^-1);
  for i in [3..t] do
    out:= KroneckerProduct(out, GL(m, q).0);
  end for;
  out:= SL(d, q)!out;

  exponent:= Gcd(q-1, d) div Gcd(q-1, m^(t-1));
  new_diag:= diag^exponent;
  for i in [2..t] do
    new_diag:= KroneckerProduct(new_diag, GL(m, q).0);
  end for;    
  assert Determinant(new_diag) eq z^(exponent*m^(t-1));
  assert exists(power){e: e in [1..q-1] | z^(d*e) eq
               z^(exponent*m^(t-1))}; //exists because
                                        //exp*m^(t-1) is divisible by
                                        //(q-1, d), can divide through
                                        //by (q-1, d) then compute
                                        //(d/(q-1, d))^-1 mod (q-1)/(q-1,d)
  s:= GL(d, q)!ScalarMatrix(d, z^power);
  return sub<SL(d, q)|gens, out, new_diag*(s^-1)>;
end function;

/******************************************************************/

function SUTensorInd(m, t, q : general:=false, normaliser:=false )
  assert t gt 1;
  //assert m gt 2; KL - C5?
  //assert not IsSoluble(SU(m,q)); KL that would be too expensive!
  //SU(m,q) is soluble only for (m,q)=(2,2), (2,3), (3,2)

  if normaliser then general:=true; end if;
  z:= PrimitiveElement(GF(q^2));
  d:= m^t;
  if general then
     if normaliser then
       return sub< GL(d,q^2) | TensorWreathProduct(GU(m, q), Sym(t)),
                                                     ScalarMatrix(d, z) >;
     end if;
     return TensorWreathProduct(GU(m, q), Sym(t));
  end if;

  if (m eq 2) and (t eq 2) and (q mod 4 eq 3) then
   //kludge, but not maximal for k=2 anyway
    return TensorWreathProduct(GU(m, q), Sym(t)) meet SU(4,q);
  end if;

  diag:= GL(m, q^2)!DiagonalMatrix([z] cat [1 : i in [1..m-2]] cat [z^(-q)]);

  if ((t eq 2) and (m mod 4 eq 2) and (q mod 4 eq 1)) then 
    gens:= [KroneckerProduct(SU(m, q).i, SU(m, q).0) : i in [1, 2]]
    cat [KroneckerProduct(SU(m, q).0, SU(m, q).i) : i in [1,2]];
  else
    main:= TensorWreathProduct(SU(m, q), Sym(t));
    gens:= [];
    for x in Generators(main) do
      if Determinant(x) eq 1 then
        Append(~gens, SL(d, q^2)!x);
      else //det = -1
        if IsOdd(m) then
          Append(~gens, SL(d, q^2)!(x*ScalarMatrix(d, GF(q^2)!(-1))));
        else
          assert t eq 2 and m mod 4 eq 2 and q mod 4 eq 3;
          diag4:= diag^((q+1) div 4); //has fourth root of 1
          d42 := KroneckerProduct(diag4, SU(m, q).0);
          Append(~gens, SL(d, q^2)!(x*d42) );
        end if;
      end if;
    end for;
  end if;

  out:= KroneckerProduct(diag, diag^-1);
  for i in [3..t] do
    out:= KroneckerProduct(out, GL(m, q^2).0);
  end for;
  out:= SL(d, q^2)!out;

  exponent:= Gcd(q+1, d) div Gcd(q+1, m^(t-1));
  new_diag:= diag^exponent;
  for i in [2..t] do
    new_diag:= KroneckerProduct(new_diag, GL(m, q^2).0);
  end for;    
  assert Determinant(new_diag) eq z^((1-q)*exponent*m^(t-1));
  assert exists(power){e: e in [1..q^2-1] | z^(d*e*(q-1)) eq
               z^((1-q)*exponent*m^(t-1))}; //exists because
                                        //exp*m^(t-1) is divisible by
                                        //(q-1)(q+1, d), can divide through
                                        //by (q-1)(q+1, d) then compute
                                        //(d/(q+1, d))^-1 mod (q+1)/(q+1,d)
  s:= GL(d, q^2)!ScalarMatrix(d, z^(power*(q-1)));
  grp:= sub<SL(d, q^2)|gens, out, new_diag*(s^-1)>;

  bool, f:= UnitaryForm(grp);
  //f;
  if not bool then
    error "ERROR: group not unitary";
  end if;

  bool, f2:= UnitaryForm(SU(d, q));
  if f eq f2 then
    return grp;
  end if;

  mat1:= CorrectForm(f, d, q^2, "unitary");
  mat2:= CorrectForm(f2, d, q^2, "unitary");
  return grp^(mat1*mat2^-1);
end function;

function OrthogSpTensorInd(m, t, q :
                            special:=false, general:=false, normaliser:=false)
  //Sp(m,q) wr Sym(t)
  assert IsEven(m) and t gt 1;
  assert IsEven(t*q);
  //assert not (<m, q> eq <2, 3>); KL

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  ex := t eq 2 and m mod 4 eq 2;

  twp:= TensorWreathProduct(Sp(m, q), Sym(t));
  tmat := TransformForm(twp);
  twp := twp^tmat;

  ng := Ngens(twp);
  odd := twp.ng; //coming from odd permutation when t=2
  gens := ex and not general and not (IsEven(q) and special) select
              [ GL(m^t,q) |  twp.i : i in [1..ng-1] ] cat
              [ GL(m^t,q) | (twp.i)^odd : i in [1..ng-1] ]
          else [ GL(m^t,q) | twp.i : i in [1..ng] ];

  if IsOdd(q) and (not ex or special) then
    diag := NormSpMinusSp(m,q);
    if normaliser then
      invol:= diag;
      for i in [2..t] do
        invol:= KroneckerProduct(invol, GL(m, q).0);
      end for;
    else
      invol:= KroneckerProduct(diag, diag^-1);
      for i in [3..t] do
        invol:= KroneckerProduct(invol, GL(m, q).0);
      end for;
    end if;
    invol := (GL(m^t,q)!invol)^tmat;
    Append(~gens,invol);
  end if;

  if normaliser and IsEven(q) and q gt 2 then
    Append(~gens, ScalarMatrix(m^t, PrimitiveElement(GF(q))) );
  end if;

  return sub< GL(m^t, q)| gens >;
  //ex (t=2, m=2 (mod 4)): c=1
  //else q odd: c=4, so,go; q even: c=2, so.
end function;

function OrthogTensorInd(m, t, q, sign :
                            special:=false, general:=false, normaliser:=false)
  //O^sign(m,q) wr Sym(t), s even 
  assert (IsEven(m) and sign in {-1,1}) or (IsOdd(m) and sign eq 0);
  assert t gt 1;
  assert m^t gt 4;

  if sign eq 1 and m eq 2 then
    error "Illegal parameters - OmegaPlus(2,q) is reducible";
  end if;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;
  if IsOdd(m) then
    twp:= general      select TensorWreathProduct(GO(m,q), Sym(t))
          else special select TensorWreathProduct(SO(m,q), Sym(t))
                         else TensorWreathProduct(Omega(m,q), Sym(t));
    cmat := TransformForm(twp);
    twp := twp^cmat;
    gsl := SOMinusOmega(m, q, 0);
    g1 := KroneckerProduct(gsl, GL(m,q).0);
    g2 := KroneckerProduct(gsl, gsl^-1);
    for i in [3..t] do
      g1:= KroneckerProduct(g1, GL(m, q).0);
      g2:= KroneckerProduct(g2, GL(m, q).0);
    end for;
    g1 := (GL(m^t,q)!g1)^cmat;
    g2 := (GL(m^t,q)!g2)^cmat;
    gens:= [GL(m^t,q)|];
    for x in [twp.i : i in [1..Ngens(twp)]] do
      y := x;
      if not general and Determinant(y) ne 1 then
         y *:= GL(m^t,q)!ScalarMatrix(m^t, GF(q)!(-1)); 
      end if;
      if not special and not InOmega(y, m^t, q, 0) then
         y *:= g1;
      end if;
      Append(~gens, y);
    end for;
    if not special then Append(~gens, g2); end if;
    twp := sub< GL(m^t, q) | gens >;
    //twp := twp^TransformForm(twp);
    if normaliser and q gt 3 then
      twp := sub< GL(m^t, q) | twp,
                             ScalarMatrix(m^t, PrimitiveElement(GF(q))) >;
    end if; 

    return twp;
    //c=1
  end if;

  ex1 := t eq 2 and m mod 4 eq 2;
  ex1m := IsOdd(q) and (t eq 2 and m mod 4 eq 0 and sign eq -1);
  ex2 := t eq 3 and m mod 4 eq 2 and
           ((sign eq 1 and q mod 4 eq 3) or (sign eq -1 and q mod 4 eq 1));

  grp1 := sign eq 1 select SOPlus(m,q) else SOMinus(m,q);
  symt := t eq 3 select sub< Sym(t) | (1,2,3), (1,2) > else Sym(t);
  twp:= TensorWreathProduct(grp1, symt);
  tmat := TransformForm(twp);
  twp := twp^tmat;

  ng := Ngens(twp);
  odd := twp.ng; //coming from odd permutation when t=2 or 3
  gens := ex1 and general select
              [ GL(m^t,q) | twp.i : i in [1..ng] ]
          else ex1 select
              [ GL(m^t,q) |  twp.i : i in [1..ng-1] ] cat
              [ GL(m^t,q) | (twp.i)^odd : i in [1..ng-1] ]
          else ex1m or ex2 select
              [ GL(m^t,q) | twp.i : i in [1..ng-1] ]
          else [ GL(m^t,q) | twp.i : i in [1..ng] ];

  if IsOdd(q) then
    ggl := GOMinusSO(m, q, sign);
    for i in [2..t] do
      ggl:= KroneckerProduct(ggl, GL(m, q).0);
    end for;
    ggl := (GL(m^t,q)!ggl)^tmat;
    if special or InOmega(ggl, m^t, q, 1) then
      inom := true;
      Append(~gens,ggl);
      if ex1 then Append(~gens,ggl^odd); end if;
    else
      assert t eq 2;
      inom := false;
      Append(~gens,ggl*ggl^odd);
    end if;
    
    diag := NormGOMinusGO(m, q, sign);
    if normaliser then
      invol:= diag;
      for i in [2..t] do
        invol:= KroneckerProduct(invol, GL(m, q).0);
      end for;
    else
      invol:= KroneckerProduct(diag, diag^-1);
      for i in [3..t] do
        invol:= KroneckerProduct(invol, GL(m, q).0);
      end for;
    end if;
    invol := (GL(m^t,q)!invol)^tmat;
    if special or InOmega(invol, m^t, q, 1) then
      inom := true;
      Append(~gens,invol);
    else
      assert t eq 2;
      if not inom then
        Append(~gens,ggl*invol);
      end if;
    end if;

    if (special and ex2) or ex1m then
      if special or InOmega(odd, m^t, q, 1) then
        Append(~gens,odd);
      else assert inom;
        Append(~gens,ggl*odd);
      end if;
    end if;
  end if;
  if normaliser and IsEven(q) and q gt 2 then
    Append(~gens, ScalarMatrix(m^t, PrimitiveElement(GF(q)) ) );
  end if; 

  return sub< GL(m^t, q)| gens >;
  //ex1 (t=2, m=2 (mod 4)): c=1
  //ex2 (t=3, m=2 (mod 4), sign=1 & q=3 (mod 4) or sign=-1 & q=1 (mod 4)):
  // OR ex1m t=2, sign=-1, m=0 (mod 4)): c=2, go
  //else c=4, so,go;
end function;

