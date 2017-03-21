freeze;

import "spinor.m": InOmega;
import "classicals.m":  NormSpMinusSp, SOMinusOmega, GOMinusSO, NormGOMinusGO;

function SLTensor(d1, d2, q : general:=false )

  assert #Factorisation(q) eq 1;
  assert d2 ge d1;
  //contained in C7 if d2=d1
  //if d1 eq 2 then assert q gt 2; end if; why? 

  k1:= Gcd(d1, q-1); k2:= Gcd(d2, q-1);
  c:= Gcd(k1, k2);
  d:= d1*d2;
  k:= Gcd(d, q-1);
  z:= PrimitiveElement(GF(q));
  scal:= ScalarMatrix(d, z^((q-1) div k));
  i1:= SL(d1, q).0; i2:= SL(d2, q).0;

  newgens:= general select [GL(d,q) | ] else [SL(d,q) | scal];
  if general then
    for i in [1, 2] do
      Append(~newgens, GL(d, q)!KroneckerProduct(GL(d1, q).i,i2));
      Append(~newgens, GL(d, q)!KroneckerProduct(i1,GL(d2,q).i));
    end for;
  else
    for i in [1, 2] do
      Append(~newgens, SL(d, q)!KroneckerProduct(SL(d1, q).i,i2));
      Append(~newgens, SL(d, q)!KroneckerProduct(i1,SL(d2,q).i));
    end for;
  end if;

  ext:= k1*k2*c div k;

  if general or ext eq 1 then
    return sub<GL(d, q)|newgens>;
  end if;

  assert q gt 2;
  g1:= GL(d1, q).1;
  g2:= GL(d2, q).1;
  assert Determinant(g1) eq Determinant(g2);
  assert Determinant(g1) eq z;

  mat := Matrix(Integers(),3,1,[d2,d1,q-1]);
  N :=Nullspace(mat);
  for n in Generators(N) do
    Append(~newgens,KroneckerProduct(g1^n[1],g2^n[2]));
  end for;

  return sub<SL(d, q)|newgens>;
end function;

/********************************************************************/
function GetAandB(q)
  z:= PrimitiveElement(GF(q));
  for a in GF(q) do
    bool, b:= IsSquare(z - a^2);
    if bool then
      return a, b;
    end if;
  end for;
end function;

function SpTensors(d1, d2, q : normaliser:=false )
  assert IsEven(d1);
  //assert d2 gt 2;
  //if d2 eq 3 then assert not q eq 3; end if; //nonmaximal;
  assert IsOdd(q);// q even causes crashes
  assert #Factorisation(q) eq 1;

  d:= d1*d2;  
  i1:= SL(d1, q).0; i2:= SL(d2,q).0;

  if IsOdd(d2) then
    newgens:= [];
    for i in [1..Ngens(SO(d2, q))] do
      Append(~newgens, GL(d, q)!KroneckerProduct(i1,SO(d2, q).i));
    end for;
    for i in [1, 2] do
      Append(~newgens, GL(d, q)!KroneckerProduct(Sp(d1, q).i,i2));
    end for;
    isit, form := SymplecticForm(sub<SL(d, q)|newgens>);
    assert isit;
    if normaliser then
      Append(~newgens, GL(d, q)!KroneckerProduct(NormSpMinusSp(d1,q),i2) );
    end if;
    trans := CorrectForm(form,d,q,"symplectic");
    return sub<GL(d, q)| [trans^-1*g*trans: g in newgens] >, _;
  end if;

  //form_minus:= SymmetricBilinearForm(GOMinus(d2, q));
  isit, type, form_minus:= OrthogonalForm(GOMinus(d2, q));
  assert isit and type eq "orth-";
  //this will conjugate the group so that it is in the form
  //assumed by Kleidman and Liebeck.
  mat_minus:= GL(d2, q)!CorrectForm(form_minus, d2, q, "orth-");
  gominus:= GOMinus(d2, q)^mat_minus;

  newgensp:= []; newgensm:= [];
  for i in [1..Ngens(GOPlus(d2, q))] do
    Append(~newgensp, GL(d, q)!KroneckerProduct(i1,GOPlus(d2,q).i));
  end for;
  for i in [1..Ngens(gominus)] do 
    Append(~newgensm, GL(d, q)!KroneckerProduct(i1,gominus.i));
  end for;
  for i in [1,2] do
    x:= GL(d, q)!KroneckerProduct(Sp(d1, q).i, i2);
    Append(~newgensp, x); Append(~newgensm, x);
  end for;

  z:= PrimitiveElement(GF(q));
  deltasp:= GL(d1, q)!DiagonalMatrix([z : i in [1..(d1 div 2)]] cat [1:
    i in [1..(d1 div 2)]]);
  deltaplus:= GL(d2, q)!DiagonalMatrix([z : i in [1..(d2 div 2)]] cat [1:
    i in [1..(d2 div 2)]]);
  a, b:= GetAandB(q);  
  if IsEven((q-1)*d2 div 4) then
     deltaminus:= GL(d2, q)!Matrix(GF(q), d2, d2,
       &cat[[<2*i+1, 2*i+1, a>, <2*i+1, 2*i+2, b>,
       <2*i+2, 2*i+1, b>, <2*i+2, 2*i+2, -a>] : i in [0..((d2 div 2)-2)]]
       cat [<d2-1, d2, 1>, <d2, d2-1, z>]);
  else
     deltaminus:= GL(d2, q)!Matrix(GF(q), d2, d2,
        &cat[[<2*i+1, 2*i+1, a>, <2*i+1, 2*i+2, b>,
         <2*i+2, 2*i+1, b>, <2*i+2, 2*i+2, -a>] : i in [0..((d2 div 2)-1)]]);
  end if;

  Append(~newgensp, GL(d, q)!KroneckerProduct(deltasp, deltaplus^-1));
  Append(~newgensm, GL(d, q)!KroneckerProduct(deltasp, deltaminus^-1));

  isit, form := SymplecticForm(sub<GL(d, q)|newgensp>);
  assert isit;
  trans := CorrectForm(form,d,q,"symplectic");
  if normaliser then
    Append(~newgensp, GL(d, q)!KroneckerProduct(NormSpMinusSp(d1,q),i2) );
  end if;
  newgensp := [trans^-1*g*trans: g in newgensp];

  isit, form := SymplecticForm(sub<GL(d, q)|newgensm>);
  assert isit;
  trans := CorrectForm(form,d,q,"symplectic");
  if normaliser then
    Append(~newgensm, GL(d, q)!KroneckerProduct(NormSpMinusSp(d1,q),i2) );
  end if;
  newgensm := [trans^-1*g*trans: g in newgensm];

  return sub<GL(d, q)|newgensp>, sub<GL(d, q)|newgensm>;
  //c=1

end function;

function SUTensor(d1, d2, q : general:=false, normaliser:=false )

  assert #Factorisation(q) eq 1;
  assert d2 ge d1;
  //contained in C7 if d2=d1

  if normaliser then general:=true; end if;
  k1:= Gcd(d1, q+1); k2:= Gcd(d2, q+1);
  c:= Gcd(k1, k2);
  d:= d1*d2;
  k:= Gcd(d, q+1);
  z:= PrimitiveElement(GF(q^2));
  scal:= normaliser select ScalarMatrix(d, z)
                      else ScalarMatrix(d, z^((q^2-1) div k));
  i1:= SU(d1, q).0; i2:= SU(d2, q).0;

  //scal preservesform I_d, but we want it to preserve antidiagonal
  form:= Matrix(GF(q^2), d, d, [<i, d-i+1, 1>: i in [1..d]]);
  trans:=CorrectForm(form, d, q^2, "unitary");

  newgens:= normaliser   select [GL(d,q^2) | scal ]
            else general select [GL(d,q^2) | ]
            else [SL(d,q^2) | scal ];

  if general then
    for i in [1, 2] do
      Append(~newgens, GL(d, q^2)!KroneckerProduct(GU(d1, q).i,i2));
      Append(~newgens, GL(d, q^2)!KroneckerProduct(i1,GU(d2,q).i));
    end for;
  else
    for i in [1, 2] do
      Append(~newgens, SL(d, q^2)!KroneckerProduct(SU(d1, q).i,i2));
      Append(~newgens, SL(d, q^2)!KroneckerProduct(i1,SU(d2,q).i));
    end for;
  end if;

  ext:= k1*k2*c div k;

  if ext eq 1 or general then
    return sub<GL(d, q^2)|newgens>;
  end if;

  form1:= Matrix(GF(q^2), d1, d1, [<i, d1-i+1, 1>: i in [1..d1]]);
  trans1:=CorrectForm(form1, d1, q^2, "unitary");
  form2:= Matrix(GF(q^2), d2, d2, [<i, d2-i+1, 1>: i in [1..d2]]);
  trans2:=CorrectForm(form2, d2, q^2, "unitary");
  g1:= DiagonalMatrix(GF(q^2),[z^(q-1)] cat [GF(q^2)!1: i in [1..d1-1]]);
  g2:= DiagonalMatrix(GF(q^2),[z^(q-1)] cat [GF(q^2)!1: i in [1..d2-1]]);
  g1 := trans1 * g1 * trans1^-1;
  g2 := trans2 * g2 * trans2^-1;

  mat := Matrix(Integers(),3,1,[d2,d1,q+1]);
  N :=Nullspace(mat);
  for n in Generators(N) do
    Append(~newgens,KroneckerProduct(g1^n[1],g2^n[2]));
  end for;

  return sub<SL(d, q^2)|newgens>;
end function;

function OrthSpTensor(d1, d2, q :
                  special:=false, general:=false, normaliser:=false)
  assert #Factorisation(q) eq 1;
  assert IsEven(d1) and IsEven(d2);
  assert d2 ge d1;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  d:= d1*d2;
  i1:= SL(d1, q).0; i2:= SL(d2, q).0;
  newgens:= [GL(d,q) | ];
  for i in [1..Ngens(Sp(d1, q))] do
    Append(~newgens, SL(d, q)!KroneckerProduct(Sp(d1, q).i,i2));
  end for;
  for i in [1..Ngens(Sp(d2, q))] do
    Append(~newgens, SL(d, q)!KroneckerProduct(i1,Sp(d2,q).i));
  end for;

  if special or (IsOdd(q) and d mod 8 eq 0) then
    g1 := NormSpMinusSp(d1,q);
    g2 := NormSpMinusSp(d2,q);
    gp := GL(d, q)!KroneckerProduct(g1,g2^-1);
    if general or (special and Determinant(gp) eq 1) or
                                           (IsOdd(q) and d mod 8 eq 0) then
      Append(~newgens, SL(d, q)!KroneckerProduct(g1,g2^-1) );
    end if;
  end if;

  grp := sub< GL(d,q) | newgens >;
  tmat := TransformForm(grp);
  if normaliser then
    if IsOdd(q) then
      Append(~newgens, GL(d, q)!KroneckerProduct(g1, Id(Sp(d2,q)) ) );
    elif q gt 2 then
      Append(~newgens, GL(d, q)!ScalarMatrix(d, PrimitiveElement(GF(q)) ) );
    end if;
    grp := sub< GL(d,q) | newgens >;
  end if;

  return grp^tmat;
  //if q odd and 8|d, c=4, go,so; o.w. c=2, so (q even), go-so (q odd)
end function;

function OrthTensorOddOdd(d1,d2,q :
                  special:=false, general:=false, normaliser:=false)
//type O(d1,q) tensor O(d2,q), d1,d2 odd 
  assert #Factorisation(q) eq 1;
  assert IsOdd(q);
  assert IsOdd(d1) and IsOdd(d2);
  assert d2 ge d1;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  d:= d1*d2;
  i1:= SL(d1, q).0; i2:= SL(d2, q).0;
  newgens:= [GL(d,q) | ];
  fac1 := general select GO(d1,q) else special select SO(d1,q) else Omega(d1,q);
  fac2 := general select GO(d2,q) else special select SO(d2,q) else Omega(d2,q);
  for i in [1..Ngens(fac1)] do
    Append(~newgens, GL(d, q)!KroneckerProduct(fac1.i,i2));
  end for;
  for i in [1..Ngens(fac2)] do
    Append(~newgens, GL(d, q)!KroneckerProduct(i1,fac2.i));
  end for;
  grp := sub< GL(d,q) | newgens >;
  tmat := TransformForm(grp);
  newgens := [g^tmat : g in newgens];

  if not special then
    //need 2 on top
    gso1 := SOMinusOmega(d1, q, 0); 
    gso2 := SOMinusOmega(d2, q, 0); 
    elt := (GL(d, q)!KroneckerProduct(gso1,gso2))^tmat;
    assert InOmega(elt, d, q, 0);
    Append(~newgens,elt);
  end if;

  if normaliser  and q gt 3 then
    Append(~newgens, GL(d, q)!ScalarMatrix(d, PrimitiveElement(GF(q)) ) );
  end if;

  return sub< GL(d,q) | newgens >;
  //c=1.
end function;

function OrthTensorEvenOdd(d1, d2, q, sign1 :
                  special:=false, general:=false, normaliser:=false)
//type O(d1,q) tensor O(d2,q), d1 even, d2 odd 
  assert #Factorisation(q) eq 1;
  assert IsOdd(q);
  assert IsEven(d1) and IsOdd(d2);
  assert sign1 in {-1,1};

  if sign1 eq 1 and d1 eq 2 then
    error "Illegal parameters - Omega(2,q) is reducible"; 
  end if;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  d:= d1*d2;
  i1:= SL(d1, q).0; i2:= SL(d2, q).0;
  newgens:= [GL(d,q) | ];
  if general then
    grp1 := sign1 eq 1 select GOPlus(d1,q) else GOMinus(d1,q);
  elif special then
    grp1 := sign1 eq 1 select SOPlus(d1,q) else SOMinus(d1,q);
  else
    grp1 := sign1 eq 1 select OmegaPlus(d1,q) else OmegaMinus(d1,q);
  end if;
  grp2 := SO(d2,q);

  for i in [1..Ngens(grp1)] do
    Append(~newgens, GL(d, q)!KroneckerProduct(grp1.i,i2));
  end for;
  for i in [1..Ngens(grp2)] do
    Append(~newgens, GL(d, q)!KroneckerProduct(i1,grp2.i));
  end for;
  grp := sub< GL(d,q) | newgens >;
  tmat := TransformForm(grp);
  if normaliser then
    if IsOdd(q) then
      g1 := NormGOMinusGO(d1, q, sign1);
      Append(~newgens, GL(d, q)!KroneckerProduct(g1, i2) );
    elif q gt 2 then
      Append(~newgens, GL(d, q)!ScalarMatrix(d, PrimitiveElement(GF(q)) ) );
    end if;
    grp := sub< GL(d,q) | newgens >;
  end if;
  return grp^tmat;
  //c=1.
end function;

function OrthTensorEvenEven(d1, d2, q, sign1, sign2 :
                  special:=false, general:=false, normaliser:=false)
//type O(d1,q) tensor O(d2,q), d1 d2 even - the most complicated case
//note result is always O^+
  assert #Factorisation(q) eq 1;
  assert IsOdd(q);
  assert IsEven(d1) and IsEven(d2);
  assert sign1 in {-1,1} and sign2 in {-1,1};
  assert sign1 ne sign2 or d1 le d2;
  assert sign1 eq 1 or sign2 eq -1; //use (+,-), not (-,+)

  if sign1 eq 1 and d1 eq 2 then
    error "Illegal parameters - Omega(2,q) is reducible"; 
  end if;

  if normaliser then general:=true; end if;
  if general then special:=true; end if;

  d:= d1*d2;
  i1:= SL(d1, q).0; i2:= SL(d2, q).0;
  newgens:= [GL(d,q) | ];
  if special then
    grp1 := sign1 eq 1 select GOPlus(d1,q) else GOMinus(d1,q);
    grp2 := sign2 eq 1 select GOPlus(d2,q) else GOMinus(d2,q);
  else
    grp1 := sign1 eq 1 select SOPlus(d1,q) else SOMinus(d1,q);
    grp2 := sign2 eq 1 select SOPlus(d2,q) else SOMinus(d2,q);
  end if;
  for i in [1..Ngens(grp1)] do
    Append(~newgens, GL(d, q)!KroneckerProduct(grp1.i,i2));
  end for;
  for i in [1..Ngens(grp2)] do
    Append(~newgens, GL(d, q)!KroneckerProduct(i1,grp2.i));
  end for;
  grp := sub< GL(d,q) | newgens >;
  tmat := TransformForm(grp);
  newgens := [g^tmat : g in newgens];

  //now difficult bit - stuff on top!
  ggl1 := GOMinusSO(d1, q, sign1);
  gd1  := NormGOMinusGO(d1, q, sign1);
  ggl2 := GOMinusSO(d2, q, sign2);
  gd2  := NormGOMinusGO(d2, q, sign2);

  t1 := (GL(d, q)!KroneckerProduct(ggl1, i2))^tmat;
  t2 := (GL(d, q)!KroneckerProduct(i1, ggl2))^tmat;
  diag := (GL(d, q)!KroneckerProduct(gd1, gd2^-1))^tmat;

  if special then
    Append(~newgens,diag);
  else
    //for checking purposes, use KL's D function.
    D1 := d1 mod 4 eq 2 and q mod 4 eq 3 select -sign1 else sign1;
    D2 := d2 mod 4 eq 2 and q mod 4 eq 3 select -sign2 else sign2;

    if InOmega(t1, d, q, 1) then
      int1 :=true;
      Append(~newgens,t1);
    else int1:= false;
    end if;
    assert int1 eq (D2 eq 1);

    if InOmega(t2, d, q, 1) then
      int2 :=true;
      Append(~newgens,t2);
    else int2:= false;
    end if;
    assert int2 eq (D1 eq 1);
  
    if not int1 and not int2 then
      assert InOmega(t1*t2, d, q, 1);
      Append(~newgens,t1*t2);
    end if;

    assert InOmega(diag, d, q, 1) eq (d mod 8 eq 0);

    if d mod 8 eq 0 then
      Append(~newgens,diag);
    elif not int1 then
      assert InOmega(t1*diag, d, q, 1);
      Append(~newgens,t1*diag);
    elif not int2 then
      assert InOmega(t2*diag, d, q, 1);
      Append(~newgens,t2*diag);
    end if;
  end if;

  if normaliser then
    Append(~newgens, (GL(d, q)!KroneckerProduct(gd1, i2))^tmat );
  end if;

  return sub< GL(d,q) | newgens >;
  //sign1=sign2=1: (q odd) d1 or d2 = 2 mod 4 and q = 3 mod 4, c=2, go.
  //                d = 4 (mod 8), c=2, go; o.w. c=4, go,so
  //sign1=sign2=-1: (q odd) c=2, go.
  //sign1=1,sign2=-1: (q odd) 4|d1, d2 = 2 mod 4, q mod 4 = 3 c=4, so,go;
  //                           o.w. c=2, go.
end function;
