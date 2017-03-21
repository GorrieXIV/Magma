freeze;

/////////////////////////////////////////////////////
//                                                 //
//     TESTING EQUIVALENCE OF TERNARY CUBICS       //
//             "3descent-testeq.m"                 //
//                                                 //
//                T. A. Fisher                     //
//                                                 //
//           Version: 11th April 2006              //
//                                                 //
/////////////////////////////////////////////////////

/*****************

     CHANGE LOG 
               
              **** Please record all changes here ****

  November 2006, Tom:
     * Deleted version of IsEquivalent taking genus one models
         as input. (It's now in "g1testequiv.m")    
     * Versions of ThreeSelmerElement and ThreeTorsionMatrices 
         added that take a genus one model (of degree 3) as input.   
     * Deleted an assert statement in IsEquivalent. (Since the 
         HackObj conversion, it has been checking the wrong thing!)
     * Equations(cubic) replaced by cubic in verbose printing.     

// T. Fisher, April 2010 : Converted to use new TransG1 type
//                         Reduce now calls genus one model version

                                         *************/ 


// This file contains intrinsics :-  
//
//   ThreeTorsionType(E)
//   ThreeTorsionPoints(E)
//   ThreeSelmerElement(E,cubic)
//   ThreeTorsionMatrices(E,cubic)
//   IsEquivalent(cubic1,cubic2)
//   Reduce(cubic)

declare attributes CrvEll: ThreeTorsionType,ThreeTorsionPoints;

Q := Rationals();
K3 := CyclotomicField(3);
// K3 := NumberField( Polynomial([1,1,1]) );

function apply(trans, cubic) 
  return (trans*GenusOneModel(cubic))`Equation;
end function;

// function RationalGCD(S)
//   B := Universe(S);
//   d := LCM([Denominator(Rationals()!x):x in S| x ne 0] cat [1]);
//   return B!(GCD([IntegerRing()!(x*d): x in S])/d);
// end function;

function ThreeIsogenyType(split,a) 
  if split then 
    if IsSquare(a) or IsSquare(-3*a) then 
      type := "mu3+Z/3Z";
    else 
      type := "Diagonal";
    end if;
  else
    if IsSquare(a) then 
      type := "Z/3Z-nonsplit";
    elif IsSquare(-3*a) then 
      type := "mu3-nonsplit";
    else 
      type := "Generic3Isogeny";
    end if;
  end if;
  return type;
end function;

intrinsic ThreeTorsionType(E::CrvEll[FldRat]) -> MonStgElt 
{Identifies the action of Galois on E[3], where E is an elliptic curve over Q. 
The possible values returned are "Generic", "2Sylow", "Dihedral", "Generic3Isogeny", 
"Z/3Z-nonsplit", "mu3-nonsplit", "Diagonal" and "mu3+Z/3Z".}
  if assigned E`ThreeTorsionType then 
    return E`ThreeTorsionType;
  end if;
  c4,c6 := Explode(cInvariants(E));
  if c4 eq 0 then 
    return ThreeIsogenyType(IsPower(c6,3),-6*c6);
  end if;
  P := PolynomialRing(Q); X := P.1;
  F := X^4 - 6*c4*X^2 - 8*c6*X - 3*c4^2;
  if IsIrreducible(F) then 
    Delta := Discriminant(E);
    return IsPower(Delta,3) select "2Sylow" else "Generic";
  end if;
  ff :=  Factorization(F);
  if [Degree(f[1]): f in ff] eq [2,2] then
    type := "Dihedral";
  else
    aa := &cat[Roots(f[1]): f in ff];
    type := ThreeIsogenyType(#aa gt 1,aa[1][1]);
  end if;
  E`ThreeTorsionType := type;
  return type;
end intrinsic; 

// Computes a tuple <T_1 ,..., T_r> of 3-torsion points on E,
// with one representative for each Galois orbit.

function ThreeTorsionReps(E);
  a1,a2,a3,a4,a6 := Explode(aInvariants(E));
  b2,b3,b6,b8 := Explode(bInvariants(E));
  c4,c6 := Explode(cInvariants(E));
  P := PolynomialRing(Q); X := P.1;
  F := X^4 - 6*c4*X^2 - 8*c6*X - 3*c4^2;
  if c4 eq 0 then F := ExactQuotient(F,X); end if;
  FF := Factorization(F);
  FF := [Evaluate(f[1],X^2) : f in FF];
  FF := &cat[Factorization(f): f in FF]; 
  FF := [f[1] : f in FF];
  function torspt(L,phi)
    x := (phi^2 - b2)/12;
    y := (phi^4 - c4)/(48*phi) - (a1*x + a3)/2;
    return E(L)![x,y];
  end function;
  TT := <torspt(Q,Roots(f)[1][1]) : f in FF | Degree(f) eq 1>;
  if c4 eq 0 then 
    flag,sqrt := IsSquare(-c6/6);
    if flag then 
      Append(~TT,E(Q)![-b2/12,sqrt/12 + a1*b2/24 - a3/2]);
      Append(~TT,E(Q)![-b2/12,-sqrt/12 + a1*b2/24 - a3/2]);
    else 
      L<u> := NumberField(X^2 + c6/6);
      Append(~TT,E(L)![-b2/12,u/12 + a1*b2/24 - a3/2]);
    end if;
  end if;
  F2 := [f : f in FF | Degree(f) gt 1];
  F2 := Sort(F2,func<f,g|Degree(f) - Degree(g)>);
  for f in F2 do
    L<u> := NumberField(f);
    Append(~TT,torspt(L,u));
  end for;
  return TT;
end function;

// Optimise the field of definition of a point on E.

function OptimisePoint(T1 : OptimisedRep )
  E := Curve(T1);
  L1 := Ring(Parent(T1));
  if L1 cmpeq Rationals() then return T1; 
  elif Degree(L1) eq 2 and Discriminant(RingOfIntegers(L1)) eq -3 then 
    //Lopt<u>,map1 := OptimizedRepresentation(L1);
    // Unclear whether OptimizedRepresentation makes things faster or slower.
    //flag,map2 := IsIsomorphic(Lopt,K3);
    //assert flag;
    //L2 := K3;
    //map := map1*map2;
    // AVOID CREATING ANY MAPS INVOLVING THE FIELD K3,
    // WHICH IS A GLOBAL VARIABLE.
    // THE ISOMORPHISMS, AND THE ISOMORPHIC FIELDS WILL 
    // STICK AROUND FOREVER, AND EVERYTHING WILL SLOW DOWN.
    
    // L1 is isomorphic to K3
    l := L1.1;
    nl, tl := Explode(Eltseq(MinimalPolynomial(l)));
    dl := tl^2-4*nl;
    _, d := IsSquare( -dl/3 );
    l_K3 := -tl/2 + d*(K3.1-K3.1^2)/2;   // K3.1-K3.1^2 is sqrt(-3)
    assert Evaluate( MinimalPolynomial(l), l_K3) eq 0;
    L1toK3 := func< ll | Eltseq(ll)[1] + Eltseq(ll)[2]*l_K3 >;
    return E(K3)![L1toK3(x): x in Eltseq(T1)];
  elif not OptimisedRep then return T1; 
  else
     L2<u>,L1toL2 := OptimizedRepresentation(L1);
     vprintf ThreeDescent, 1 : "We optimise : %o\n to get : %o\n",
                        DefiningPolynomial(L1), DefiningPolynomial(L2);
     return E(L2)![L1toL2(x): x in Eltseq(T1)];
  end if;
end function;

conjK3 := hom<K3->K3|K3.1^2>;
conjEK3 := func<T|Parent(T)![conjK3(x): x in Eltseq(T)]>;

FieldDegrees := func<GaloisType|case<GaloisType|
  "Generic"         : [8],
  "2Sylow"          : [8],
  "Dihedral"        : [4,4],
  "Generic3Isogeny" : [2,6],
  "Z/3Z-nonsplit"   : [1,1,6],
  "mu3-nonsplit"    : [2,3,3],
  "Diagonal"        : [2,2,4],
  "mu3+Z/3Z"        : [1,1,2,2,2], 
  default           : []            
> >;

procedure CheckTorsionPoints(TT)
  E := Curve(TT[1]);
  GaloisType := ThreeTorsionType(E);
  assert forall{T : T in TT | Curve(T) eq E};
  assert forall{T : T in TT | 3*T eq E!0};
  LL := <Ring(Parent(T)): T in TT>;
  assert &+[Degree(L): L in LL] eq 8;
  assert [Degree(L): L in LL] eq FieldDegrees(GaloisType);
  case GaloisType :
    when "Z/3Z-nonsplit" :
      assert LL[1] eq Q;
      assert LL[2] eq Q;
      assert TT[2] eq -TT[1];
    when "mu3-nonsplit" :
      assert LL[1] eq K3;   
      assert LL[2] eq LL[3];
      assert TT[3] eq -TT[2];
    when "mu3+Z/3Z" :
      assert forall{i : i in [1..2] | LL[i] eq Q};
      assert forall{i : i in [3..5] | LL[i] eq K3};
      S := TT[3];
      T := E(K3)!TT[1];
      assert TT[4] eq S+T;
      assert TT[5] eq S-T;
      assert conjEK3(S) eq -S;
  end case;
end procedure;

intrinsic ThreeTorsionPoints(E::CrvEll[FldRat] : OptimisedRep:=true ) -> Tup
{Same as ThreeTorsionOrbits}
  return ThreeTorsionOrbits(E : OptimisedRep:=OptimisedRep);
end intrinsic;

intrinsic ThreeTorsionOrbits(E::CrvEll[FldRat] : OptimisedRep:=true ) -> Tup
{Computes <T_1, ... , T_r> where the T_i are representatives for the Galois orbits on E[3] - O. }

Check := false;  // Takes significant time 

  if assigned E`ThreeTorsionPoints then
    return E`ThreeTorsionPoints;
  end if;
  TT := ThreeTorsionReps(E);
  TT := <OptimisePoint(T : OptimisedRep:=OptimisedRep) : T in TT>;
  GaloisType := ThreeTorsionType(E);
  case GaloisType :
    when "mu3-nonsplit" :
      S := TT[1];
      T := TT[2];
      TT := <S,T,-T>;
    when "mu3+Z/3Z" :
      SS := [TT[i] : i in [3..5]];
      assert exists(S){S : S in SS | conjEK3(S) eq -S};
      T := E(K3)!TT[1];
      TT := <TT[1],-TT[1],S,S+T,S-T>;
  end case;
  if Check then CheckTorsionPoints(TT); end if;
  E`ThreeTorsionPoints := TT;
  return TT;
end intrinsic;

// Sometimes we need to make a change of co-ordinates
// so that the coefficient of x^3 is non-zero.
// One of the following matrices should suffice.

I := IdentityMatrix(Rationals(),3);
R := Matrix(Rationals(),3,3,[0,0,1,1,0,0,0,1,0]);
S := Matrix(Rationals(),3,3,[1,0,0,1,1,0,0,0,1]);
T := Matrix(Rationals(),3,3,[1,0,0,1,1,0,1,0,1]);
mats := [I,R,R^2,S,R*S,R^2*S,S^(-1),R*S^(-1),R^2*S^(-1),T];

// Computes the syzygetic triangle corresponding to
// the 3-torsion point (xT,yT). A change of co-ordinates
// is made if necessary to ensure that the coefficient 
// of x^3 is non-zero. 

function SyzygeticTriangle(cubic,xT,yT)
  c4,c6 := Invariants(GenusOneModel(cubic));
  assert yT^2 eq xT^3 - 27*c4*xT - 54*c6;
  L := Parent(xT);
  U := ChangeRing(Parent(cubic),L)!cubic;
  H := Parent(U)!Hessian(GenusOneModel(cubic))`Equation;
  T := (xT/3)*U + H;
  for mat in mats do
    _,tr := IsTransformation(3,<1,Transpose(mat)>);
    T1 := apply(tr,T);
    if Evaluate(T1,[1,0,0]) ne 0 then
      cob := Matrix(L,3,3,[mat[i,j]:i,j in [1..3]]);
      break;
    end if;
  end for;
  return T1,cob;
end function;

function kumgen(cubic,xT,yT)
  T := SyzygeticTriangle(cubic,xT,yT);
  r,s3,t3,s1,t1,s2,v,t2,w,u := Explode(ModelToSequence(GenusOneModel(T)));
  assert r ne 0; 
  R := 2*s1^3 - 9*r*s1*s2 + 27*r^2*s3;
  S := 2*s1^2*v - s1*s2*u - 6*s1*s3*t1 + 2*s2^2*t1 - 6*r*s2*v + 9*r*s3*u;
  return (1/2)*(R + 27*r*S/yT);
end function;

function torsmat(cubic,xT,yT)
  T,cob := SyzygeticTriangle(cubic,xT,yT);
  r,s3,t3,s1,t1,s2,v,t2,w,u := Explode(ModelToSequence(GenusOneModel(T)));
  L := Parent(xT);
  assert r ne 0; 
  mat1 := Matrix(L,3,3,[
    -12*r*s2*w - 36*r*s3*t2 + 12*r*u*v + 4*s1^2*w + 4*s1*s2*t2 
        - 8*s1*t1*v - s1*u^2 + 12*s3*t1^2, 
    -54*r*s3*w + 18*r*v^2 + 6*s1*s2*w - 3*s1*u*v - 6*s2*t1*v + 9*s3*t1*u, 
    -81*r*s3*t3 + 9*r*v*w + 9*s1*s2*t3 - 3*s1*t2*v - 3*s2*t1*w + 9*s3*t1*t2, 
    36*r*s2*t2 - 9*r*u^2 - 12*s1^2*t2 + 12*s1*t1*u - 12*s2*t1^2, 
    24*r*s2*w + 18*r*s3*t2 - 15*r*u*v - 8*s1^2*w - 2*s1*s2*t2 + 10*s1*t1*v 
        + 2*s1*u^2 - 3*s2*t1*u - 6*s3*t1^2, 
    54*r*s2*t3 - 9*r*u*w - 18*s1^2*t3 + 6*s1*t1*w + 3*s1*t2*u - 6*s2*t1*t2, 
    0, 
    -18*r*s2*v + 27*r*s3*u + 6*s1^2*v - 3*s1*s2*u - 18*s1*s3*t1 + 6*s2^2*t1, 
    -12*r*s2*w + 18*r*s3*t2 + 3*r*u*v + 4*s1^2*w - 2*s1*s2*t2 - 2*s1*t1*v 
        - s1*u^2 + 3*s2*t1*u - 6*s3*t1^2 
  ]);
  mat2 := Matrix(L,3,3,[
    r*s1*u - 2*r*s2*t1, r*s1*v - 3*r*s3*t1,
    r*s1*w - 4*r*s2*t2 - r*t1*v + r*u^2 + s1^2*t2 - s1*t1*u + s2*t1^2, 
    -3*r^2*u + 2*r*s1*t1, -3*r^2*v + r*s2*t1, -3*r^2*w + r*s1*t2, 
    6*r^2*s2 - 2*r*s1^2, 9*r^2*s3 - r*s1*s2, 3*r^2*v - r*s1*u + r*s2*t1
  ]);
  M := -27*(r*mat1 + (yT/3)*mat2)/(2*r*yT^2);
  return cob*M*cob^(-1); 
end function;

intrinsic ThreeSelmerElement(E::CrvEll[FldRat],C::Crv) -> Tup
{Given a ternary cubic with the same invariants as E, returns an element in
(the algebra associated to) the 3-Selmer group of E, corresponding to the cubic. }
  return ThreeSelmerElement(E, Equation(C));
end intrinsic;

intrinsic ThreeSelmerElement(cubic::Any) -> Tup
{Given a ternary cubic C, returns the corresponding element in
(the algebra associated to) the 3-Selmer group of E, where E is the Jacobian of C. }
  E := Jacobian(cubic);
  return ThreeSelmerElement(E,cubic);
end intrinsic;

intrinsic ThreeSelmerElement(E::CrvEll[FldRat],cubic::ModelG1) -> Tup
{Given a ternary cubic with the same invariants as E, returns an element in
(the algebra associated to) the 3-Selmer group of E, corresponding to the cubic. }
  require Degree(cubic) eq 3 : "Genus one model must have degree 3";
  return ThreeSelmerElement(E, Equation(cubic));
end intrinsic;

intrinsic ThreeSelmerElement(E::CrvEll[FldRat],cubic::RngMPolElt) -> Tup
{Given a ternary cubic with the same invariants as E, returns an element in
(the algebra associated to) the 3-Selmer group of E, corresponding to the cubic. }
  flag, model := IsGenusOneModel(cubic);
  require flag and model`Degree eq 3 : "Input must be a plane cubic";
  require cInvariants(model) eq cInvariants(E) : "Ternary cubic and elliptic curve must have the same invariants.";
  torspts := ThreeTorsionPoints(E);
  a1,a2,a3 := Explode(aInvariants(E));
  kg := func<T|kumgen(cubic,xT,yT) 
    where xT is 36*T[1] + 3*(a1^2 + 4*a2)
    where yT is 108*(2*T[2] + a1*T[1] + a3)>;
  alpha := <kg(T) : T in torspts>;
  for i in [1..#torspts] do
    if alpha[i] eq 0 then
      alpha[i] := kg(-torspts[i])^(-1);
    end if;
  end for;
  return alpha;
end intrinsic;

intrinsic ThreeTorsionMatrices(E::CrvEll[FldRat],cubic::ModelG1) -> Tup
{Given a ternary cubic with the same invariants as E, computes a matrix in GL_3(L) describing the action of E[3] on the cubic, where E[3] - \{0\} = Spec L. 
The determinant of this matrix is computed by ThreeSelmerElement.}
  require Degree(cubic) eq 3 : "Genus one model must have degree 3";
  return ThreeTorsionMatrices(E, Equation(cubic));
end intrinsic;

intrinsic ThreeTorsionMatrices(E::CrvEll[FldRat],cubic::RngMPolElt) -> Tup
{Given a ternary cubic with the same invariants as E, computes a matrix in GL_3(L) describing the action of E[3] on the cubic, where E[3] - \{0\} = Spec L. 
The determinant of this matrix is computed by ThreeSelmerElement.}

Check := false;  // takes about a third of the time

  flag, model := IsGenusOneModel(cubic);
  require flag and model`Degree eq 3 : "Input must be a plane cubic";
  require cInvariants(model) eq cInvariants(E) : 
    "Ternary cubic and elliptic curve must have the same invariants.";
  torspts := ThreeTorsionPoints(E);
  a1,a2,a3 := Explode(aInvariants(E));
  mat := func<T|torsmat(cubic,xT,yT) 
    where xT is 36*T[1] + 3*(a1^2 + 4*a2)
    where yT is 108*(2*T[2] + a1*T[1] + a3)>;
  M := <mat(T) : T in torspts>;
  for i in [1..#torspts] do
    if M[i] eq 0 then
      M[i] := mat(-torspts[i])^(-1);
    end if;
  end for;
  if Check then 
    detM := ThreeSelmerElement(E,cubic);
    r := #M;
    assert r eq #detM;
    for i in [1..r] do
      L := Parent(detM[i]);
      assert L eq BaseRing(M[i]);
      assert Determinant(M[i]) eq detM[i];
      U := ChangeRing(Parent(cubic),L)!cubic;
      _,tr := IsTransformation(3,<1,Transpose(M[i])>);
      assert apply(tr,U) eq detM[i]*U;
    end for; 
  end if;
  return M;
end intrinsic;

function IsEqualModCubes(r1,r2);
  m := #r1;
  cbrt := <>;
  for i in [1..#r1] do
    flag,t := IsPower(r1[i]/r2[i],3);
    if flag then 
      cbrt := Append(cbrt,t);
    else
      break;
    end if;
  end for;
  return flag,cbrt;
end function;

function LinearSolve(M1,M2)
  Q := Rationals();
  m := #M1;
  n := Nrows(M1[1]);
  L := <BaseRing(M1[i]): i in [1..m]>;
  degs := [Degree(L[i]) : i in [1..m]];
  assert &+degs eq n^2-1;  
  mats1 := &cat[[Matrix(Q,n,n,[Eltseq(M1[t][i,j])[k] :i,j in [1..n]])
     : k in [1..degs[t]]] : t in [1..m]];
  mats2 := &cat[[Matrix(Q,n,n,[Eltseq(M2[t][i,j])[k] :i,j in [1..n]])
     : k in [1..degs[t]]] : t in [1..m]];  
  M := MatrixAlgebra(Q,n);
  m1 := ChangeUniverse(mats1,M); 
  m2 := ChangeUniverse(mats2,M);
  mat := Matrix(Q,n^2,n^2*(n^2-1),
    [ &cat[Eltseq(Eij*m1[k]-m2[k]*Eij) : k in [1..n^2-1]] : Eij in Basis(M)]); 
  km := KernelMatrix(mat);
  if Nrows(km) eq 1 then 
    soln := &+[km[1,i]*Basis(M)[i] : i in [1..n^2]];
    assert forall{i: i in [1..n^2-1] | soln*m1[i] eq m2[i]*soln};
  else 
    soln := M!0;
  end if;
  return soln;
end function;   

intrinsic IsEquivalent(cubic1::RngMPolElt,cubic2::RngMPolElt: E:=Jacobian(GenusOneModel(cubic1)) ) -> BoolElt,Tup 
{Determines whether two ternary cubics over Q are equivalent as genus one models, 
and if so also returns the transformation relating them. }
  flag, model1 := IsGenusOneModel(cubic1);
  require flag and model1`Degree eq 3 : "The arguments must be plane cubics";
  flag, model2 := IsGenusOneModel(cubic2);
  require flag and model2`Degree eq 3 : "The arguments must be plane cubics";
  B1 := BaseRing(Parent(cubic1));
  require B1 cmpeq Rationals() : "The arguments must be defined over Q.";
  B2 := BaseRing(Parent(cubic2));
  require B2 cmpeq Rationals() : "The arguments must be defined over Q.";
  require cInvariants(model1) eq cInvariants(E)
    : "The arguments must have same invariants as E";
  GaloisType := ThreeTorsionType(E);
  E2 := Jacobian(model2);
  flag,iso := IsIsomorphic(E,E2);
  if not flag then return false,_; end if;
  r,s,t,u := Explode(IsomorphismData(iso));
  originalcubic2 := cubic2;
  cubic2 *:= 1/u;
  kum1 := ThreeSelmerElement(E,cubic1);
  kum2 := ThreeSelmerElement(E,cubic2);
  flag,cbrt := IsEqualModCubes(kum1,kum2);
  if not flag then 
    cubic2 *:= -1;
    u *:= -1;
    kum1 := ThreeSelmerElement(E,cubic1);
    kum2 := ThreeSelmerElement(E,cubic2);
    flag,cbrt := IsEqualModCubes(kum1,kum2);
  end if;
  if not flag then return false,_; end if;
  M1 := ThreeTorsionMatrices(E,cubic1);
  M2 := ThreeTorsionMatrices(E,cubic2);
  M2 := <cbrt[i]*M2[i] : i in [1..#M2]>;
  detM1 := <Determinant(m) : m in M1>;
  detM2 := <Determinant(m) : m in M2>;
  assert detM1 eq detM2;
  L := CartesianProduct(<BaseRing(M): M in M1>);
  m := NumberOfComponents(L);
  auxrts := [L!<1 : i in [1..m]>];
  case ThreeTorsionType(E) :
    when "Diagonal" :
      flag,z := HasRoot(PolynomialRing(L[3])![1,1,1]);
      assert flag;
      auxrts := [elt<L|1,1,z^i>: i in [0..2]];
    when "mu3-nonsplit" :
      auxrts := [elt<L|L[1].1^i,1,1> : i in [0..2]];
    when "mu3+Z/3Z" :
      auxrts := [elt<L|1,1,1,L[4].1^i,L[5].1^j>: i,j in [0..2]];
  end case;
  Q := Rationals();
  for z in auxrts do   
    M2z := <z[i]*M2[i] : i in [1..m]>;
    B := LinearSolve(M1,M2z);
    if B ne 0 then break; end if;
  end for;
  assert B ne 0;
  BB := Transpose(B^(-1));
  dd := RationalGCD(Eltseq(BB));
  _,g := IsTransformation(3,<dd^3*u*Determinant(B),(1/dd)*BB>);
  newcubic := Parent(originalcubic2)!(apply(g,cubic1));
  assert newcubic eq originalcubic2;
  return true,g;
end intrinsic;

r1 := func<L|a where a,b is Signature(L)>;
r2 := func<L|b where a,b is Signature(L)>; 
ConjMat := func<m|Matrix(3,3,[ComplexConjugate(m[i,j]):i,j in [1..3]])>;

// Computes the Heisenberg-invariant inner product, used
// for the reduction of ternary cubics.

function ReductionInnerProduct(cubic,torspts,prec)

  E := Curve(torspts[1]);
  a1,a2,a3 := Explode(aInvariants(E));
  mat := func<T|torsmat(cubic,xT,yT) 
    where xT is 36*T[1] + 3*(a1^2 + 4*a2)
    where yT is 108*(2*T[2] + a1*T[1] + a3)>;
  MM := <mat(T) : T in torspts>;
  for i in [1..#torspts] do
    if MM[i] eq 0 then
      MM[i] := mat(-torspts[i])^(-1);
    end if;
  end for;
  assert exists(M1){ M : M in MM | r1(BaseRing(M)) ne 0 };
  assert exists(M2){ M : M in MM | r2(BaseRing(M)) ne 0 };   
  k := r1(BaseRing(M2))+1;
  while true do
    R := RealField(prec);
    C := ComplexField(prec);
    if BaseRing(M1) cmpeq Rationals() then
      matR := Matrix(R,3,3,[M1[i,j]:i,j in [1..3]]);
    else 
      gen1 := Roots( MinimalPolynomial(BaseRing(M1).1), R)[1][1];
      conj := func< mm | &+[ seq[i]*gen1^(i-1) : i in [1..#seq]] 
                         where seq:=Eltseq(mm) >;
      matR := Matrix(R,3,3,[conj(M1[i,j]):i,j in [1..3]]);
    end if;

    // Correction made 27th March 2009 - to make sure gen2 is not real
    // (see also the "extra piece of checking" a few lines below)
    // gen2 := Roots( MinimalPolynomial(BaseRing(M2).1), C)[1][1];
    rts := Roots( MinimalPolynomial(BaseRing(M2).1), C);
    _,j := Maximum([Abs(Im(r[1])): r in rts]);
    gen2 := rts[j][1];

    conj := func< mm | &+[ seq[i]*gen2^(i-1) : i in [1..#seq]]
                       where seq:=Eltseq(mm) >;
    matC := Matrix(C,3,3,[conj(M2[i,j]):i,j in [1..3]]);
    detR := Determinant(matR);
    detC := Determinant(matC);
    if Abs(detR) gt 10^(-prec/2) and Abs(detC) gt 10^(-prec/2) then break; end if;
    prec *:= 2;
  end while;
  matR := matR/Abs(Determinant(matR))^(1/3);
  matR *:= Sign(Determinant(matR));
  matC := matC/(Determinant(matC))^(1/3);

  // This "extra piece of checking" should be kept commented out
  // since it can fail when we don't use enough precision.
  // wp := matR*matC*matR^(-1)*matC^(-1); // should be zeta_3 I_3
  // z := (1/3)*Trace(wp);
  // error if Abs(z^2+z+1) gt 1,"Matrices do not generate action of E[3]";

  matCbar := ConjMat(matC);
  A := IdentityMatrix(R,3);
  A := &+[Transpose(matR)^j*A*matR^j : j in [0..2]];
  A := MatrixAlgebra(C,3)!A;
  A := &+[Transpose(matCbar)^j*A*matC^j : j in [0..2]];
  A := Matrix(R,3,3,[Re(A[i,j]): i,j in [1..3]]);
  A := A + Transpose(A);
  return A;
end function;

// Find some 3-torsion points on the Jacobian of a ternary cubic.
// (To be used for reduction of the ternary cubic.)
 
function RedTorsPts(cubic,prec)
  E := Jacobian(cubic);
  TT := ThreeTorsionReps(E);
  LL := <Ring(Parent(T)) : T in TT>;
  m := #TT;
  assert exists(r){ i : i in [1..#TT] | r1(LL[i]) ne 0 };
  assert exists(s){ i : i in [1..#TT] | r2(LL[i]) ne 0 };   
  TT := <TT[i] : i in {r,s}>;
  for T in TT do
    L := Ring(Parent(T));
    if not (L cmpeq Rationals()) then 
      SetKantPrecision(L, Max(10,prec) );
    end if;
  end for;
  return TT;
end function;

// Now calls genus one model version

intrinsic Reduce(cubic::RngMPolElt:steps:=3, prec:=0) -> RngMPolElt, Tup
{Replaces a ternary cubic by a GL_3(Z)-equivalent one with smaller coefficients.}
  flag, model := IsGenusOneModel(cubic);
  require flag and model`Degree eq 3 : "Input must be a plane cubic curve";
  model1,tr := Reduce(model);
  require model1 eq tr*model : 
    "Failed to correctly record the transformations";
  return Parent(cubic)!Equation(model1),Tuple(tr);
end intrinsic;








