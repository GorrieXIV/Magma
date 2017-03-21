freeze;
//======================================================//
// 2ndDescent.m						//
// Brendan Creutz					//
// Started: Dec 2010					//
// Last updated: May 2011				//
//							//
//							//
//							//
// We consider a q-isogeny phi: E1 -> E2 where the	//
// kernel of phi is Z/qZ. We perform phi-descents	//
// on the elements of the phi'-Selmer group		//
//							//
//							//
//======================================================//

QQ := Rationals();
ZZ := Integers();


MakeIntegral := function(Quadrics,PZ);
  nquad := [];
  for quad in Quadrics do
	  cs := Coefficients(quad);
	  m := LCM([Denominator(cs[i]):i in [1..#cs]]);
	  quad2 := (m*quad);
	  cs2 := Coefficients(quad2);
	  r := GCD([ZZ!cs2[i]: i in [1..#cs]]);
	  quad3 := PZ ! (quad2/r);
	  nquad cat:= [Parent(quad)!quad3];
  end for;
  return nquad;
end function;

AdHocReduction := function(Eqns);

  P := Parent(Eqns[1]);
  d := Degree(Eqns[1]);
  monsd := MonomialsOfDegree(P,d);
  PZ := PolynomialRing(ZZ,Rank(P));

  matsize := func<mat | &+[AbsoluteValue(c^2) : c in Eltseq(mat)]>;
  polsize := func<pol | &+[AbsoluteValue(c^2) : c in Coefficients(pol)]>;
  matssize := func<mats | &+[matsize(m) : m in mats]>;
  polssize := func<pols | &+[polsize(p) : p in pols]>;

  function PL(pols)
    mat := Matrix([[MonomialCoefficient(e, m) : m in monsd] : e in pols]);
    gain := &*ElementaryDivisors(mat);
    mat1 := BasisMatrix(PureLattice(Lattice(mat)));
    return [&+[mat1[i,j]*monsd[j] : j in [1..#monsd]] : i in [1..#pols]], gain;
  end function;

  Eqns := MakeIntegral(Eqns,PZ);
 vprintf Selmer,3: "Original size of model (log_10): %o\n", ChangePrecision(Log(10,polssize(Eqns)), 4);

 eqns1 := PL(Eqns);
 vprintf Selmer, 3: "size after PureLattice (log_10): %o\n", ChangePrecision(Log(10, polssize(eqns1)), 4);
  return eqns1;

end function;


/** More Ad Hoc Minimisation and Reduction (for quadric intersections) *****/

RedMiniQI := function(pols,S);

P := Parent(pols[1]);
q := Rank(P);

// Calls Fisher's Minimisation
function Minim(Quadrics,S);
// attempts to minimise Quadrics at the primes in S

  M := MinimisationMatrix(Quadrics,S);
  nquad := [];
  P := Universe(Quadrics);
  for quad in Quadrics do
	  nquad cat:= [Evaluate(quad,[ &+[M[i][j]*P.j : j in [1..q]] : i in [1..q] ] )];
  end for;
  return nquad;

end function;

matsize := func<mat | &+[c^2 : c in Eltseq(mat)]>;
polsize := func<pol | &+[c^2 : c in Coefficients(pol)]>;
matssize := func<mats | &+[matsize(m) : m in mats]>;
polssize := func<pols | &+[polsize(p) : p in pols]>;
mons2 := MonomialsOfDegree(P, 2);

function PL(pols)
  mat := Matrix([[MonomialCoefficient(e, m) : m in mons2] : e in pols]);
  gain := &*ElementaryDivisors(mat);
  mat1 := BasisMatrix(PureLattice(Lattice(mat)));
  return [&+[mat1[i,j]*mons2[j] : j in [1..#mons2]] : i in [1..#pols]], gain;
end function;

function Upper(M)
// Given a symmetric nondegenerate matrix ovre Q, this returns a positive definite matrix over Q bounding the quadratic form.
  D, T := OrthogonalizeGram(M);
  Ti := ChangeRing(T, QQ)^-1;
  D1 := DiagonalMatrix(QQ, [Abs(D[i,i]) : i in [1..NumberOfRows(D)]]);
  return Ti*D1*Transpose(Ti);
end function;

function QFormToMatrix(F)
// Gives the symmetric matrix representing the quadratic form F.
  P := Parent(F);
  d := Rank(P);
  // require IsHomogeneous(F) and TotalDegree(F) eq 2:
  //         "The polynomial must be a quadratic form (homogeneous of degree 2).";
  return Matrix([[(i eq j select 2 else 1)*MonomialCoefficient(F, P.i*P.j)
                    : j in [1..d]] : i in [1..d]]);
end function;

function MatrixToQForm(M, P)
// Gives the quadratic form in the polynomial ring represented by the matrix.
  // require IsSymmetric(M): "Matrix must be symmetric.";
  // require NumberOfRows(M) eq Rank(P): "Polynomial Ring must have as many variables "as the matrix has rows.";
  d := Rank(P);
  return &+[M[i,i]*P.i^2 : i in [1..d]]
          + 2*&+[M[i,j]*P.i*P.j : j in [i+1..d], i in [1..d-1]];
end function;

function REDUCE(Quadrics)
  mats := [QFormToMatrix(e) : e in Quadrics];
  siz := matssize(mats);
 // printf "size of matrices before ad hoc reduction: %o\n", Log(10,siz);

  repeat
    oldsiz := siz;
    U := &+[Upper(m) : m in mats];
    _, T := LLLGram(U);
    mats1 := [T*m*Transpose(T) : m in mats];
    mats1 := [Matrix(q, Eltseq(b))
	       : b in Basis(LLL(Lattice(Matrix([Eltseq(m) : m in mats1]))))];
    siz := matssize(mats1);
  //  printf "size now: %o\n", Log(10,siz);
    if siz lt oldsiz then mats := mats1; end if;
  until siz ge oldsiz;

  neweqns := PL([MatrixToQForm(m, P) : m in mats]);
  PQ := PolynomialRing(QQ,q);
  return [ PQ ! quad : quad in neweqns ];
end function;

MakeIntegral := function(Quadrics);
  return [ P ! quad : quad in Quadrics ];
end function;

MakeRational := function(Quadrics);
  P := PolynomialRing(QQ,q);
  return [ P ! quad : quad in Quadrics ];
end function;

Quadrics := PL(MakeIntegral(pols));
  return REDUCE(MakeIntegral(Minim(MakeRational(Quadrics),S)));
end function;

intrinsic LocalGlobalSelmerDiagram(k::FldNum,c::FldRatElt,S::SeqEnum,q::RngIntElt) -> Tup, Map, SeqEnum, SeqEnum, SeqEnum
{Gives the map k* -> k(S,q)/Q(S,q), the subset satisfying Norm(d) = cQ^*q and local versions at the primes in the set S.}

//======================================================//
//							//
//	Returns maps defining the following diagram	//
//	where Prod_p is the product over p in S.	//
//							//
//	K ---------KtoKSqQ-----------> KSqQ > Hc	//
//	|				|		//
//	|				|		//
//   respFlds			     respGrps		//
//	|				|		//
//	|				|		//
//	v				v		//
// Prod_p K_p ----KpModqQs----> Prod_p K_p* /Q_p*K_p*q	//
//							//
//							//
//	KSqQ is the subgroup of K* / Q*K*q that		//
//	is unramified outside S.			//
//							//
//	Hc gives the subset of KSqQ of elements		//
//	with norm = c mod Q*q.				//
//							//
//======================================================//

Q := PolynomialRing(QQ); x := Q.1;
Qnf := NumberField(x-1 : DoLinearExtension);
Z:=MaximalOrder(Qnf);
O := MaximalOrder(k);
S_Z := {ideal<Z|p> : p in S };
S_O := { fid[1] : fid in Factorization(ideal<O|p>), p in S };

// Compute k(S,q)
vprintf Selmer: "Computing %o-Selmer group of field of degree %o\n", q, Degree(k);
vtime Selmer:
KSq,KtoKSq,mB,B := pSelmerGroup(q,S_O:Raw);
QSq,QtoQSq := pSelmerGroup(q,S_Z);
ImageOfS := {KtoKSq(x) : x in Set(S) join {-1}};

// Quotient to obtain F(S,q)/Q(S,q)
KSqQ, modQstar := quo<KSq | ImageOfS>;
KtoKSqQ := KtoKSq * modQstar;
KSqQtoK := Inverse(KtoKSqQ);
// Defining norms
B := Eltseq(B);
NB := [Norm(b) : b in B];
// N : K(S,q) -> Q(S,q)
BruinNorm := hom<KSq -> QSq |
[QtoQSq(PowerProduct(NB,[c mod q : c in Eltseq(mB(g))])) :
g in OrderedGenerators(KSq)]>;
// N : K(S,q)/K(S,q) -> K(S,q)
MyNorm := hom<KSqQ -> QSq | [BruinNorm(a@@modQstar) : a in
OrderedGenerators(KSqQ)]>;
// The Norm condition
bool, c1 := HasPreimage(QtoQSq(c), MyNorm);

if bool then
	Ker := Kernel(MyNorm);
	//rankFSqQwithNormCond := Ilog(q,#Ker);
	// Representation of the coset c1+Ker:
	_, quomap := quo<KSqQ | Ker>;
	Hc := <quomap, {quomap(c1)} >;
	// The coset of KSqQ of elements satisfying the norm condition is
	// { c1 @@ quomap + x : x in Ker(quomap) }
else
	// The norm condition is not satisfiable.
	Hc := <{},{}>;
end if;

  LocalSelmerGroup := function(K,p,q,ModQ);

  F := GF(q);
  O := MaximalOrder(K);
  pids := [ pid[1] : pid in Factorization(p*O)];

  injs := [];
  ress := [];
  dim := 0;

  for pid in pids do
    K_p, inj := Completion(K,pid);
    pr := (p in {2,3}) select 1000 else 300; 
    SetPrecision(K_p,pr);
    G,m := pSelmerGroup(q,K_p);
    injs cat:= [inj];
    ress cat:= [m];
    dim +:= #Generators(G);
  end for;

  A := FreeAbelianGroup(dim);
  G := quo<A | [ q*A.i : i in [1..dim]]>;
  dima := 0;
  lis := [];
  for i in [1..#injs] do
    G_i := Codomain(ress[i]);
    lis cat:= [hom< G_i -> G | [G.(i+dima) : i in [1..#Generators(G_i)]] >];
    dima +:= #Generators(G_i);
  end for;

  ModqthPowers := map< CartesianProduct([K_p : K_p in [ Domain(m) : m in ress]]) -> G | x :-> &+[ lis[i](ress[i](x[i])) : i in [1..#ress] ]>;
  Inj := map< k -> Domain(ModqthPowers) | x :-> < injs[i](x) : i in [1..#injs] > >;

  if ModQ then
    // We need to mod out by the image of Q* / Q*q as well.
    H,mp := pSelmerGroup(q,Completion(QQ,p));
    Gens := { g @@ mp : g in Generators(H) };
    Qpq := sub< G | { ModqthPowers( < g : i in [1..NumberOfComponents(Domain(ModqthPowers))] > ) : g in Gens } >;
    _,modq := quo< G | Qpq>;
    return ModqthPowers * modq, Inj;
  end if;

  return ModqthPowers, Inj;
  end function; // LocalSelmerGroup

respGrps := [];
respFlds := [];
KpModqQs := [];
for p in S do
  m1,m2 := LocalSelmerGroup(k,p,q,true);
  resp := hom<KSqQ -> Codomain(m1) | [ m1(m2(k ! KSqQtoK(Domain(KSqQtoK).i))) : i in [1..#Generators(KSqQ)] ] >;
  respGrps cat:= [resp];
  respFlds cat:= [m2];
  KpModqQs cat:= [m1];
end for;

return Hc,KtoKSqQ,respFlds,respGrps,KpModqQs;

end intrinsic; //LocalGlobalSelmerDiagram

FindQpPoint := function(C,p,prec)
  // Calls IsLocallySolvable - may result in error...
  // Finds a 'random' Q_p-point on C (not deterministic)
  
  eqs := DefiningEquations(C);
  BP := AmbientSpace(C);
  q := Dimension(BP)+1;
  Zp2 := Integers(p^2);
  LocPoint := false;
  
  while not LocPoint do
  
  Hyperplane := &+[ (ZZ!Random(Zp2))*BP.i : i in [1..q] ];
  HypSlice := Scheme(BP, [ Evaluate(f,[BP.i : i in [1..q]]) : f in eqs] cat [Hyperplane]);
  
    if Dimension(HypSlice) eq 0 then
      LocPoint, Pt := IsLocallySolvable(HypSlice,p);
    end if;
  
  end while; //LocPoint
  
  Qp := pAdicField(p,2*prec);
  Pt := C(Qp)!Pt;
  Pt := LiftPoint(Pt,prec);
  
  Pt := [QQ!c : c in Eltseq(Pt)];
  d := LCM([Denominator(co) : co in Pt]);
  Pt := [ZZ!d*co : co in Pt];
  
  return Pt;
end function; //FindQpPoint

//The main function:
PhiDescent := function(Torsor,E1,E2,Models);

C := Curve(Torsor);
BP := AmbientSpace(C);
q := Dimension(BP)+1;

GetFlexes := function(T);
  // T is a g1 normal curve of degree q
  // returns: Fields:: SeqEnum of FldNum, Flexes:: Tup of SeqEnum 
  dT := DefiningEquations(T);
  BP := AmbientSpace(T);
  Flexes := <>;
  Fields := <>;
  
  for i in [1..q] do
    Ti := Scheme(BP,dT cat [BP.i]);
    Z,AC := PointsOverSplittingField(Ti);
    Pac := Z[1]; 
    f := MinimalPolynomial(AC.1);
    k := ext<QQ|f>;
    Pk := [];
  
    for j in [1..q] do
      a := Roots(MinimalPolynomial(Pac[j]),k)[1,1];
      Pk cat:= [a];
    end for; // j = q
  
    Append(~Fields,k);
    Append(~Flexes,Pk);
  end for; //i = q
  
  // We want to make sure the fields are given by integral primitive elements
  // i.e. we want monic defining polynomials.
  NewFields := <>;
  NewFlexes := <>;
  for u in [1..#Fields] do
    //get better representations;
    Knew,toKnew := OptimisedRepresentation(Fields[u]);
    Append(~NewFields,Knew);
    Append(~NewFlexes, [ toKnew(Flexes[u][i]) : i in [1..q] ] );
  end for;
  return NewFlexes, NewFields;
end function; //GetFlexes


  GetEll := function(T,Flex,ELL2)
  //======================================================
  // T is a genus one normal curve of degree q		
  // in BP^{q-1} and Flex is a flex point of T.		
  //							
  //  Returns: l1,l2,c,beta,Deltac,ND,embed1,embed2	
  //  * { l1 = 0 } is a hyperplane meeting T in Flex
  //    with mult. q					
  //  * { l2 = 0 } is a hyperplane meeting T in Flex
  //    with mult. q-2 and transversely at Flex + Q,
  //   Flex - Q, where Q is some point in E[phi] = mu_q.
  //  * c and Deltac are rationals, Deltac is a q-th power
  //    and they satisfy: N(l1) = c*Deltac*(x.coord)^q
  //    mod the homogeneous ideal of T.
  //  * beta is in H_2 and satisfies: ND(l1) = beta*l2^q
  //    mod the homogeneous ideal of T.
  //  * ND : K -> H_2, the 'induced norm map' labelled
  //    \partial_2 in the manuscript.
  //  * embed1,embed2 : K -> H_2
  //
  //  Will result in an error if the curve is not in
  //  the correct form. i.e. Flexes must lie on a
  //  coordinate hyperplane (possible when the kernel of
  //  phi is mu_q).
  //
  //  if ELL2 eq false this only computes l1. Note l2
  //  is only needed to compute defining equations
  //  (or compute full Selmer set).
  //
  //======================================================//
  
    K := Parent(Flex[1]);
    S := Parent(DefiningEquations(T)[1]);
    P := Flex;
    //Determine which coordinate hyperplane P lies on (assumes the other lie there as well).
    coord := 1;
    while 0 ne P[coord] do
      coord +:=1;
    end while;
    
    
    if ELL2 then
      LoverK := ext<K|CyclotomicPolynomial(q)>;
      H_2overK := [ R[1] : R in Subfields(LoverK) | Degree(R[1]) eq ZZ!((q-1)/2) ][1]; //the unique index 2 subfield of LoverK
h := [ f[1] : f in Factorization(DefiningPolynomial(K),H_2overK) | Degree(f[1]) eq 2 ][1];    
      conjs := [ r[1] : r in Roots(h,LoverK) ];
      nembed1 := hom< K -> LoverK | conjs[1] >;
      nembed2 := hom< K -> LoverK | conjs[2] >;
      
      H_2 := AbsoluteField(H_2overK);
      ND := map< K -> H_2 | phi :-> H_2 ! (H_2overK ! (phi^(q-2)*nembed1(phi)*nembed2(phi))) >;
      // ND is the 'induced norm map' labelled \partial in the manuscript.
      P2 := [ nembed1(x) : x in P];
      //P2 is another flex in the same orbit as P
      //We want a linear form meeting T at P with multiplicity q-2 and meeting T at P2 with multiplicity 1.
      L := AbsoluteField(LoverK);
      P := [LoverK!x : x in P];
      P2 := [LoverK!x : x in P2];
      PwM := [ <P,q-2>, <P2,1> ];
    end if;
    
    GetLinearForm := function(T,L,PwM)
      dT := DefiningEquations(T);
      P := PwM[1][1];
      R := PolynomialRing(L,q);
      N := #dT;
      // T should be defined by N quadrics in BP^{q-1}
      
      //determines an affine patch { x_patch = 1 } on which P lies.
      patch := 1;
      while not patch in { i : i in [1..q] | not 0 in { Pm[1][i] : Pm in PwM } } do
        patch +:= 1;
      end while;
      Ind := Remove([1..q],patch);
      
      X_0 := [];
      cond := [];
      
      //now compute the desired linear form
      for Pm in PwM do
        P := [Pm[1][patch]^(-1)*cc : cc in Eltseq(Pm[1]) ];
        m := Pm[2];
        X_0 cat:= [P[s] : s in Ind];
        cond cat:= [-1];
      
        if m gt 1 then
      
        FirstDerivatives := [];
        fd := [];
      
        for n in [1..N] do
          for i in [1..q] do
            FirstDerivatives cat:= [Evaluate(Derivative(dT[n],i),P)];
            if i in Ind then
        fd cat:= [Evaluate(Derivative(dT[n],i),P)];
            end if;
          end for; //i
        end for; //n
      
        FirstDerivatives := Matrix(L,N,q, FirstDerivatives);
        fd := Matrix(L,N,q-1,fd);
        // FirstDerivatives[n,i] = df_n/d_xi(P)
      
        M1 := Transpose(fd);
        X1 := Kernel(M1);
        x1 := Eltseq(Basis(X1)[1]);
        x1 := [ x1[r] : r in [1..patch-1] ] cat [0] cat [x1[r] : r in [patch..q-1] ];
        cond cat:= [0];
      
        x := Matrix(L,1,q,x1);
        r := 1;
      
        end if; // m ge 1
        if m gt 1 then
      
        SecondDerivatives := [];
        for n in [1..N] do
          M := [];
          for i in [1..q] do
            for j in [1..q] do
        M cat:= [Evaluate(Derivative(Derivative(dT[n],j),i),P)];
            end for; //j
          end for; //i
          fnij := Matrix(L,q,q,M);
          SecondDerivatives cat:= [fnij];
        end for; //n
        // SecondDerivatives[n][i,j] = d^2f_n/dx_idx_j (P)
      
        ComputeHigherMultiplicity := function(r,x);
          //r-th derivatives
          Target := [];
      
          for n in [1..N] do //running over f_n
            target := 0;
            for ijk in CartesianProduct([ Ind : t in [1..2] ]) do
        for a in [1..r-1] do
          target +:= SecondDerivatives[n][ijk[1],ijk[2]]*x[a,ijk[1]]*x[r-a,ijk[2]];
        end for;
            end for;
            Target cat:= [(-1)/(q-1)*target];
          end for; //n in [1..N]
          _,X := IsConsistent(M1,Image(M1)!Target);
          xr := Eltseq(X);
          xr := [ xr[s] : s in [1..patch-1] ] cat [0] cat [xr[s] : s in [patch..q-1] ];
          x := Eltseq(x) cat Eltseq(xr);
          return Matrix(L,r,q,x);
          end function; // ComputeHigherMultiplicity(r,x)
      
        while r lt m-1 do
      
          r +:= 1;
          x := ComputeHigherMultiplicity(r,x);
          cond cat:= [0];
      
        end while;
      
        X_0 cat:= &cat([ [ x[i][j] : j in Ind ] : i in [1..m-1] ]);
      
        end if; // m gt 1
      end for; // Pm in PwM
      
      As := Transpose(Matrix(L,q-1,q-1,X_0));
      _,as := IsConsistent(As,Image(As)! cond );
      as := [ as[r] : r in [1..patch-1] ] cat [0] cat [as[r] : r in [patch..q-1] ];
      as := Eltseq(as);
      return &+[R.i*as[i] : i in Ind] + R.patch;
    end function;//GetLinearForm
      
    RmConsts :=function(Lform:RngMPolElt);
      /*  This function determines obvious common factors of the coefficients of a linear form and removes them. Returning a hopefully smaller integral linear form.
      */
      
      // Make it integral (assuming integral basis for F)
      l := LCM([ Denominator(c) : c in Coefficients(Lform)]) * Lform;
      l *:= GCD( [ZZ! n : n in &cat[ Eltseq(c) : c in Coefficients(l) ] ])^(-1);
      
      return l;
    end function; //RmConsts
  
    // Computing l1
    Ell1 := GetLinearForm(T,K,[<Flex,q-1>]);
    l1 := RmConsts(Ell1);
    RK := Parent(Ell1);
    _,mapa := SwapExtension(RK);
    IT := Ideal(T);
    X_coord5 := NormalForm((S.coord)^q,IT);
    NEll := NormalForm(S!Norm(mapa(l1)),IT);
    c := QQ! (NEll/X_coord5);
    Deltac := Denominator(c)^(-1);
    c := AbsoluteValue(c*Denominator(c)^q);
    fc := Factorization(ZZ!c);
    
    for factor in fc do
      val := factor[2];
      if val ge q then
        Deltac *:= (factor[1]^(Floor(val/q)));
        c := c/(factor[1]^(q*Floor(val/q)));
      end if;
    end for;
    
    if not ELL2 then
      return l1,QQ!c,Deltac;
    end if;
  
    // Computing l2
    Ell2 := PolynomialRing(H_2,q) ! GetLinearForm(T,LoverK,PwM);
    l2 := RmConsts(Ell2);
    RH := Parent(Ell2);
    RL := PolynomialRing(LoverK,q);
    cs := Coefficients(l1);
    NDl1 := RL ! (l1^(q-2));
    NDl1 *:= &+[ nembed1(cs[i])*RL.i : i in [1..q] ];
    NDl1 *:= &+[ nembed2(cs[i])*RL.i : i in [1..q] ];
    NDl1 := RH ! NDl1;
    ITH := ideal< RH | DefiningEquations(T)>;
    l2q := NormalForm(l2^q,ITH);
    NDl1 := NormalForm(NDl1,ITH);
    beta := H_2 ! (NDl1/l2q);
    
    return l1,l2,(QQ!c),beta,Deltac,ND,nembed1,nembed2;
  end function; // GetEll(T,K,Flex)


  BadPrimesFromEll := function(l,q);
    k := BaseRing(Parent(l));
    O := MaximalOrder(k);
    cs := Coefficients(l);
    S1 := <>;
    for a in cs do
      I := ideal<O|a>;
      fI := Factorization(I);
      Append(~S1,{ fI[r][1] : r in [1..#fI]});
    end for;
    S := S1[1];
    for i in [2..q] do
      S := S meet S1[i];
    end for;
    return {Factorization(Norm(pid))[1][1] : pid in S};
  end function; //BadPrimesFromEll

// Begin:
if q eq 5 and false then
  vprintf Selmer, 1: "Attempting to improve model before descent: ";
  g1mC := GenusOneModel(C);
  if Discriminant(g1mC) ne Discriminant(MinimalModel(E1)) then
    ng1mC := Reduce(Minimize(g1mC));
    if IsEmpty({ i : i in [1..5] | #Coefficients(DefiningEquations(Curve(ng1mC))[i]) ne 3 }) then
      vprintf Selmer, 1: "...found better model.\n";
      C := Curve(ng1mC);
    else
      vprintf Selmer, 1: "...no improvement.\n";
    end if;
  end if;
end if;

//E2 := Jacobian(C); not implemented for q = 7...
//E1 := IsogenousCurves(E)[1];
// Assumes E1(Q)[q] = Z/qZ is the optimal curve in the iso class.

S_E := Seqset(BadPrimes(E2));

S_tama1 := {};
S_tama2 := {};
for p in S_E do
  ct := TamagawaNumber(E1,p)/TamagawaNumber(E2,p);
  if QQ!ct eq q then
    Include(~S_tama1,p);
    //Tama +:= 1;
  end if;
  if QQ!ct eq 1/q then
    Include(~S_tama2,p);
    //Tama +:= -1;
end if;
end for;
S_tama := S_tama1 join S_tama2;
vprintf Selmer, 3: "tama1 and tama2 are: %o\n%o.\n",S_tama1,S_tama2;
  
Flexes, Fields := GetFlexes(C);
error if { Degree(k) : k in Fields } ne {q}, "Has a rational flex point.\nNot implemented in this case.";

d,n := Min([ ZZ! Discriminant(Integers(K)) : K in Fields ]);
K := Fields[n];
fd := Factorization(d);
S_F := { p[1] : p in fd } join {q};
vprintf Selmer, 2: "Computing linear forms defining descent maps.\n";
Flex := Flexes[n];

if Models then 
  l1,l2,c,beta,Deltac,ND,nembed1,nembed2 := GetEll(C,Flex,true);
else
  l1,c,Deltac := GetEll(C,Flex,false);
end if;

ell := l1;
vprintf Selmer, 2: "ell_1 = %o.\n",ell;

S_ell := BadPrimesFromEll(l1,q);
S_c := { pp[1] : pp in Factorization(ZZ!c) };

vprintf Selmer, 3: "Primes ramifying in flex algebra are %o.\nBad Primes from E are %o.\nBad Primes from l are %o.\nBad Primes from c are %o.\n", S_F,S_E,S_ell,S_c;

S := S_E join S_F join S_ell join S_c;
S := Setseq(S);
vprintf Selmer, 1: "Discriminant of K is %o.\n", d;
vprintf Selmer, 1: "Computing K(S,%o)/Q(S,%o) for the %o, with S = %o.\n",q,q, K, S;
Hc,KtoKSqQ,respFlds,respGrps,KpModqQs := LocalGlobalSelmerDiagram(K,c,S,q);
KSqQtoK := Inverse(KtoKSqQ);
KernelNorm := Kernel(Hc[1]);
vprintf Selmer, 1: "Subset of K*/Q*K*q unramified outside S and satisfying the norm condition had dimension %o.\n", #Generators(KernelNorm);
Alpha_c := Random(Hc[2]) @@ Hc[1]; // an element in KSqQ of norm c
vprintf Selmer, 3: "An element of norm c = %o is Alpha_c = %o.\n", c, Alpha_c;
KSqQ := Domain(KSqQtoK);
h := KSqQtoK;

DimensionOfLocalImage := function(p);

// returns the F_q dimension of the image of the fake local descent map at the prime p. May only give an upper bound in some cases.

if p in S_tama1 then
  // in this case the local image of the genuine descent map is trivial.
  vprintf Selmer, 3: "Split multiplicative reduction -->\n";
  vprintf Selmer, 2: "Local image should have dimension 0.\n";
  return 0;
end if;

case q:
  when 5: // q = 5
  if p mod q gt 1 and d mod p eq 0 then
    vprintf Selmer, 3: "%o is totally ramified and Q_%o does not contain primitive %o-th roots of unity. Local data will yield no information.\n", p,p,q;
    vprintf Selmer, 2: "Local image should have dimension 0.\n";
    return -1; // should return -1 (set to 0 to test the claim).
  end if;

  if not p in S_tama then
    //local image is a coset of the unramified subgroup (or p = 5).
    vprintf Selmer, 3: "Local image is a coset of unramified subgroup.\n";
    
    case p mod 5:
      when 1:
	vprintf Selmer, 3: "Kernel of fake descent map has dimension 1.\n"; // mu_q in Q_p, so kernel is nontrivial
	if not p in S_F then
	  // kernel is unramified.
	  vprintf Selmer, 3: "Kernel of fake descent map is unramified.\n";
	  vprintf Selmer, 2: "Local image should have dimension 0.\n";
	  return 0; //(should return 0)
	else // kernel should be ramified...
	  vprintf Selmer, 1: "Kernel of fake descent map is ramified. Local image of fake descent map SHOULD be 1***.\n";
	  return 1; // should return 1 (set to 2 to test the claim)
	end if;

      else:
	vprintf Selmer, 3: "Fake descent map is injective.\n";
	vprintf Selmer, 2: "Local image should have dimension 1.\n";
	return 1;//should return 1
    end case; // p mod 5

  else // p in S_tama2; kernel may or may not be ramified.
    vprintf Selmer, 3: "Split multiplicative reduction with reversed Tamagawa numbers.\n";
      
    case p mod 5:

      when 1: //descent map is not injective (no clue)
	vprintf Selmer, 1: "Local descent map at %o not injective, dimension of local image between 1 and 2.\n", p;
	return 2;
      else:
	vprintf Selmer, 1: "Fake descent map is injective at %o and local image has dimension 2!\n", p;
	return 2;
    end case;
      
  end if; // not p in S_tama
  
when 7: // q = 7
    
  if not p in S_tama then
    //local image is a coset of the unramified subgroup (or p = 7).
    vprintf Selmer, 3: "Local image is a coset of unramified subgroup.\n";
    
    case LegendreSymbol(p,7):

      when 1: //Local descent map is not injective.
	vprintf Selmer, 3: "Kernel of fake descent map has dimension 1.\n";
	if not p in S_F then
	  vprintf Selmer, 3: "Kernel of fake descent map is unramified. Local image has dimension 0.\n";
	  return 0;
	else // p ramifies in F
	  // kernel should be ramified...
	  vprintf Selmer, 1: "Kernel of fake descent map is ramified. Local image of fake descent map SHOULD be 1***.\n";
	  return 2; // should return 1 (set to 2 to test the claim)
	end if;
	  
      else: //Local descent map is injective
	vprintf Selmer, 3: "Local descent map is injective. Dimension of local image at %o is 1.\n",p;
	return 1;
      
    end case; //LegendreSymbol(p,7)

  else // p in S_tama1, Kernel may or may not be ramified.

    vprintf Selmer, 1: "Split multiplicative reduction with reversed Tamagawa numbers!.\n";
	  
    case LegendreSymbol(p,7):

      when 1: //descent map is not injective (no clue)
	vprintf Selmer, 1: "Local descent map at %o not injective, dimension of local image between 0 and 2!.\n", p;
	return 2;
      else:
	vprintf Selmer, 1: "Fake descent map is injective at %o and local image has dimension 2!.\n", p;
	return 2;
    end case;
	  
  end if; // not p in S_tama
    
end case; // q
end function;

ComputeLocalImageAtp := function(p);

N := Index(S,p);
KtoKp := respFlds[N]; 
mod_q := KpModqQs[N]; // K_p ---> K_p* / Q_p*K_p*q
res_p := respGrps[N]; // K(S,q)/Q(S,q) --> K_p* / Q_p*K_p*q
Gp := Codomain(res_p);
pr := (p in {2,3}) select 500 else 300;

vprintf Selmer, 1: "Computing local data at the prime p = %o.\n", p;
dimLocalImage := DimensionOfLocalImage(p);
if dimLocalImage lt 0 then
  return <Domain(res_p),Domain(res_p)!0>;
else

  vprintf Selmer, 3: "Searching for a Q_%o-point.\n",p;
  found := false;
  while not found do
    R := FindQpPoint(C,p,pr);
    if Valuation(Norm(Evaluate(ell,R)),p) lt pr/4 then
      found := true;
    end if;
  end while;
  EllofR1 := mod_q(KtoKp(Evaluate(ell,R)));
  vprintf Selmer, 3: "Found the Q_%o-point R = %o.\nl_%o(R) = %o.\n", p, [ (ZZ!r) : r in R ], p, EllofR1;
  //DefiningEquations(C);

  LocalImage := < sub<Gp|0> , EllofR1 >;
  tries := 0;

 while #Generators(LocalImage[1]) lt dimLocalImage or tries lt 5 do

    found := false;
    while not found do
      R := FindQpPoint(C,p,pr);
      if Valuation(Norm(Evaluate(ell,R)),p) lt pr/4 then
	found := true;
      end if;
    end while;
    EllofR := mod_q(KtoKp(Evaluate(ell,R)));
    nim := sub<Gp| { EllofR - LocalImage[2] + b : b in Generators(LocalImage[1]) join {LocalImage[1] ! 0} } >;
    if #Generators(nim) gt #Generators(LocalImage[1]) then
      vprintf Selmer, 3: "Found new Q_%o-point R = %o mod %o.\nl_%o(R) = %o.\n", p, [ (ZZ!r) : r in R ], p, p, EllofR;
      LocalImage := <nim,EllofR1>;
      vprintf Selmer, 3: "Dimension of found space is now %o.\n", #Generators(nim);
      tries := 0;
    end if;
    tries +:= 1;
    if tries gt 100 then
      dimLocalImage -:= 1;
      printf "****************\nCould not find enough Q_%o-points!.\n****************\n",p;
      tries := 0;
    end if;
    if #Generators(LocalImage[1]) gt dimLocalImage then
      printf "****************\nFinding spurious Q_%o-points!\n****************\n",p;
    end if;
  end while;
  vprintf Selmer, 2: "\nFinished computing the local image:\n";
  if #Generators(LocalImage[1]) eq 0 then
    vprintf Selmer, 3: "l(C(Q_%o)) = %o.\n", p,LocalImage[2];
  else
    vprintf Selmer, 3: "l(C(Q_%o)) = Span(%o) + %o.\n", p, Generators(LocalImage[1]), LocalImage[2];
  end if;

  // compute preimage of l(C(Q_p)) in KSqQ.
  GpmodIm,modIm := quo<Gp|LocalImage[1]>;
  comp := hom<Domain(res_p) -> Codomain(modIm) | [ (res_p*modIm)(KSqQ.i) : i in [1..#Generators(KSqQ)] ] >;
  boo,preim := HasPreimage(modIm(LocalImage[2]-res_p(Alpha_c)),comp);
  if boo then
    PI := < Kernel(comp),preim + Alpha_c>;
    vprintf Selmer, 3: "res_%o^(-1)(l(C(Q_%o))) has dimension %o.\n",p,p,#Generators(PI[1]);
  else
    PI := "empty";
    vprintf Selmer, 3: "res_%o^(-1)(l(C(Q_%o))) is empty.\n", p,p;
  end if;
  return PI;
end if;
end function;

PreimsOfLocalIms := <KernelNorm,Alpha_c>;

  IntersectCosets := function(V,W);
    V1 := V[1];
    v1 := V[2];
    V2 := W[1];
    v2 := W[2];
    // we want to find  ( V1 + v1 ) meet ( V2 + v2)
    VW,i1,i2 := DirectSum(V1,V2);
    p1 := Inverse(i1); p2 := Inverse(i2);
    dif := hom< VW -> KSqQ | [ -p1(VW.i) : i in [1..#Generators(V1)] ] cat [ p2(VW.i) : i in [#Generators(V1)+1..#Generators(VW)] ] >;
    if HasPreimage(v1-v2, dif) then
      alpha := v1 + p1((v1-v2) @@ dif);
      return <V1 meet V2,alpha>;
    else
      return "empty";
    end if;
  end function;


vprintf Selmer, 1: "\nComputing Local images.\n\n";

for p in S do
  PI := ComputeLocalImageAtp(p);
  if Type(PI) eq MonStgElt then
    if Models then
      return [],[* *];
    else
      return -1;
    end if;
  end if;
  PreimsOfLocalIms := IntersectCosets(PreimsOfLocalIms,PI);
  if Type(PreimsOfLocalIms) eq MonStgElt then
    if Models then
      return [],[* *];
    else
      return -1;
    end if;
  else
    vprintf Selmer, 2: "Dimension is now %o.\n\n", #Generators(PreimsOfLocalIms[1]);
  end if;
end for;

vprintf Selmer, 1: "Fake phi-Selmer set has dimension %o.\n", #Generators(PreimsOfLocalIms[1]);

if not Models then
  //gives the dimension of the fake phi Selmer set.
  return #Generators(PreimsOfLocalIms[1]);
end if;
// else: continue computing Models

Sel_0 := PreimsOfLocalIms[1];
sel := PreimsOfLocalIms[2];
SelK := [ NiceRepresentativeModuloPowers(KSqQtoK(g + sel),q) : g in Sel_0 ];
//Representatives for the fake Selmer set in K*

LoverK := Codomain(nembed1);
H_2 := Codomain(ND);
vprintf Selmer, 1: "Finding lifts to K* x H_2*.\n";
DelEps := [];
// Some improvement should be possible here...
for del in SelK do
  // finds lifts of del in K* to K* x H_2*
  rt := Roots(PolynomialRing(H_2)!( [-ND(del)/beta] cat [0 : i in [1..q-1]] cat [1]));
  if #rt gt 0 then
    DelEps cat:= [<del,rt[1][1]>];
  end if;
end for;

if #DelEps eq 0 then
  return [],[* *];
end if;

RL<[v]> := PolynomialRing(LoverK,2*q);
RK<[w]> := PolynomialRing(K,q);
RH<[x]> := PolynomialRing(H_2,2*q);
RQ<[u]> := PolynomialRing(QQ,q);
Pr := ProjectiveSpace(RQ);
_,mmK := SwapExtension(RK);
_,mmH := SwapExtension(RH);
RK2q<[t]> := PolynomialRing(K,2*q);
l2 :=  Evaluate(l2,[ Explode([x])[i] : i in [1..q] ]);
l1 :=  Evaluate(l1,[ Explode([t])[i] : i in [1..q] ]);

O := LLL(Integers(K));
genK := &+[ RK.i*O.i : i in [1..q] ];
zq := Evaluate(genK^q, [ RK2q.i : i in [q+1..2*q]]);
NDz := Evaluate(genK^(q-2),[ Explode([v])[i] : i in [q+1..2*q] ]);
NDz *:= &+[ RL.(i+q)*nembed1(Coefficients(genK)[i]) : i in [1..q] ];
NDz *:= &+[ RL.(i+q)*nembed2(Coefficients(genK)[i]) : i in [1..q] ];
NDz := RH ! NDz;

GetModel := function(deleps)
//This gives a model as an intersection of q*(q-1)/2 forms of degree q, together with the covering map PI.

  delta := K ! deleps[1];
  eps := H_2 ! deleps[2];

  e1 := l1 - delta*zq;
  e2 := l2 - eps*NDz;

  _,rk := SwapExtension(Parent(e1));
  _,rh := SwapExtension(Parent(e2));

  CovMapPolys := Reduce(Eltseq(rk(e1)));

  PI := [ - Evaluate(pi, [0 : i in [1..q]] cat [ RQ.i : i in [1..q]]) : pi in CovMapPolys];

  eqs := Eltseq(rh(e2));
  eqs := [Evaluate(e, PI cat Explode([u])) : e in eqs];

  DegreeqToDegree2 := function(Eqns);
  // This finds the space of quadric hypersurfaces containing D, then returns the scheme their intersection defines (the correct model for D).
    RR := Parent(Eqns[1]);
    q := Rank(RR);
    Quadrics := AdHocReduction(Eqns);
    LS := LinearSystem(Pr,2);

    i := 1;
    while #Sections(LS) gt q*(q-3)/2 do
      Dxi := Scheme(Pr,Eqns cat [RR.i]);
      I := Saturation(Ideal(Dxi));
      LS := LinearSystem(LS,Scheme(Pr,I));
      i +:= 1;
      if #Sections(LS) lt q*(q-3)/2 then
	printf "Problems finding intersections";
      end if;
    end while;
    return AdHocReduction(Sections(LS));

  end function; //DegreeqToDegree2
  
  dd := DegreeqToDegree2(eqs);
  //dd := RedMiniQI(dd,Set(S));
  D := Curve(Pr,dd);
  pi := map<D->C| PI>;
  return D,pi;

end function; //GetModel

Models := [];
Maps := [* *];
vprintf Selmer, 1: "Computing Models.\n";
for de in DelEps do
  D,pi := GetModel(de);
  Dmin,TM := Minimize(GenusOneModel(D));
  Dmin,TM2 := Reduce(Dmin);
  // could also check minimal discriminant... for locally solvability.
  TM := TM2 * TM;
  D2 := Curve(Dmin);
  rm := map<D2 -> D | [ &+[TM`Matrix[i,j]*Pr.i : i in [1..5] ] : j in [1..5] ] >;
  pi := rm * pi;

  Models cat:= [D2];
  Append(~Maps,pi);
end for;

return Models, Maps;
end function; //PhiDescent


