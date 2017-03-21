freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//       HEIGHT PAIRING AND INDEPENDENCE OF NON-TORSION POINTS        //
//                           David Kohel                              //
//                                                                    //
//       (New independence by Mark Watkins, 2011)                     //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose HeightPairing, 1;

PREC:=Precision;

intrinsic HeightPairingMatrix(E::CrvEll : Precision:=0) -> AlgMatElt
    {The height pairing matrix of the Mordell-Weil group of
    the elliptic curve E over the rationals.}

 if Precision eq 0 then pr:=PREC(RealField()); else pr:=Precision; end if;
    require Type(BaseRing(E)) eq FldRat :
       "Argument must be defined over the rationals";
    require IsIntegralModel(E) : "Argument must be an integral model";

    r := Ngens(TorsionSubgroup(E));
    G := Generators(E);
    S := G[[r+1..#G]];
    return HeightPairingMatrix(S : Precision:=pr);
end intrinsic;

intrinsic MordellWeilLattice(E::CrvEll[FldRat]) -> Lat, Map
{The height pairing lattice of the free quotient of the Mordell-Weil
 group of E, together with a map to the elliptic curve.}
 return HeightPairingLattice(E); end intrinsic;

intrinsic HeightPairingLattice(E::CrvEll : Precision:=0) -> Lat, Map
{The height pairing lattice of the free quotient of the Mordell-Weil
 group of E, together with a map to the elliptic curve.}
    r := Ngens(TorsionSubgroup(E));
    G := Generators(E);
    S := G[[r+1..#G]];
 if Precision eq 0 then pr:=PREC(RealField()); else pr:=Precision; end if;
return HeightPairingLattice(S:Precision:=pr); end intrinsic;

intrinsic HeightPairingLattice(S::[PtEll[FldRat]] : Precision := 0) -> AlgMatElt, Map
   {The height pairing lattice of a sequence of independent points on
   an elliptic curve over Q.}

   require not IsEmpty(S) : "The given sequence of points is empty";

 if Precision eq 0 then pr:=PREC(RealField()); else pr:=Precision; end if;
   E := Curve(Universe(S));
   require Type(BaseRing(E)) eq FldRat :
      "Universe of argument 1 must be defined over the rationals";
   require IsIntegralModel(E) : "Argument universe must be an integral model";
   require IsLinearlyIndependent(S) : "Argument is not linearly independent";

   L := LatticeWithGram(HeightPairingMatrix(S : Precision:=pr));
   f := hom< L -> E | v :-> &+[ E | (Integers()!v[i])*S[i] : i in [1..#S] ] >;
   return L, f;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            REGULATOR                               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Regulator(S::[PtEll] : Precision:=0) -> FldReElt
{The regulator of the sequence S of points on an elliptic curve
 over Q, i.e. the determinant of the height pairing matrix.}

 if Precision eq 0 then 
    pr:=PREC(RealField()); 
 else 
    pr:=Precision; 
 end if;
 if IsEmpty(S) then 
    return RealField(pr)!1;
 end if;
 return Determinant(HeightPairingMatrix(S : Precision:=pr)); 
end intrinsic;

intrinsic Regulator(E::CrvEll : Precision:=0) -> FldReElt
{The regulator of the Mordell-Weil generators of an elliptic curve.}
 if Precision eq 0 then pr:=PREC(RealField()); else pr:=Precision; end if;
 return Determinant(HeightPairingMatrix(E : Precision:=pr)); end intrinsic;


intrinsic ConjecturalRegulator(E::CrvEll[FldRat], v::FldReElt) -> FldReElt
{Given the leading L-value computes reg*Sha under the assumptions of B-S--D}
 E:=MinimalModel(E); pr:=Precision(v);
 Ep:=Periods(E : Precision:=pr);
 prodcp:=&*[TamagawaNumber(E,p) : p in BadPrimes(E)]; et:=#TorsionSubgroup(E); 
 ap:=Real(Ep[1])*(Discriminant(E) gt 0 select 2 else 1);
 return v*et^2/(prodcp*ap); end intrinsic;

intrinsic ConjecturalRegulator(E::CrvEll[FldRat] : Precision:=0) -> FldReElt, RngIntElt
{Computes regulator*Sha under the assumptions of B-S--D }
 E:=MinimalModel(E); if Precision eq 0 then pr:=PREC(RealField());
                     else pr:=Precision; end if;
 rk,Ls1:=AnalyticRank(E : Precision:=pr); Ep:=Periods(E : Precision:=pr);
 prodcp:=&*[TamagawaNumber(E,p) : p in BadPrimes(E)]; et:=#TorsionSubgroup(E); 
 ap:=Real(Ep[1])*(Discriminant(E) gt 0 select 2 else 1);
 return Ls1*et^2/(prodcp*ap),rk; end intrinsic;


////////////////////////////////////////////////////////////////////////
//                                                                    //
//               LINEAR DEPENDENCE VIA E/2E                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function two_indep_internal(PTS,n,E) A:=[]; FUNC:=[]; ROOT:=[* *];
 F2:=GF(2); K:=BaseRing(E); OK:=Integers(K);
 E,m:=CubicModel(E); PTS:=[m(PT) : PT in PTS];
 E,m:=IntegralModel(E); PTS:=[m(PT) : PT in PTS];
 n:=Max([n,#PTS+1]); ROWS:=[]; D:=Discriminant(E); p:=101;
 while &or[PT[1] eq 0 : PT in PTS] do
  E,m:=Transformation(E,[1,0,0,1]); PTS:=[m(PT) : PT in PTS]; end while;
 a:=aInvariants(E); f:=Polynomial([a[5],a[4],a[2],1]);
 while true do
  while #ROWS lt n+#PTS do p:=NextPrime(p);
   // maybe not best order of primes ? sort by norm somehow?
   for F in Factorization(p*OK) do P:=F[1];
    if Valuation(D,P) ne 0 then continue; end if;
    if &or[Valuation(PT[1],P) lt 0 : PT in PTS] then continue; end if;
    KK,mp:=ResidueClassField(OK,P);
    fp:=Polynomial([mp(c) : c in Coefficients(f)]); R:=[r[1] : r in Roots(fp)];
    if #R eq 0 then continue; end if;
    G:=func<P,r | mp(P[1])-r eq 0 and mp(P[2]) eq 0
	          select Evaluate(Derivative(fp),r) else mp(P[1])-r>;
    ROWS cat:=[[IsSquare(G(PT,R[1])) select F2!0 else F2!1 : PT in PTS]];
    FUNC cat:=[G]; ROOT cat:=[* R[1] *];
    if #R ge 2 then
     ROWS cat:=[[IsSquare(G(PT,R[2])) select F2!0 else F2!1 : PT in PTS]];
     FUNC cat:=[G]; ROOT cat:=[* R[2] *]; end if; end for; end while;
  M:=Matrix(ROWS); B:=Basis(Kernel(Transpose(M)));
  if #B eq 0 then return true,_; end if; C:=[];
  w:=Vector(ChangeUniverse(Eltseq(B[1]),Integers()));
  w:=Vector([(-1)^Random([0..1])*w[i] : i in [1..#PTS]]); // random +/- 1
  PT:=&+[PTS[i]*w[i] : i in [1..#PTS]];
  if PT eq E!0 then return false,A cat [<w,0>]; end if;
  r:=Random([i : i in [1..#PTS] | w[i] ne 0]); // better than Heights
  if w[r] eq -1 then w:=-w; PT:=-PT; end if;
  DP:=DivisionPoints(PT,2); if #DP eq 0 then n:=n+1; continue; end if;
  j:=Index(PTS,DP[1]);
  if j ne 0 then w[j]:=w[j]-2; return false,A cat [<w,0>]; end if;
  j:=Index(PTS,-DP[1]);
  if j ne 0 then w[j]:=w[j]+2; return false,A cat [<w,0>]; end if;
  PTS[r]:=DP[1]; A cat:=[<w,r>]; o:=Order(PTS[r]);
  if IsOdd(o) then v:=Vector([0:i in [1..#PTS]]);
   v[r]:=Order(PTS[r]); A cat:=[<v,0>]; return false,A; end if; ELIM:=[];
  for x in [1..#ROWS] do p:=Characteristic(Parent(ROOT[x]));
   if Valuation(Denominator(DP[1][1]),p) ne 0 then ELIM cat:=[x];
   else ROWS[x][r]:=F2!(IsSquare(FUNC[x](DP[1],ROOT[x])) select 0 else 1);
    end if; end for; // ELIM;
  ROWS:=[ROWS[i] : i in [1..#R] | not i in ELIM];
  FUNC:=[FUNC[i] : i in [1..#R] | not i in ELIM];
  ROOT:=[* ROOT[i] : i in [1..#R] | not i in ELIM *];
 end while; end function;

function two_indep(PTS,n,E) if #PTS eq 0 then return true,_; end if;
 i:=Index(PTS,E!0);
 if i ne 0 then v:=Vector([0:i in [1..#PTS]]); v[i]:=1; return false,v; end if;
 MPTS:=SequenceToMultiset(PTS);
 for m in Set(MPTS) do
  if Multiplicity(MPTS,m) ne 1 then
   i:=Index(PTS,m); j:=Index(Remove(PTS,Index(PTS,m)),m)+1;
   v:=Vector([0:i in [1..#PTS]]); v[i]:=1; v[j]:=-1; return false,v; end if;
  end for;
 b,A:=two_indep_internal(PTS,n,E); if b then return b,_; end if;
 w,r:=Explode(A[#A]); Prune(~A); W:=w;
 while #A ge 1 do
  w,r:=Explode(A[#A]); Prune(~A); T:=W; W[r]:=0; W:=2*W+T[r]*w; end while;
 return false,W; end function;

function IsLinInd(E,S)
 G,m:=TwoTorsionSubgroup(E);
 b,T:=two_indep(S cat [m(G.i) : i in [1..Ngens(G)]],#S+Ngens(G),E);
 if b then return true,_; end if;
 if Ngens(G) gt 0 and T[#S+1] ne 0 then o:=Order(m(G.1));
  o:=o div Gcd(o,T[#S+1]); T:=T*o; T[#S+1]:=0; end if;
 if Ngens(G) gt 1 and T[#S+2] ne 0 then o:=Order(m(G.2));
  o:=o div Gcd(o,T[#S+2]); T:=T*o; T[#S+2]:=0; end if;
 T:=Eltseq(T); T:=[T[i] : i in [1..#S]]; g:=Gcd(T); assert g ne 0;
 return false,Vector(T); // could do below with mod p maps
 T:=[t div g : t in T]; e:=&+[S[i]*T[i] : i in [1..#S]]; // best possible vec
 return false,Vector(T)*Order(e); end function;

intrinsic IsLinearlyIndependent(P::PtEll,Q::PtEll : Epsilon := 10.0^-6 ) 
-> BoolElt, ModTupRngElt // Epsilon is no longer used
    {Returns true if and only if P is linearly independent of Q over
    the integers; if false then the second return value is a vector
    giving a linear combination of the points which is torsion (and
    thus in the kernel of the height pairing).}

    PS := Parent(P);
    E := Curve(PS);
    require PS eq Parent(Q) : "Arguments must have the same parent.";
    require Type(Epsilon) in {FldReElt} and
        0 lt Epsilon and Epsilon lt 1 :
        "Parameter \"Epsilon\" must be a real number between 0 and 1";
    return IsLinearlyIndependent([P,Q] : Epsilon:=Epsilon);
end intrinsic;

intrinsic IsLinearlyDependent(S::SeqEnum[PtEll] : Epsilon := 10.0^-6 )
-> BoolElt,ModTupRngElt // Epsilon is no longer used
   {Returns true if the points in the sequence S are not independent,
    together with a vector giving a linear combination of the points which
    is a torsion point. Otherwise false}

    flag,v:=IsLinearlyIndependent(S : Epsilon:=Epsilon);
    if flag then return false,_; end if;
    return true,v;
end intrinsic;

// Should work over any field with a height pairing that takes rational values
function IsLinearlyIndependent_gen(S)
    M:=HeightPairingMatrix(S);
    D:=Determinant(M);
    if D ne 0 then return true,_; end if;
    N:=Nullspace(M);
    v:=Eltseq(Basis(N)[1]);
    v:=Vector([Integers()!(l*x): x in v]
	      where l is LCM([Denominator(x): x in v]));
    return false,v;
end function;

intrinsic IsLinearlyIndependent (S::[PtEll] : Epsilon := 10.0^-10)
-> BoolElt, ModTupRngElt // Epsilon no longer used
    {Returns true if and only if the sequence of points is linearly
    independent over the integers; if false then the second return
    value is a vector giving a linear combination of the points which
    is torsion (and thus in the kernel of the height pairing).}
	
    PS := Universe(S);
    E := Curve(PS);
    if ISA(Type(BaseRing(E)), FldFunG) then
        return IsLinearlyIndependent_gen(S); 
    end if;

    type := Type(BaseRing(E));
    require type eq FldRat or ISA(type, FldAlg) :
        "Universe of argument must be a curve over the rationals.";
    return IsLinInd(E,S); // MW Apr 5 2011
end intrinsic;


///////////////////////////////////////////////////////
//                                                   //
// Functions calculating dependence relations for    //
// points on an elliptic-curve over function fields  //
// (or general fields with a height pairing)         //
//                                                   //
///////////////////////////////////////////////////////

intrinsic ReducedBasis(points::Setq[PtEll] : Start:=1)-> SeqEnum[PtEll]
{Same as IndependentGenerators}
   return IndependentGenerators(points : Start:=Start);
end intrinsic;

intrinsic IndependentGenerators(points::Setq[PtEll] : Start:=1) -> SeqEnum[PtEll]
{A sequence of points on an elliptic curve E over a field F that are
 independent in E(F)/E_tors(F), and that generate the same subgroup
 of E(F)/E_tors(F) as the given sequence of points.}
  
   verb := IsVerbose("Height") or IsVerbose("HeightPairing");

   if #points eq 0 then return points; end if;

   require Type(Start) eq RngIntElt and Start ge 1: "'Start' must be a positive integer";

   U := Universe(points);
   if Type(U) ne SetPtEll then
     U := U(BaseRing(U));
   end if;
   E := Curve(U);
   require BaseRing(E) eq Ring(U): "Points must be defined over the base ring of the curve";
   // TO DO: extensions allowed? if so, base change now

   Plist0 := [U| points[i] : i in [1..Start-1]];
   Plist  := [U| points[i] : i in [Start..#points]];

   for i in [1..#Plist] do
     if verb then print "adding point ",i+Start-1,": ",Plist[i]; end if;
     Append(~Plist0, Plist[i]);
     flag, v := IsLinInd(E, Plist0);
     if flag then
       if verb then print "points are independent, rank increases to ",#Plist0; end if;
     else
       if Abs(v[#Plist0]) eq 1 then
         if verb then print "new point is dependent on previous ones"; end if;
         Plist0:=[U| Plist0[j] : j in [1..#Plist0-1]];
       else
         if verb then print "Dependency relation ",v," gaining index ",Abs(v[#Plist0]); end if;
         minvi,mini:=Min([vi eq 0 select 1000 else Abs(vi):vi in Eltseq(v)]);
         if minvi eq 1 then // easy way
           if verb then print "Point ",mini," is redundant, discarding..."; end if;
           Plist0:=[U| Plist0[j] : j in [1..#Plist0] | j ne mini];
           if verb then print "New generators: ",Plist0; end if;
         else
           if verb then print "no redundant points, rearranging..."; end if;
           _,_,Q:=SmithForm(Matrix(v));
           Q:=Q^(-1);  // Q is unimodular with v as its top row
           Plist0:=[U| &+[Q[j,k]*Plist0[k] : k in [1..#Plist0]] :j in [2..#Plist0]];
           if verb then print "New generators: ",Plist0; end if;
         end if;
       end if;
     end if;
   end for;
   return Plist0;
end intrinsic;

