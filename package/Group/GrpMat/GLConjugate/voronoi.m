freeze;

/**********************************************************
* Enumerating perfect forms and deciding conjugacy in     *
* GL(n, Z). Based on J.Opgenorth, W. Plesken, T. Schulz;  *
* Crystallogrphic Algorithms and Tables, Acta Cryst A54,  *
* 517 -- 531. 
*                                                         *
* March 2010, Markus Kirschmer                            *
*                                                         *
**********************************************************/

import "../../../Lattice/Lat/sublat.m" : sublattices, identify_field;

declare attributes GrpMat : PerfectForms;

QQ:= Rationals();
ZZ:= Integers();

PerfectFormsRecord:= recformat<
  Forms,
  Rays,
  Complete,
  FormSpace,
  QToZ,
  Columns,
  Stabs,
  Connectors,
  Norm,
  NormB
>;


function Inv(f)
  signs:= {* Sign(d) : d in Diagonal(OrthogonalizeGram(f)) *};
  return < signs, 0 in signs select 0 else Determinant(f) >;
end function;

function SortRays(R)
  U:= Universe(R);
  Invs:= [ Inv(f) : f in R ];
  Is:= []; Fs:= [U | ]; Rs:= [ PowerSet(U) | ];
  for s in Sort(Setseq(Set(Invs))) do
    idx:= Indices(Invs, s);
    Append(~Is, <s, #idx>);
    if #idx eq 1 then 
      Append(~Fs, R[idx[1]]);
    else
      Append(~Rs, {R[i] : i in idx});
    end if;
  end for;
  return <SequenceToMultiset(Is), Fs, Rs>;
end function;

RaySequence:= func< R | R[2] cat Setseq( &join R[3] ) >;

function myisom(L1, Rays1, L2, Rays2)
   if Rays1[1] ne Rays2[1] then return false, _; end if;
   return IsIsometric(L1, Rays1[2], Rays1[3], L2, Rays2[2], Rays2[3]);
end function;

order_mod := function(g, o, S)
  for d in Divisors(o) do
    if g^d in S then return d; end if;
  end for;
  error "Impossible failure";
end function;

redgen := function(G)
  if Ngens(G) le 2 then return G; end if;
  gens := [G.i: i in [1 .. Ngens(G)]];
  ords := [Order(x): x in gens];
  S := sub<G | >;
  repeat
    _, p := Max(ords);
    S := sub<G | S, gens[p]>;
    ords := [order_mod(gens[i], ords[i], S): i in [1 .. #gens]];
    assert ords[p] eq 1;
  until #S eq #G;
  return S;
end function;

function myauto(L, Rays)
  AA:= AutomorphismGroup(L, Rays[2], Rays[3]);
  return redgen(AA);
end function;


// G acts through h: SxG->S. We find generators for the stabilizer in G of some X \in S.
// G is usually infinite! But the orbit of X is not.
function MyStabGens(G, h, X)
  n:= Ngens(G);
  Orbit:= {@ X @};
  Path:= [ Id(G) ];
  Stab:= [];
 
  i:= 0;
  while i lt #Orbit do
    i+:= 1;
    for j in [1..n] do
      x:= Path[i] * G.j;
      Xx:= h(X, x);
      idx:= Index(Orbit, Xx);
      if idx eq 0 then
        Include(~Orbit, Xx);
        Append(~Path, x);
      else
        x:= x * Path[idx]^-1; 
        assert h(X, x) eq X;
        if not IsOne(x) and x notin Stab and x^-1 notin Stab then
          Append(~Stab, x);
        end if;
      end if;
    end for;
  end while;

  return Stab;
end function;

function MyNorm(N, G)
  return MyStabGens(N, func<GG, n | GG^n>, G );
end function;

function MyCent(N, G)
  return MyStabGens(N, func<GG, n | [ ninv * g * n: g in GG ] where ninv:= n^-1>, [ Generic(G) | G.i : i in [1..Ngens(G)] ]);
end function;


function OrbitReps(A, Rays)
  // ARGH. WHY can't I make a GSet form a matrix group ???!!!
  Rays:= IndexedSet(RaySequence(Rays));
  Agen:= GeneratorsSequence(A);
  ATgen:= [ Transpose(a) : a in Agen ];
  Ps:= [ []^^#Agen ];
  for i in [1..#Rays] do
    for j in [1..#Agen] do
      X:= Agen[j] * Rays[i] * ATgen[j];
      Append(~Ps[j], Index(Rays, X));
    end for;
  end for;

  Orbs:= Orbits( sub< Sym(#Rays) | Ps > );
  return Rays[ [ Rep(x) : x in Orbs ] ];
end function;


function reduce(X)
  if Type(BaseRing(X)) ne RngInt then
    d1:= Denominator(X);
    X:= Matrix(ZZ, d1*X);
  else
    d1:= 1;
  end if;
  d2:= GCD(Eltseq(X));
  if d2 eq 1 then return X, d1/1; end if;
  return X div d2, d1/d2;
end function;

function xAxtr(x,A)
  return (Vector(x) * A * Matrix(1, Eltseq(x)))[1];
end function;


// now we start.


// This is a blatant copy of the corresponding CARAT function.
function vor_neighbor(L, X)
  A:= GramMatrix(L);
  minA:= Minimum(L);

  // First calculate Form N = lm * L + rm * X, with N positiv definite and min(N) < lm * minA
  lu := 1; ru := 0;
  lo := 0; ro := 1;
  found := false;
  repeat
    lm := lu + lo;
    rm := ru + ro;
    N:= lm * A + rm * X;
    if IsPositiveDefinite(N) then
      N:= LatticeWithGram(N);
      if Minimum(N) lt lm * minA then
        found:= true;
      else
        lu := lm; ru := rm;
      end if;
    else
     lo := lm; ro := rm;
    end if;
  until found;

  /************************************************************************\
  | Let y be a shortest vector of N. Then
  |     lm * min(A) > yNy^{tr} = lm * yAy^{tr} + rm * yXy^{tr}
  |  Now yAy^{tr} > min(A) and yXy^{tr} < 0.
  |  Calculate the rational number p/q = (minA - yAy^{tr}) / (yXy^{tr}) >= 0.
  |  Then y (q * A + p * X) y^{tr} = q * minA
  |  Replace N by q * A + p X.
  |  If min(N) = q * min(A) we are done, otherwise repeat
  \************************************************************************/

  repeat
    y:= ShortestVectors(N : Max:= 1)[1];
    // calculate Ay =   y A y^{tr}
    // calculate Xy = - y x y^{tr}
    Ay :=  xAxtr(y,A);
    Xy := -xAxtr(y,X);

    //calculate the new N
    Ay -:= minA;
    d := GCD(Ay, Xy);
    if d ne 1 then
      Ay div:= d;
      Xy div:= d;
    end if;

    N:= LatticeWithGram(Xy * A + Ay * X);
  until Minimum(N) eq Xy*minA;

  // *lc = Xy; *rc = Ay;
  d:= GCD(Eltseq(GramMatrix(N)));
  if d ne 1 then 
    return LatticeWithGram( GramMatrix(N) div d );
  else
    return N;
  end if;
end function;


function first_perfect(T : PositiveDefinite:= 0)
  n:= Ncols(T[1]);
  if #T eq (n*(n+1)) div 2 then
    return LatticeWithGram(GramMatrix(Lattice("A", n)));
  end if;
  P:= PositiveDefinite cmpeq 0 select T[1] else PositiveDefinite;
  while not IsPositiveDefinite(P) do
    P:= &+[ Random([-100..100]) * t: t in T ];
  end while;
  P:= reduce(P);

  L:= LatticeWithGram(P : CheckPositive:= false);
  S:= ShortestVectors(L);
  K:= Kernel(Matrix(QQ, [ [ (Vector(s)*t*Matrix(1, Eltseq(s)))[1] : s in S ] : t in T ] ));

  while Dimension(K) ne 0 do
    vprint Voronoi: "Dim of Kernel:", Dimension(K); 
    M:= reduce(&+[ x[i] * T[i] : i in [1..#T] | x[i] ne 0 ] where x:= K.1);
    L:= vor_neighbor(L, IsPositiveSemiDefinite(M) select -M else M);
    S:= ShortestVectors(L);
    K:= Kernel(Matrix(QQ, [ [ (Vector(s)*t*Matrix(1, Eltseq(s)))[1] : s in S ] : t in T ] ));
  end while;

  return L;
end function;


function Rays(L, F)
//  L: Magma; F:Magma;
  SV:= ShortestVectorsMatrix(L);
  SVtr:= Transpose(SV);
  Norms:= Transpose(Matrix([ Diagonal( SV * f * SVtr ) : f in F ])); 
  RemoveRowContents(~Norms);
  Ineqs:= Setseq(Seqset(RowSequence(Norms)));
  vprint Voronoi: #Ineqs, "inequalities in dimension", #F;
  C:= ConeWithInequalities( ChangeUniverse( Ineqs, ToricLattice(#F) ) );
  vtime Voronoi: List:= MinimalRGenerators(C);
  List:= [ reduce( &+ [ e[j] * F[j] : j in [1..#F] | e[j] ne 0] where e:= Eltseq(R)) : R in List ];
  assert Rank(Matrix( [ Eltseq(R) : R in List ] )) eq #F;
  return SortRays(List);
end function;


// N(B(G)) / B(G) acts faithfully on the form space of G.
// This is used to reduce the number of additional generators.
function reduce_gens(pf, N)
  if not IsEmpty(N) then
    n:= Nrows(pf`FormSpace);
    d:= Nrows(N[1]);
    N:= Setseq(Set(N));
    F:= [ Matrix(d, Eltseq(pf`FormSpace[i])) : i in [1..n] ];
    X:= [];
    cols:= pf`Columns;
    for n in N do
      X cat:= [ Eltseq(n * f * ntr)[cols] : f in F ] where ntr:= Transpose(n);		// This is the action of n^-1. But who cares?
    end for;
    S:= Matrix(ZZ, Matrix(QQ, X) * pf`QToZ);

    List:= {@ @};
    elim:= 0;
    for i in [#N .. 1 by -1] do
      X:= RowSubmatrix(S, (i-1)*n+1, n);
      if IsOne(X) or X in List or X^-1 in List then
        elim +:= 1;
        Remove(~N, i);
      else
        Include(~List, X);
      end if;
    end for;
    vprint Voronoi: "Eliminated", elim, "generators by form space action.";
  end if;
  return N;
end function;

lat2form:= func< Ls | [ Matrix(ZZ, GramMatrix(l)) : l in Ls ] >;

intrinsic PerfectForms(G :: GrpMat[RngInt] : Limit:= Infinity()) -> []
{Compute the perfect forms of G up to the action of the normalizer of the Bravais group.}

  if Type(Limit) ne Infty then requirege Limit, 1; end if;

  pf:= assigned G`PerfectForms select G`PerfectForms else rec< PerfectFormsRecord | Complete:= false >;
  if assigned pf`Forms and ((assigned pf`Complete and pf`Complete) or (Limit le #pf`Forms)) then return lat2form(pf`Forms); end if;

  if not assigned pf`FormSpace then
    F:= SymmetricForms(G);
    if #F eq 1 then			// This case is very easy. Just set up the record and leave.
      pf`FormSpace:= Matrix(ZZ, [ Eltseq(F[1]) ] );
      pf`Forms:= [ LatticeWithGram( F[1] : CheckPositive:= false ) ];
      pf`Rays:= [ < 0, F, [ PowerSet(Universe(F)) | ] > ];
      pf`Complete:= true;
      pf`QToZ:= Matrix(QQ, 1, 1, [1]);
      pf`Columns:= [1];
      pf`NormB:= [];
      G`PerfectForms:= pf;
      return lat2form(pf`Forms);
    end if;

    // The Q-Basis F is NOT a Z-Basis of all integral G-invariant forms.
    // Thus we should get rid of denominators first and then LLL-reduce to get small entries.
    H:= Matrix( [Eltseq(f) : f in F] );
    S, P:= SmithForm( H );
    H:= P*H;
    for i in [i : i in [1..#F] | S[i,i] ne 1] do
      H[i]:= Vector(H[i] div S[i,i]);
    end for; 
    pf`FormSpace:= LLL(H);
    delete H;
    // Now get EchelonForm over Q, and remember which columns are steps.
    // It makes it easy to solve F = x*FormSpace later on.
    NF, X:= EchelonForm( ChangeRing(pf`FormSpace, QQ) );
    pf`QToZ:= X;
    pf`Columns:= [ Depth(NF[i]) : i in [1..#F] ];
    delete NF, X;
  end if;
  F:= [ Matrix(Degree(G), Eltseq(pf`FormSpace[i])) : i in [1..Nrows(pf`FormSpace)] ];

  if not assigned pf`Forms then
    vtime Voronoi: P:= first_perfect(F : PositiveDefinite:= PositiveDefiniteForm(G));
    pf`Forms:= [P]; 
    pf`Rays:= [Rays(P, F)];
    pf`Stabs:= [];
    pf`Connectors:= [];
  end if;

  inspected:= #pf`Stabs;
  while (inspected lt #pf`Forms) and (Limit gt #pf`Forms) do
    inspected +:= 1;
    vprint Voronoi: "Testing number", inspected, "out of", #pf`Forms;
    L:= pf`Forms[inspected];
    A:= myauto(L, pf`Rays[inspected]);
    Append(~pf`Stabs, A);
    for R in OrbitReps(A, pf`Rays[inspected]) do
      if not IsPositiveSemiDefinite(R) then
        assert not IsNegativeSemiDefinite(R);
        Q:= vor_neighbor(L, R);
        RQ:= Rays(Q, F);
        for i in [1..#pf`Forms] do
          ok, T:= myisom(Q, RQ, pf`Forms[i], pf`Rays[i]);
          if ok then
            Append(~pf`Connectors, T);
            continue R;
          end if;
        end for;
        Append(~pf`Forms, Q);
        Append(~pf`Rays, RQ);
        if Limit le #pf`Forms then break; end if;
      end if;
    end for;
  end while;
  pf`Complete:= inspected eq #pf`Forms;

  // Get generators of the normalizer of B(G) now. It does not cost much.
  if pf`Complete then
    pf`NormB:= reduce_gens(pf, &cat [GeneratorsSequence(s) : s in pf`Stabs] cat pf`Connectors);
  end if;

  G`PerfectForms:= pf;
  return lat2form(pf`Forms);
end intrinsic;


// Let N normalize B(G)=B(H). Then G^N is finite. This function finds some n in N s.t. G^n=H
function FindInOrbit(N, G, H)
  if G eq H then return true, N ! 1; end if;
  Orbit:= {@ G @};
  Words:= [ [ZZ | ] ];
  i:= 0;
  while i lt #Orbit do
    i +:= 1;
    X:= Orbit[i];
    for j in [1..Ngens(N)] do
      Y:= X^N.j;
      if Y eq H then return true, &*[ N | N.k : k in Words[i] ] * N.j; end if;
      Include(~Orbit, Y);
      if #Orbit gt #Words then Append(~Words, Append(Words[i], j) ); end if;
    end for;
  end while;
  return false, _;
end function;


intrinsic NormalizerGLZ(G :: GrpMat[RngInt] : IsBravais:= false) -> GrpMat
{Computes the normalizer of a finite subgroup of GL(n,Z) in GL(n,Z).}

  require IsFinite(G) : "The group must be a finite integral matrix group.";

  if not assigned G`PerfectForms or not assigned G`PerfectForms`Norm then
    // This case takes too long otherwise.
    if forall{g : g in Generators(G) | IsScalar(g) } then return Generic(G); end if;

    if IsBravais then
      B:= G;
    else
      B:= BravaisGroup(G);
      IsBravais:= #B eq #G;
    end if;

    // Compute the perfect forms and trigger the normalizer computation
    _:= PerfectForms(G);
    vprint Voronoi: "Found", #G`PerfectForms`NormB, "additional generators.";
    if IsEmpty(G`PerfectForms`NormB) then
      N:= IsBravais select G else Normalizer(B, G);
    else
      N:= sub< Generic(G) | B, G`PerfectForms`NormB >;	// The normalizer of B in GL(n,Z). 
//      N: Magma;
//      GetSeed();
//      "finite start";
      if not IsBravais then
//        if IsFinite(N) then		// This takes way too long.
        if false then
          vprint Voronoi: "Normalizer is finite. Calling the corresponding intrinsic now.";
          N:= Normalizer(N, G);
        else
          vprint Voronoi: "Normalizer of Bravais group found. Starting stabilizer computation.";
          NBG:= IsBravais select G else Normalizer(B, G);	// N_B(G) = N_GL(n,Z)(G) \cap B
          // Reduce the Normalizer using the form space action.
          // This computes the normalizer modulo NBG. So add NBG again.
          N:= sub< Generic(G) | NBG, reduce_gens(G`PerfectForms, MyNorm(N, G)) >;
        end if;
      end if;
    end if;

    if assigned G`PerfectForms then
      G`PerfectForms`Norm:= N;
    else
      G`PerfectForms:= rec< PerfectFormsRecord | Norm:= N >;
    end if;
    delete N;
  end if;
  
  return G`PerfectForms`Norm;
end intrinsic;


intrinsic CentralizerGLZ(G :: GrpMat[RngInt] : IsBravais:= false) -> GrpMat
{Computes the centralizer of a finite subgroup of GL(n,Z) in GL(n,Z).}

  require Type(BaseRing(G)) eq RngInt and IsFinite(G) : "The group must be a finite integral matrix group.";

  // This case takes too long otherwise.
  if forall{g : g in Generators(G) | IsScalar(g) } then return Generic(G); end if;

  if IsBravais then
    B:= G;
  else
    B:= BravaisGroup(G);
    IsBravais:= #B eq #G;
  end if;

  // Compute the perfect forms and trigger the normalizer computation
  _:= PerfectForms(G);
  vprint Voronoi: "Found", #G`PerfectForms`NormB, "additional generators.";
  if IsEmpty(G`PerfectForms`NormB) then
    return IsBravais select Center(G) else Centralizer(B, G);
  end if;

  N:= sub< Generic(G) | B, G`PerfectForms`NormB >;  // The normalizer of B in GL(n,Z).
//      if IsFinite(N) then           // This takes way too long.
  if false then
    vprint Voronoi: "Normalizer is finite. Calling the corresponding intrinsic now.";
    return Centralizer(N, G);
  end if;

  vprint Voronoi: "Normalizer of Bravais group found. Starting stabilizer computation.";
  CBG:= IsBravais select Center(G) else Centralizer(B, G);       // C_B(G) = C_GL(n,Z)(G) \cap B
  // Reduce the Centralizer using the form space action.
  // This computes the normalizer modulo CBG. So add CBG again.
  return sub< Generic(G) | CBG, reduce_gens(G`PerfectForms, MyCent(N, G)) >;
end intrinsic;


nfound:= function(G)
  if not assigned G`PerfectForms or not assigned G`PerfectForms`Forms then 
    return <0, false>;
  end if;
  return <#G`PerfectForms`Forms, G`PerfectForms`Complete>;
end function;

intrinsic IsBravaisEquivalent(G :: GrpMat[RngInt], H :: GrpMat[RngInt]) -> BoolElt, GrpMatElt
{Tests whether the Bravais groups B(G) and B(H) are conjugate in GL(n,Z). If so, the second return value x satisfies B(G)^x == B(H).}

  require Degree(G) eq Degree(H) and IsFinite(G) and IsFinite(H) : 
    "The groups must be finite integral matrix groups of the same degree.";

  // In this stupid case, there are too many perfect forms.
  scalarG:= forall{g : g in Generators(G) | IsScalar(g)};
  scalarH:= forall{g : g in Generators(H) | IsScalar(g)};
  if scalarG ne scalarH then return false, _;
  elif scalarG then return true, Generic(G) ! 1; end if;

  // The numbers of forms will be computed anyway.
  if NumberOfSymmetricForms(G) ne NumberOfSymmetricForms(H) or
     NumberOfAntisymmetricForms(G) ne NumberOfAntisymmetricForms(H) then
    vprint Voronoi: "Different dimensions of form spaces.";
    return false, _;
  end if;

  // If at least one of the groups has a complete set of perfect forms, we can compare numbers somewhat
  nG:= nfound(G);
  nH:= nfound(H);
  if (nG[2] and nG[1] lt nH[1]) or (nH[2] and nH[1] lt nG[1]) then
    vprint Voronoi: "Different numbers of perfect forms.";
    return false, _;
  end if;

  // Switch G and H if appropriate
  switchGH:= nG[2] and not nH[2];
  if switchGH then
    tmp:= G; G:= H; H:= tmp; delete tmp;
  end if;

  // get one perfect form of G and all of H
  _:= PerfectForms(G : Limit:= 1);
  P1:= G`PerfectForms`Forms[1];
  R1:= G`PerfectForms`Rays[1];
  _:= PerfectForms(H);
  Forms:= H`PerfectForms`Forms;

  // do the obvious
  for i in [1..#Forms] do
    ok, T:= myisom(Forms[i], H`PerfectForms`Rays[i], P1, R1);
    if ok then 
      return true, Generic(G) ! (switchGH select T^-1 else T);
    end if;
  end for;
  return false, _;
end intrinsic;


// this should go into the generic IsGLConjugate intrinsic ...
intrinsic IsGLZConjugate(G :: GrpMat[RngInt], H :: GrpMat[RngInt]) -> BoolElt, GrpMatElt
{Tests whether the finite subgroups G and H of GL(n,Z) are conjugate in GL(n,Z). If so, the second return value x satisfies G^x == H.}

  require Degree(G) eq Degree(H) and IsFinite(G) and IsFinite(H) :
    "The groups must be finite integral matrix groups of the same degree.";

  if #G ne #H then return false, _; end if;

  // In this stupid case, there are too many perfect forms.
  scalarG:= forall{g : g in Generators(G) | IsScalar(g)};
  scalarH:= forall{g : g in Generators(H) | IsScalar(g)};
  if scalarG ne scalarH then return false, _;
  elif scalarG then return true, Generic(G) ! 1; end if;

  // test other invariants as you wish, then
  ok, x:= IsBravaisEquivalent(G, H);
  if not ok then return false, _; end if;

  vprint Voronoi: "Corresponding Bravais groups are equivalent.";
  Gold:= G;
  Hold:= H;

  // Solve (G^x)^n=H or (G^n)=H^(x^-1) ???
  takeH:= assigned H`PerfectForms and H`PerfectForms`Complete;
  if takeH then
    B:= BravaisGroup(H);
    NormB:= H`PerfectForms`NormB;
    G:= G^x;
  else
    B:= BravaisGroup(G);
    NormB:= G`PerfectForms`NormB;
    H:= H^(x^-1);
  end if;

  if IsEmpty(NormB) then
    vprint Voronoi: "Testing conjugacy in the Bravais group is sufficient.";
    ok, n:= IsConjugate(B, G, H);
  else
    vprint Voronoi: "Enumerating orbits of G in N(B(H))";
    // N is the normalizer of the Bravais group B(H)=B(G) in GL(n, Z).
    N:= sub< Generic(B) | B, NormB >;
    ok, n:= FindInOrbit(N, G, H);
  end if;

  if ok then
    x:= takeH select x*n else n*x;
    assert Gold^x eq Hold;
    return true, x;
  end if;
  return false, _;
end intrinsic;


function test_cand(G, cand)
  G:= ChangeRing(G, QQ);
  M:= GModule(G);
  N:= GModule(G, [Matrix(QQ, g): g in cand]);
  return IsIsomorphic(M, N);
end function;


// this should go into the generic IsGLConjugate intrinsic ...
intrinsic IsGLQConjugate(G :: GrpMat, H :: GrpMat: Al:= "") -> BoolElt, GrpMatElt
{Tests whether the finite subgroups G and H of GL(n,Q) are conjugate in GL(n,Q). If so, the second return value x satisfies G^x == H.}

  require Type(BaseRing(G)) in {FldRat, RngInt} and IsFinite(G) and
          Type(BaseRing(H)) in {FldRat, RngInt} and IsFinite(H) and
          Degree(G) eq Degree(H):
    "The groups must be finite rational matrix groups of the same degree.";

  if #G ne #H then return false, _; end if;

  if {* <g[1], g[2], Trace(g[3]) >: g in Classes(G) *} ne {* <g[1], g[2], Trace(g[3]) >: g in Classes(H) *} then
    return false, _;
  end if;
  // TODO: Test some more properties?

  if Al cmpeq "" then
    Al:= Degree(G) le 4 select "ZClasses" else "Aut"; 
  end if;

  case Al:
    when "ZClasses":
      Hold:= ChangeRing(H, QQ);
      if BaseRing(H) eq QQ then 
        H, TH:= IntegralGroup(H);
        TH:= Matrix(QQ, TH)^-1;
      else
        TH:= 1;
      end if;
 
      Z, Ts:= ZClasses(G);
      Ts:= &cat Ts;
      for i in [1..#Z] do
        ok, T:= IsGLZConjugate(Z[i], H);
        if ok then
          T:= GL(Degree(G), QQ) ! (Matrix(QQ, Ts[i])^-1 * Matrix(QQ, T) * TH);
          assert ChangeRing(G, QQ)^T eq Hold;
          return true, T;
        end if;
      end for;
      return false, _;

    when "Aut": 
      ok, phi:= IsIsomorphic(G, H);
      if not ok then return false, _; end if;

      // Who came up with this insane outer Aut story?
      genH:= [ G.i @ phi: i in [1..Ngens(G)] ];
      delete phi;
      A:= AutomorphismGroup(H);
      AFP, phi:= FPGroup(A);
      O, psi:= OuterFPGroup(A);
      P, tau:= PermutationGroup(O);
      for p in P do
        h:= ((p @@ tau) @@ psi) @ phi;
        ok, T:= test_cand(G, [ g @ h : g in genH ]);
        if ok then 
          return true, GL(Degree(G), QQ) ! T;
        end if;
      end for;
      return false, _;
    else
      error "Unknown algorithm";
  end case;
end intrinsic;


function get_primes(G)
  if Degree(G) le 6 then return PrimeDivisors(#G); end if; 		// This suffices for subgroups of GL(6,Z).

  vprintf Voronoi: "get list of primes:";

  P:= Set(PrimeDivisors(#G));
  C:= CentreOfEndomorphismRing(ChangeRing(G, QQ));
  _, Cs:= CentralIdempotents(C);

  for c in Cs do
    if Dimension(c) eq 1 then continue; end if;
    R:= Integers(Domain(identify_field(c)));
    Cl, h:= NarrowClassGroup(R);
    S:= sub< Cl | [ d[1] @@ h : d in Decomposition(R, p), p in P ] >;
    p:= 1;
    while #S ne #Cl do
      p:= NextPrime(p);
      if p in P then continue; end if;
      for d in Decomposition(R, p) do
        x:= d[1] @@ h;
        if x notin S then 
          S:= sub< Cl | S, x >;
          Include(~P, p);
          if #S eq #Cl then break; end if;
        end if;
      end for;
    end while;
  end for;
  vprint Voronoi: " We are using the primes", P, "for sublattice computation.";
  
  return Sort(Setseq(P));
end function;


intrinsic ZClasses(G :: GrpMat : Homogeneously:= false ) -> [], []
{Splits the GL(n,Q)-conjugacy class of the finite rational matrix group G into GL(n,Z)-conjugacy classes.}

  require Type(BaseRing(G)) in {RngInt, FldRat} and IsFinite(G) :
     "The group must be a finite rational matrix group.";

//  Gold := G;
  d:= Degree(G);

  // Take care of this stupid case and do not waste time enumerating perfect forms.
  if forall{g : g in Generators(G) | IsScalar(g) } then
    return [ G ], [ [IdentityMatrix(ZZ, d)] ];
  end if;

  if Type(BaseRing(G)) eq FldRat then
    G, T1:= IntegralGroup(G);
  else
    T1:= 1;
  end if;

  I:= CentralIdempotents( CentreOfEndomorphismRing(ChangeRing(G, QQ)) );

  if #I ne 1 then
    Mn:= MatrixRing(ZZ, d);
//    Ls:= < BasisMatrix(PureLattice(Lattice( i ))) : i in I >;
    Ls:= < Matrix(QQ, BasisMatrix(Lattice( i ))) : i in I >;
    B:= VerticalJoin(Ls);

    if /*B notin Mn or not IsUnit(Mn ! B)*/ not IsOne(B) then
      T1:= B * T1;
      //B:= Matrix(QQ, B);
      Binv:= B^-1;
      Ls:= [ Mn | B * i * Binv : i in I ];
      G:= ChangeRing(ChangeRing(G ,QQ)^(GL(d, QQ) ! Binv), ZZ);			// This copies order, base, strong gens.
    else
      Ls:= ChangeUniverse(I, Mn);
    end if;
    Gen:= ChangeUniverse(GeneratorsSequence(G), Mn);
  else
    Gen:= GeneratorsSequence(G);
    Ls:= [];
    Homogeneously:= true;
  end if;

  // Use the sublattice algorithm to get the "homogeneously decomposable" lattices.
  S, Grps:= sublattices(Gen cat Ls, get_primes(G), Infinity(), Infinity() : zclass:= G, action:= NormalizerGLZ(G));
  vprint Voronoi: "Found", #Grps, "classes of homogeneously decomposable lattices.";

  if Homogeneously then return Grps, [ [s * T1] : s in S ]; end if;

  // Now the sublattices with the correct projections yield the desired groups.
  Result:= [];
  Ts:= [];
  GLd:= GL(d, QQ);
  P:= PrimeDivisors(#G);
  for i in [1..#S] do
    Gen:= GeneratorsSequence(Grps[i]);
    T:= sublattices(Gen, P, Infinity(), Infinity() : action:= NormalizerGLZ(Grps[i]), proj:= Ls, needint:= false);
    Append(~Result, Grps[i]);			// This copy already knows its normalizer etc.
    Result cat:= [ ChangeRing(GG^((GLd ! T[j])^-1), ZZ) : j in [2..#T] ] 
      where GG := ChangeRing(Grps[i], QQ);
    Append(~Ts, [ t * X : t in T ] where X:= S[i] * T1);
  end for;

  //assert forall{i: i in [1..#Result] | Result[i] eq ChangeRing(ChangeRing(Gold ,QQ)^((GL(d, QQ) ! TT[i])^-1), ZZ)} where TT:= &cat Ts;
  return Result, Ts;
end intrinsic;

/*
load "qtoz";
for i in [1..#Groups], j in [1..#Groups[i]] do <i,j>; P:= PerfectForms( Groups[i,j]); end for;
for i in [1..#Groups] do i; Z:= ZClasses(Groups[i,1]); assert #Groups[i,1] le 10 or &and [ 1 eq #[ H: H in Z | IsGLZConjugate(H, g) ] : g in Groups[i] ]; end for;
*/
