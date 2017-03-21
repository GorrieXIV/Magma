freeze;

//////////////////////////////////////////////////////////////////////////
//
//  Brandt matrices over Z and F_q[t]
//
//  Markus Kirschmer (and Steve Donnelly)
//  November 2012
//
//////////////////////////////////////////////////////////////////////////


import "p1.m" : MyProjectiveLine, PLIndex;

import "../ModFrmHil/hecke.m" :
  dimension_lower_bound, 
  reduction_mod_random_large_split_prime;


declare type ModBrdtNew [ModBrdtNewElt];

declare attributes ModBrdtNew:
  MaximalOrder,
  Conductor,
  Dimension,
  Space,
  IdealClasses,			// Right ideal class reps of the max. order
  Grams,			// Canonical Gram matrices of the left orders of these reps
  Indices,			// The index of the left order of the reps in Grams.
  ResidueClassMap,
  P1,
  P1Orbits,
  Hecke,
  HeckeBound,
  PartialHecke,
  HeckeAlgebraPrimes,
  QuaternionOrder,
  Ideals,
  Lattices;

declare type ModBrdtNewElt;

declare attributes ModBrdtNewElt:
    Parent,
    Element;


gram:= func< L | Type(BaseRing(L)) eq RngInt select ReducedGramMatrix(L) else ReducedGramMatrix(L : Canonical) >;

function UnitFactor(R)
  if Type(R) eq RngInt then return 2; end if;
  return #BaseRing(R) - 1;
end function;

function SetupElement(P, e);
  elt:= New(ModBrdtNewElt);
  elt`Parent:= P;
  elt`Element:= P`Space ! e;
  return elt;
end function;

//////////////////////////////////////
// Magma required interface functions

intrinsic Print(M::ModBrdtNew)
  {internal}
  printf "Brandt module (new) of level (%o,%o) and dimension %o",
    Discriminant(M`MaximalOrder), M`Conductor, M`Dimension;
end intrinsic;

intrinsic Print(e::ModBrdtNewElt)
  {internal}
  printf "%o", e`Element;
end intrinsic;

intrinsic Parent(e::ModBrdtNewElt) -> ModBrdtNew
  {internal}
  return e`Parent;
end intrinsic;

intrinsic IsCoercible(M::ModBrdtNew, e::.) -> BoolElt, ModBrdtNewElt
  {internal}
  T:= Type(e);
  case T:
    when ModBrdtNewElt: 
      if IsIdentical(Parent(e), M) then return true, e; end if;
    when SeqEnum:
      ok:= #e eq M`Dimension and Type(Universe(e)) eq RngInt;
    when ModTupRngElt:
      ok:= Degree(e) eq M`Dimension and Type(BaseRing(Parent(e))) eq RngInt;
    else ok:= false;
  end case;
  if ok then
    return true, SetupElement(M, e);
  end if;
  return false, "Invalid coercion";
end intrinsic;

///////////////////////////////////////
// Operations on Brandt module elements
// TODO: Deal with ambient spaces?

intrinsic '+'(e::ModBrdtNewElt, f::ModBrdtNewElt) -> ModBrdtNewElt
{internal}
  P:= Parent(e);
  require IsIdentical(P, Parent(f)):
    "Elements must have the same parents";
  return SetupElement(P, e`Element + f`Element);
end intrinsic;

intrinsic '-'(e::ModBrdtNewElt, f::ModBrdtNewElt) -> ModBrdtNewElt
{internal}
  P:= Parent(e);
  require IsIdentical(P, Parent(f)):
    "Elements must have the same parents";
  return SetupElement(P, e`Element - f`Element);
end intrinsic;

// allow other scalars?
intrinsic '*'(e::ModBrdtNewElt, s::RngIntElt) -> ModBrdtNewElt
{internal}
  return SetupElement(Parent(e), s*e`Element);
end intrinsic;

intrinsic '*'(s::RngIntElt, e::ModBrdtNewElt) -> ModBrdtNewElt
{internal}
  return SetupElement(Parent(e), s*e`Element);
end intrinsic;

intrinsic '*'(e::ModBrdtNewElt, H::AlgMatElt[RngInt]) -> ModBrdtNewElt
{internal}
  P:= Parent(e);
  require Nrows(H) eq P`Dimension:
    "The operator has the wrong degree";
  return SetupElement(P, e`Element * H);
end intrinsic;

///////////////////////////////////////
// The Brandt module interface

intrinsic Dimension(M::ModBrdtNew) -> RngIntElt
  {Dimension of the Brandt module M}
  return M`Dimension;
end intrinsic;

intrinsic Basis(M::ModBrdtNew) -> RngIntElt
  {The basis of the Brandt module M}
  return [ M ! x: x in Basis(M`Space) ];
end intrinsic;

intrinsic Level(M::ModBrdtNew) -> RngElt
  {The level of the Brandt module M}
  return Discriminant(M`MaximalOrder) * M`Conductor;
end intrinsic;

intrinsic Discriminant(M::ModBrdtNew) -> RngElt
  {The discriminant of the quaternion algebra attached to the Brandt module M}
  return Discriminant(M`MaximalOrder);
end intrinsic;

intrinsic Conductor(M::ModBrdtNew) -> RngElt
  {The Eichler level of the quaternion order attached to the Brandt module M}
  return M`Conductor;
end intrinsic;

intrinsic InnerProductMatrix(M::ModBrdtNew) -> AlgMatElt
  {The natural inner product on the Brandt module M}
  return InnerProductMatrix(M`Space);
end intrinsic;

intrinsic QuaternionOrder(M::ModBrdtNew) -> AlgQuatOrd
  {The quaternion order attached to the Brandt module M}
  N:= M`Conductor;
  if N eq 1 then 
    return M`MaximalOrder;
  elif not assigned M`QuaternionOrder then
    MO:= M`MaximalOrder;
    R:= BaseRing(MO);
    B:= Basis(MO);
    k:= quo< R | N >;
    m:= Matrix(k, [ Eltseq(b @ h) : b in B ]) where h:= M`ResidueClassMap;
    s:= Solution(m, Matrix(k, 4, [1,0,0,0, 0,1,0,0, 0,0,0,1]));
    s:= ChangeRing(s, R);
    O:= QuaternionOrder([ N*b: b in B ] cat [ MO ! Eltseq(s[i]) : i in [1..3] ]);
    assert IsEichler(O) and Discriminant(O) eq Level(M);
    M`QuaternionOrder := O;
  end if;
  return M`QuaternionOrder;
end intrinsic;

// The builtin meet has to find the correct order etc. 
// This doesn't.
function mymeet(I, J, O)
  B:= BasisMatrix(I, O);
  C:= BasisMatrix(J, O);
  d:= LCM(Denominator(B), Denominator(C));
  R:= BaseRing(O);
  ImeetJ:= Image(Matrix(R, d*B)) meet Image(Matrix(R, d*C));
  return rideal< O | [ O | [e/d: e in Eltseq(b)] : b in Basis(ImeetJ) ] >;
end function;

intrinsic Ideals(M::ModBrdtNew) -> []
  {The quaternion ideals corresponding to the basis of the Brandt module M}
  N:= M`Conductor;
  if N eq 1 then 
    return M`IdealClasses;
  elif not assigned M`Ideals then
    O:= QuaternionOrder(M);
    R:= BaseRing(O);
    B:= Basis(O);
    k:= quo< R | N >;
    m:= Matrix(k, [ Eltseq(b @ h) : b in B ]) where h:= M`ResidueClassMap;
    s:= Solution(m, Matrix(k, 4, [0,1,0,0, 0,0,0,1]));
    e12:= O ! Eltseq(ChangeRing(s[1], R));
    e22:= O ! Eltseq(ChangeRing(s[2], R));
    NMO:= [ N*b : b in Basis(M`MaximalOrder) ];
    Js:= [];
    I:= M`IdealClasses; n:= #I;
    Indices:= M`Indices;
    C:= Classes(M`P1);
    Reps:= {@ <i, o[1]> : o in M`P1Orbits[Indices[i]], i in [1..n] @};
    for j in { r[2]: r in Reps } do
      Js[j]:= rideal< O | Append(NMO, e12*(R!C[j,1,1]) + e22*(R!C[j,2,1])) >;
      assert RightOrder(Js[j]) eq O and Norm(Js[j]) eq N;
    end for;
    M`Ideals:= [ mymeet(I[r[1]], Js[r[2]], O) : r in Reps ];
  end if;
  return M`Ideals;
end intrinsic;


function QuotientSplittingData0(OH, OHB, pr, e)
   // Given a maximal order OH, a prime ideal pr and an integer e, this return a sequence of matrices
   // (M_i) in M_2(OK/pr^e) which is a basis of the reduction OH\otimes OK/pr^e\cong M_2(OK/pr^e) as
   // an (OK/pr^e)-algebra.

   assert IsPrime(pr);
//   assert forall{m: m in [1..4] | Valuation(OHB[m][1], pr) ge 0};	// FIX

   OK:= BaseRing(OH); R:=quo<OK|pr^e>;
   embed_mats:=[];
   _, fp2, gp2:=pMatrixRing(OH, pr: Precision:=e+20);
   for m:=1 to 4 do
      mat_ents:=Eltseq(fp2(OHB[m]));			// FIX
      mat:=Matrix(OK, 2, [OK!(R!(OK!(s@@gp2))): s in mat_ents]);
      Append(~embed_mats, mat);
   end for;

   return embed_mats;
end function;

function QuotientSplittingData(OH, d)
   // Given a maximal order OH and an ideal d, this return a sequence of matrices (M_i) in M_2(OK/d) which
   // form a basis of the reduction OH\otimes (OK/d)\cong M_2(OK/d) as an (OK/d)-algebra.

   OK:= BaseRing(OH);
   if d eq 1 then
      OHBd:=Basis(OH); splitting_mats:=[MatrixRing(OK, 2)!1: m in [1..4]];
   else
      div_fact:=Factorization(d);
      div_seq:=[ fact[1]^fact[2] : fact in div_fact];
      OHBd:= Basis(OH);
      embed_mats:=[QuotientSplittingData0(OH, OHBd, div_fact[l][1], div_fact[l][2]): l in [1..#div_fact]];
      splitting_mats:=[];
      for l:=1 to 4 do
         split_mat_ents:=[];
         for m:=1 to 4 do
            elt_red_comp:=[Eltseq(embed_mats[n][l])[m]: n in [1..#div_fact]];
            Append(~split_mat_ents, CRT(elt_red_comp, div_seq));
         end for;
         Append(~splitting_mats, Matrix(OK, 2, split_mat_ents));
      end for;
   end if;
   return OHBd, splitting_mats;
end function;

function _ResidueMatrixRing(OH, d)
   A:= Algebra(OH);
   K:= BaseField(A);
   OHB, mats := QuotientSplittingData(OH, d);
   cobi := Matrix(K, [Eltseq(A ! s): s in OHB]) ^ -1;

   OK := BaseRing(OH);
   Rd := quo<OK|d>;

   // Use coercion OK!Rd!x because x may have denominators (prime to d)
   function split_map(q)
      c := Vector(K, Eltseq(A!q)) * cobi;
      mat := Matrix(OK, 2, 2, []);
      for l := 1 to 4 do
         mat +:= (OK!Rd!c[l]) * mats[l];
      end for;
      return mat;
   end function;

   return split_map; 
end function;


intrinsic ResidueMatrixRing(OH::AlgQuatOrd, d::RngElt) -> AlgMat, Map
   {Given a (maximal) order OH in a quaternion algebra H over the rationals or F_q(x),
    and an integral element of the base ring that is coprime to
    the discriminant of OH, this returns a residue map OH -> Mat_2(O/d).  This map
    can be applied to any element of H that is integral locally at primes dividing d.}

   // check cache
   R:= BaseRing(OH);
   if not assigned OH`ResidueMatrixRings then
      OH`ResidueMatrixRings := AssociativeArray(R);
   end if;
   bool, m := IsDefined(OH`ResidueMatrixRings, d);
   if bool then
      return Codomain(m), m;
   end if;

   H := Algebra(OH);

   require d in R :
          "The second argument must be an element of the base ring of the first argument";
   require GCD(d, Discriminant(H)) eq 1 :
          "The quaternion order does not split at the given ideal";

   if Type(R) eq RngInt then d:= Abs(d); else d:= Normalize(d); end if;

   split_map := _ResidueMatrixRing(OH, d);

   MO2 := MatrixRing(R, 2);
   m := map< H -> MO2 | q :-> split_map(q) >;

   OH`ResidueMatrixRings[d] := m;
   return MO2, m;
end intrinsic;

intrinsic ResidueMatrixRing(OH::AlgQuatOrd[RngInt], d::RngInt) -> AlgMat, Map
{"} //"
   return ResidueMatrixRing(OH, Generator(d));
end intrinsic;

get_support:= function(D, N)
  P:= { f[1] : f in Factorization(D) };
  DN:= D*N;;
  if Type(D) eq RngIntElt then
    p:= 2; while DN mod p eq 0 do p:= NextPrime(p); end while;
  else
    F:= BaseRing(Parent(D));
    tries:= 0;
    repeat 
      tries+:= 1;
      p:= RandomIrreduciblePolynomial(F, (tries div 10)+1);
    until DN mod p ne 0;
  end if;
  return Include(P, p);
end function;

intrinsic BrandtModule(M::AlgQuatOrd, N::RngElt) -> ModBrdtNew
{The Brandt module of an Eichler order of conductor N inside the maximal order M}
  A:= Algebra(M);
  require IsMaximal(M) and IsDefinite(A) : 
    "The order must be a maximal order in a definite quaternion algebra";
  R:= BaseRing(M);
  factor:= UnitFactor(R);
  ok, N:= IsCoercible(R, N);
  require ok and GCD(N, Discriminant(M)) eq 1: "Level must be coprime to the discriminant";

  rat:= Type(R) eq RngInt;
  N:= rat select Abs(N) else Normalize(N);
  I:= RightIdealClasses(M : Support:= get_support(Discriminant(M), N));

  // Setup some information on the left orders
  Grams:= {@@}; Indices:= [];
  n:= #I; i:= 0; LOInds:= [1];
  repeat
    L:= LeftOrder(I[i+1]);
    t:= #TwoSidedIdealClassGroup(L);
    assert i+t-1 le #I and forall{ j: j in [i+2..i+t] | LeftOrder(I[j]) eq L };
    G:= gram(L); assert G notin Grams;
    Include(~Grams, G);
    Indices cat:= [(#Grams)^^t];
    i +:= t;
    Append(~LOInds, i+1);
  until i eq n;

  BM:= New(ModBrdtNew);
  BM`MaximalOrder:= M;
  BM`Conductor:= N;
  BM`IdealClasses:= I;
  BM`Grams:= Grams;
  BM`Indices:= Indices;

  if N eq 1 then
    // If the level is trivial, we are done
    BM`Dimension:= #I;
    U:= [ #UnitGroup( LeftOrder(I[LOInds[i]]) ) div factor : i in [1..#Grams] ];
    UnitSizes:= [ U[Indices[i]] : i in [1..#I] ];
  else
    assert forall{ i: i in I | GCD(R!Norm(i), N) eq 1 };

    // Now we work out the orbits of the unit groups of the left orders on P1.
    k, kh:= quo< R | N >;
    RMR, h:= ResidueMatrixRing(M, N);

    P:= MyProjectiveLine( k : Vector:= false );
    C:= Classes(P);

    P1Orbits:= []; UnitSizes:= [];
    dim:= 0;
    for j in [1..#Grams] do
      i:= LOInds[j];
      L:= LeftOrder(I[i]);
      multiples:= LOInds[j+1] - i;
      if not rat and Degree(ReducedGramMatrix(L)[2,2]) ne 0 then
        Orb:= [ {@ x @} : x in [1..#P] ];	// could be optimized away?
        UnitSizes cat:= [ 1^^(multiples * #Orb) ];
      else
        U, Uh:= UnitGroup(L : ModScalars);
        n:= Ngens(U);
        Gens:= [ Matrix(k, 2, [kh(x) : x in Eltseq(g) ]) where g:=  U.i @ Uh @ h : i in [1..n] ];
        Images:= [ [ PLIndex(P, g*(C[j])) : j in [1..#P] ] : g in Gens ];
        S:= sub< Sym(#P) | Images >;
        Orb:= Orbits(S);
        Orb:= [ IndexedSet(o) : o in Orb ];
        UnitSizes cat:= &cat[ [(#UnitGroup(L) div (factor*#o) ) : o in Orb]^^multiples ];
      end if;
      Append(~P1Orbits, Orb);
      dim +:= #Orb * multiples;
    end for;

    BM`Dimension:= dim;
    BM`ResidueClassMap:= h;
    BM`P1:= P;
    BM`P1Orbits:= P1Orbits;
  end if;
  BM`Space:= RSpace(Integers(), BM`Dimension, DiagonalMatrix(UnitSizes));
  return BM;
end intrinsic;

// testing
function BM(dmf, p)
  O:= QuaternionOrder(dmf); 
  I:= Ideals(dmf); n:= #I;
  M:= MatrixRing(Integers(), n) ! 0;
  for i in [1..n] do
    P:= MaximalRightIdeals(LeftOrder(I[i]), p);
    for J in P do
      idl:= rideal< O | [ x*y: x in Basis(J), y in Basis(I[i]) ] >;
      ok:= exists(j){j: j in [1..n] | IsIsomorphic(idl, I[j]) };
      assert ok;
      M[i,j] +:= 1;
    end for;
  end for;
  return M;
end function;

forward mytps;

lat:= func< G | Type(BaseRing(G)) eq RngInt select LatticeWithGram(G) else DominantDiagonalForm(G: Canonical:= false) >;
function ProductLattices(B)
  if not assigned B`Lattices then
    R:= BaseRing(B`MaximalOrder);
    I:= Ideals(B); n:= #I;
    Lats:= [];
    for i in [1..n] do
      O:= LeftOrder(I[i]);
      Append(~Lats, lat(GramMatrix(O)));
      nrm:= Norm(I[i]);
      BC:= [ Conjugate(b) : b in Basis(I[i]) ];
      for j in [i+1..n] do
        J:= rideal< O | [ x*y : x in Basis(I[j]), y in BC ] >;
        Append(~Lats, lat(Matrix(R, GramMatrix(J) / (Norm(I[j]) * nrm))));
      end for;
    end for;
    B`Lattices:= Lats;
  end if;
  return B`Lattices;
end function;

function CountVectors(L, Primes)
  max:= Primes[#Primes];
  if Type(L) eq Lat then
    TS:= ThetaSeries(L, 2*max);
    return [ Coefficient(TS, 2*p) div 2 : p in Primes ];
  else
    S:= ShortVectors(L, Degree(max));
    S:= {* Normalize(s[2]): s in S *};
    factor:= #BaseRing(Universe(Primes))-1;
    return [ Multiplicity(S, p) div factor : p in Primes ];
  end if;
end function;

procedure HeckeUpTo(BM, Bnd)
  if BM`HeckeBound ge Bnd then return; end if;
  R:= BaseRing(BM`MaximalOrder);
  if Type(R) eq RngInt then
    Primes:= PrimesUpTo(Bnd);
  else
    K:= BaseRing(R);
    Primes:= &cat [ Setseq(AllIrreduciblePolynomials(K, i)): i in [1..Bnd] ];
  end if;
  Primes:= [ p: p in Primes | not IsDefined(BM`Hecke, p) ];
  if IsEmpty(Primes) then return; end if;
  L:= ProductLattices(BM);
  U:= Diagonal(InnerProductMatrix(BM`Space));
  n:= #U; k:= 1; 
  H:= [ MatrixRing(Integers(), n) | 0^^#Primes ];
  for i in [1..n] do
    for j in [i..n] do
      count:= CountVectors(L[k], Primes);
      for l in [1..#Primes] do
        H[l,i,j]:= count[l] / U[j];
        H[l,j,i]:= count[l] / U[i];
      end for;
      k +:= 1;
    end for;
  end for;
  for l in [1..#Primes] do BM`Hecke[Primes[l]]:= H[l]; end for;
  BM`HeckeBound:= Bnd;
end procedure;

intrinsic HeckeOperator(M::ModBrdtNew, n::RngElt : Columns:= [], Al:= "Direct") -> Mtrx
{The Hecke operator T_n of the Brandt module M}
  R:= BaseRing(M`MaximalOrder);
  ok, n:= IsCoercible(R, n);
  require ok and n ne 0: 
    "The second parameter must be a non-zero element of the base ring";
  Columns:= Set(Columns);
  require Columns subset {1..M`Dimension} : "Wrong Columns option";
  require Al in {"Direct", "Forms"}:
    "The algorithm must be either \"Direct\" or \"Forms\"";
  
  rat:= Type(R) eq RngInt;
  n:= rat select Abs(n) else Normalize(n);

  if not assigned M`Hecke then
    M`Hecke:= AssociativeArray(R);
    M`Hecke[1]:= IdentitySparseMatrix(Integers(), M`Dimension);
    M`HeckeBound:= 0;
  end if;

  ok, x:= IsDefined(M`Hecke, n);
  if ok then return Matrix(x); end if;

  if not (IsEmpty(Columns) or #Columns eq M`Dimension) then
    require true or IsPrime(n : Proof:= false) : 
      "The Columns option requires the second argment to be prime";
    return mytps(M, n : Columns:= Columns);
  end if;

  T:= 1;
  F:= Factorization(n);
  if Al eq "Forms" then
    // Fill the Hecke array with all prime ideals up to the last prime.
    HeckeUpTo(M, rat select F[#F,1] else Degree(F[#F,1]));
  end if;
  for f in F do
    p:= f[1];
    if Discriminant(M`MaximalOrder) mod p eq 0 then 
      ok, U:= IsDefined(M`Hecke, p);
      if not ok then
        U:= mytps(M, p);
        M`Hecke[p]:= U;
      end if;
      U:= U^f[2];
    elif M`Conductor mod p eq 0 then
      ok, U:= IsDefined(M`Hecke, p^f[2]);
      error if not ok, "not supported";
    else
      ok, U:= IsDefined(M`Hecke, p^f[2]);
      if not ok then
        if not IsDefined(M`Hecke, p) then 
          U:= mytps(M, p);
          M`Hecke[p]:= U;
        end if;
        factor:= rat select p else #BaseRing(R)^Degree(p);
        for i in [2..f[2]] do
          if not IsDefined(M`Hecke, p^i)  then
            U:= M`Hecke[p] * M`Hecke[p^(i-1)] - Matrix(factor * M`Hecke[p^(i-2)]);
            M`Hecke[f[1]^i]:= U;
          end if;
        end for;
      end if;
    end if;
    T:= T*U;
  end for; 
  return T;
end intrinsic;

procedure RecoverColumns(~H, D, Columns)
  Rows:= {1..#D} diff Columns;
  for j in Columns do
    for i in Rows do
      H[i,j]:= (H[j,i] * D[i]) div D[j];
    end for;
  end for;
end procedure;

function mytps(M, p : Columns:={})
  assert IsPrime(p);
// start := Cputime();
// "Computing the Brandt matrix for the maximal order at the prime", p;
  O:= M`MaximalOrder;
  I:= M`IdealClasses; n:= #I;
  R:= BaseRing(O);

  Grams:= M`Grams; Indices:= M`Indices;
  maximal:= M`Conductor eq 1;
  if not maximal then
    // the internal ordering of the ideals
    Reps:= {@ <i, o[1]> : o in M`P1Orbits[Indices[i]], i in [1..n] @};
  end if;

  all:= IsEmpty(Columns) or #Columns eq M`Dimension;
  if all then
    columns:= {1..n};
    if not maximal then Columns:= {1..#Reps}; end if;
  else
    columns:= maximal select Columns else { Reps[i,1] : i in Columns };
  end if;

  // Do we already have partial results?
  if assigned M`PartialHecke and IsDefined(M`PartialHecke, p) then
    if maximal then
      oldc, TA, pIdeals, LOIndices:= Explode(M`PartialHecke[p]);
      all:= all or #(columns join oldc) eq n;
    else
      oldc, TA, pIdeals, LOIndices, oldC, TT:= Explode(M`PartialHecke[p]);
      all:= all or #(Columns join oldC) eq M`Dimension;
      Columns:= Columns diff oldC;
      if IsEmpty(Columns) then return TT; end if;
    end if;
//all, columns, oldc;
//if not maximal then "C", Columns; end if;
  else
    TA:= AssociativeArray(car< [1..n], [1..n] >);
    if not maximal then TT:= MatrixRing(Integers(), #Reps) ! 0; end if;
    oldc:= {}; oldC:= {};
    pIdeals:= [* false: i in [1..#Grams] *]; LOIndices:= [];
  end if;
  NeededOrders:= Set(Indices[Setseq(columns)]);

  // Setup the p maximal ideals for the left orders of I.
  j:= 0; 
  for i in [1..#Grams] do
    j:= Index(Indices, i, j+1);
    L:= LeftOrder(I[j]);
    if i in NeededOrders then
      Idls:= MaximalRightIdeals(L, p);
      LOIndices[i]:= [ Index(Grams, gram(LeftOrder(J))) : J in Idls ];
      assert 0 notin LOIndices[i];
      pIdeals[i]:= Idls;
    end if;
  end for;
  // "Setup complete";

//Cputime(start);
  // "Start computing tp[j,i]";
  for j in columns diff oldc do
    t:= Indices[j];
    assert pIdeals[t] cmpne false;
    B:= Basis(I[j]);		// We should use 1/p * I[j]
    for k in [1..#pIdeals[t]] do
      idl:= rideal< O | [ x*b: x in Basis(pIdeals[t,k] ), b in B ] >;
      loidx:= LOIndices[t,k];
      i:= 0; 
      for tmp in [1..n] do 
        if loidx eq Indices[tmp] then
          ok, x:= IsIsomorphic(idl, I[tmp]);
          if ok then i:= tmp; break; end if; 
        end if;
      end for;
      assert i ne 0;
//      assert rideal< O | [ x*b: b in Basis(idl)] > eq I[i];
      x:= x*p;			// Correct error made above
//      JJ:= rideal< O | [ x*b: b in B ] >;
//      rideal< O | [p*b: b in Basis(I[i])]> subset JJ, JJ subset I[i];
      idx:= <j,i>;
      if IsDefined(TA, idx) then Append(~TA[idx], x); else TA[idx]:= [x]; end if;
    end for;
  end for;
//Cputime(start);

  if maximal then
    H:= SparseMatrix(n, n, [ Append(k, #TA[k]) : k in Keys(TA) ]);
    H:= Matrix(H);
    if not all then
      if not assigned M`PartialHecke then M`PartialHecke:= AssociativeArray(); end if;
      M`PartialHecke[p]:= < columns join oldc, TA, pIdeals, LOIndices >;
      D:= Diagonal(InnerProductMatrix(M));
      RecoverColumns(~H, D, columns);
    elif assigned M`PartialHecke and IsDefined(M`PartialHecke,p) then
      Remove(~M`PartialHecke, p);
    end if;
    return H;
  end if;

  // "Recovering the Brandt matrix for level", M`Conductor;
  check:= M`Conductor mod p eq 0;
  P1:= M`P1; S:= BaseRing(P1 ! 1);
  for j in columns do
    tj:= Indices[j];
    for i in [1..n] do
      ok, X:= IsDefined(TA, <j,i>);
      if not ok then continue; end if;
      ti:= Indices[i];
      for x in X do
        mat:= Matrix(S, M`ResidueClassMap(x));
        for o in M`P1Orbits[tj] do
          jidx:= Index(Reps, <j, o[1]>); assert jidx ne 0;
          if jidx notin Columns then continue; end if;
          img:= mat * (P1 ! o[1]);
          if check and (R ! img[1,1]) mod p eq 0 and (R ! img[2,1]) mod p eq 0 then "skip"; continue; end if;
          idx:= PLIndex(P1, img);
          ok:= exists(oo){oo: oo in M`P1Orbits[ti] | idx in oo};
          assert ok;
          iidx:= Index(Reps, <i,oo[1]>); assert iidx ne 0;
          if iidx notin oldC then TT[jidx, iidx] +:= 1; end if;
        end for;
      end for;
    end for;
  end for;

  if not all then
    D:= Diagonal(InnerProductMatrix(M));
    RecoverColumns(~TT, D, Columns);
    if not assigned M`PartialHecke then M`PartialHecke:= AssociativeArray(); end if;
    M`PartialHecke[p]:= < columns join oldc, TA, pIdeals, LOIndices, Columns join oldC, TT >;
  elif assigned M`PartialHecke and IsDefined(M`PartialHecke,p) then
    Remove(~M`PartialHecke, p);
  end if;
  return TT;
end function;

intrinsic BrandtModuleDimension(D::RngElt, N::RngElt) -> RngIntElt
{Dimension of the Brandt module with discriminant D and conductor N}
  R:= Parent(D);
  require R cmpeq Parent(N) : "The parameters lie in the same ring";
  T:= Type(R);
  if T eq RngUPol then
    F:= BaseRing(R);
    require IsField(F) and IsFinite(F) : "The base ring is not suported";
    q:= #F;
    mass:= 1/(q^2-1);              // Zeta(-1) * mass from \infty
    _Norm:= func< x | q^Degree(x) >;
  elif T eq RngInt then
    _Norm:= func< x | x >;
    mass:= 1/12;
  else 
    require false : "The base ring is not supported";
  end if;

  DF := Factorization(D);
  NF := Factorization(N);
  require IsOdd(#DF) and forall{p: p in DF | p[2] eq 1} : 
    "The discriminant must be a product of an odd number of distinct primes";
  require GCD(D,N) eq 1 : "The parameters must be coprime";

  DF:= [ p[1] : p in DF ];
  mass *:= &*[ Integers()  |  _Norm(p)-1 : p in DF ] * 
           &*[ Rationals() | (_Norm(p[1])^-1+1) : p in NF ] * _Norm(N);

  // add correction term coming from local embedding numbers
  if T eq RngUPol then
    // trivial case
    if forall{p: p in DF | IsOdd(Degree(p))} and
       forall{p: p in NF | IsEven(Degree(p[1]))} then
      mass +:= q/(q+1) * 2^(#DF + #NF - 1);
    end if;  
  else
    e2:= 1; e3:= 1;             // Embedding numbers of Q(i) and Q(sqrt(-3))

    // Lets get rid of the prime 2 first
    if 2 in DF then
      Exclude(~DF, 2);
      e3:= 2;
    elif exists(x){x: x in NF | x[1] eq 2} then
      Exclude(~NF, x);
      if x[2] gt 1 then e2:= 0; end if;
      e3:= 0;
    end if;
    // now if e2 != 0, it only depends on the odd primes as follows.
    e2:= e2 ne 0 and forall{d: d in DF | d    mod 4 eq 3} 
                 and forall{x: x in NF | x[1] mod 4 eq 1} select 2^(#DF + #NF) else 0;

    // get rid of 3
    if e3 ne 0 then
      Exclude(~DF, 3);			// only yields a factor of 1.
      if exists(x){x: x in NF | x[1] eq 3} then
        Exclude(~NF, x);
        if x[2] gt 1 then e3:= 0; end if;
      end if;
    end if;
    // now get the contribution of the primes > 3 to e3.
    e3*:= e3 ne 0 and forall{d: d in DF | d    mod 24 in {5,11,17,23}} 
                  and forall{x: x in NF | x[1] mod 24 in {1, 7,13,19}} select 2^(#DF + #NF) else 0;

    mass +:= e2/4 + e3/3;		// keep your fingers crossed ...
  end if;

  assert IsIntegral(mass);
  return Integers() ! mass;
end intrinsic;


function divisors(F)
  Res:= [ [ Universe(F) | ] ];
  for f in F do
    s:= #Res;
    Res cat:= [ Append(Res[r], <f[1], i>) : r in [1..s], i in [1..f[2]] ];
  end for; 
  return Res;
end function;

function mydiv(F,D)
  for d in D do
    ok:= exists(i){ i : i in [1..#F] | F[i,1] eq d[1] };
    assert ok and F[i,2] ge d[2];
    F[i,2] -:= d[2];
  end for;
  U:= Universe(F)[1];
  return &* [ U | f[1]^f[2] : f in F | f[2] ne 0 ];
end function;

intrinsic BrandtModuleDimensionOfNewSubspace(D::RngElt, N::RngElt) -> RngIntElt
{Dimension of the newspace of a Brandt module of discriminant D and conductor N}
  ok, N := IsCoercible(Parent(D), N);
  require ok : "The arguments are incompatible";
  F:= Factorization(D);
  require GCD(D,N) eq 1 and IsOdd(#F) and forall{ f: f in F | f[2] eq 1 }:
    "The discriminant must be a product of an odd number of distinct primes";

  dim:= 0;
  F:= Factorization(N);
  for d in divisors(F) do
    if exists{f: f in d | f[2] gt 2} then continue; end if;
    c:= (-2)^#{f: f in d | f[2] eq 1};
    dim +:= c * (BrandtModuleDimension(D, mydiv(F, d))-1);
  end for;
  return dim;
end intrinsic;

function HeckeAlgebraPrimes(M) // (M::ModBrdtNew) -> []
// {A small list of primes such that the Hecke operators at these
// primes (together with the identity) generate the Hecke algebra}

  if assigned M`HeckeAlgebraPrimes then
    return M`HeckeAlgebraPrimes;
  end if;

  D:= Discriminant(M);
  N:= Conductor(M);
  F:= Factorization(N);
  dim:= 1 + &+[ BrandtModuleDimensionOfNewSubspace(D, mydiv(F, f)) : f in divisors(F) ];

  R:= BaseRing(M`MaximalOrder);
  rat:= Type(R) eq RngInt;
  if rat then 
    p:= 1;
  else
    p:= R.1;
    FF:= BaseRing(R);
  end if;

  MA:= MatrixAlgebra(Rationals(), M`Dimension);
  Primes:= [ R | ]; Gens:= [];
  S:= sub< MA | Gens >; dimS:= 1;

  while dimS ne dim do
//    <dimS, dim >;
    assert dimS lt dim;
    if rat then
      repeat p:= NextPrime(p); until N mod p ne 0;
    else
      d:= Degree(p); tries:= 0;
      repeat
        tries +:= 1;
        if tries mod 10 eq 0 then d +:= 1; end if; 
        p:= RandomIrreduciblePolynomial(FF, d);
      until N mod p ne 0;
      N *:= p;
    end if;
    H:= MA ! HeckeOperator(M, p);
    S:= sub< MA | Gens, H >;
    
    U, P := reduction_mod_random_large_split_prime(S, Rationals());
    dimU, vec := dimension_lower_bound(U : tries:=2);
    if dimU gt dimS then
      Append(~Primes, p);
      Append(~Gens, H);
      dimS:= dimU;
    end if;
  end while;

  // Now we try to reduce the number of generators.
  // the last generator must stay there.
  t := #Gens;
  inds := [1..t];
  for i in [t-1..1 by -1] do
    Ui := sub< Generic(U) | [U.j : j in inds | j ne i] >;
    if dim eq dimension_lower_bound(Ui : vector:=vec) then
      Exclude(~inds, i);
    end if;
  end for;
  if t ne #inds then
    Primes:= Primes[inds];
    //S:= sub< MA | Gens[inds] >;
  end if;

  M`HeckeAlgebraPrimes:= Primes;
  return Primes;
end function;


intrinsic HeckeEigenvectors(M::ModBrdtNew : Traces:= []) -> SeqEnum[ModBrdtNewElt]
{The common eigenvectors of all elements in the Hecke algebra of M}
  Kernels:= [ VectorSpace(Rationals(), M`Dimension) ];
  P:= HeckeAlgebraPrimes(M);

  for p in P do
    H:= ChangeRing(HeckeOperator(M, p), Rationals());
    if IsEmpty(Traces) then
//printf "Eigenvalues of T_(%o) : ", p; time
      eH:= [ t[1]: t in Eigenvalues(H) ];
//printf "%o Kernels : ", #eH; time
      KH:= [ Kernel(H-e) : e in eH ];
    else
      KH:= [ X : e in Traces | Dimension(X) ne 0 where X:= Kernel(H-e) ];
    end if;
    Kernels:= [ tt : x in Kernels, y in KH | Dimension(tt) ne 0 where tt:= x meet y ];
  end for;
 
  V :=  Sort([ ChangeRing(k.1 * LCM([Denominator(x) : x in Eltseq(k.1)]), Integers()) 
               : k in Kernels | Dimension(k) eq 1 ]);

  return [M | SetupElement(M, v) : v in V];
end intrinsic;


intrinsic HeckeEigenvalue(f::ModBrdtNewElt, p::RngElt) -> RngElt
{For a Hecke eigenform f in a Brandt module, this returns 
the eigenvalue for the Hecke operator at the prime p}

  M := Parent(f);
  v := f`Element;

  j := 0;
  for i := 1 to Ncols(v) do
    if v[i] ne 0 then
      j := i;
      break;
    end if;
  end for;
  assert j gt 0;

  T := HeckeOperator(M, p : Columns:= [j]);
  T := ChangeRing(T, BaseRing(v));
  w := v*T;

  e := w[j]/v[j];

  // if all Columns then
  // R := Parent(e);
  // assert ChangeRing(w,R) eq e*ChangeRing(v,R);

  return e;
end intrinsic;

