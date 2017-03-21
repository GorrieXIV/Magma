freeze;

// Original code: Bernd Souvignier, Jun 1997
// Modified for packages: Allan Steel, Dec 1997 -- Jan 1998
// New version: Markus Kirschmer, Nov 2009


declare type LatLat [LatLatElt];

declare attributes LatLat:
  G, Primes, Constituents, Lattices, Index, Children, Parents, Complete;

declare type LatLatElt;

declare attributes LatLatElt:
  Parent, Number, Endo;

ZZ:= Integers();
QQ:= Rationals();


// The LatLat and LatLatElt interfaces

function MtrxToElt(V, X)
  if BaseRing(X) eq QQ then                                                 
    d:= Denominator(X);                                                     
    X:= Matrix(ZZ, X*d);                                                    
    e:= 1/d;                                                                
  else
    e:= 1/1;
  end if;
  d:= GCD( Eltseq(X) );
  e*:= d;
  X:= HermiteForm(X div d);
  idx:= Index(V`Lattices, X);
  if idx ne 0 then
    x:= New(LatLatElt);
    x`Parent:= V;
    x`Number:= idx;
    x`Endo:= e;
    return true, x;
  end if;
  return false, _;
end function;

intrinsic Print(V::LatLat)
{internal}
  printf "Lattice of %o sublattices", #V`Lattices;
end intrinsic;

intrinsic Print(x::LatLatElt)
{internal}
  if (not assigned x`Endo) or (x`Endo cmpeq 1) then
    printf "sublattice number %o", x`Number;
  else
    printf "sublattice number %o times %o", x`Number, x`Endo;
  end if;
end intrinsic;

intrinsic Parent(x::LatLatElt) -> LatLat
{internal}
  return x`Parent;
end intrinsic;

intrinsic IsCoercible(V::LatLat, i::.) -> BoolElt, LatLatElt
{internal}
  // Integers i simply correspond to the i-th lattice.
  if Type(i) eq RngIntElt then
    if i ge 1 and i lt V`Index[#V`Index] then
      x:= New(LatLatElt);
      x`Parent:= V;
      x`Number:= i;
      return true, x;
    end if;
    return false, "index out of range";
  // If i is a lattice, get its basis matrix.
  elif Type(i) eq Lat then
    i:= BasisMatrix(i);
  end if;
  // If i is a matrix, try to locate it.
  if ISA(Type(i), Mtrx) and Type(BaseRing(i)) in {FldRat, RngInt} and
      #{Ncols(i), Nrows(i), Ncols(V`Lattices[1,1])} eq 1 then
    ok, x:= MtrxToElt(V, i);
    if ok then return true, x; end if;
    return false, "Lattice not found.";
  end if;
  return false, "Illegal coercion";
end intrinsic;

intrinsic '#'(V::LatLat) -> RngIntElt
{internal}
  return #V`Lattices;
end intrinsic;

intrinsic Primes(V::LatLat) -> []
{The primes used for constructing the lattice V of sublattices.}
  return V`Primes;
end intrinsic;

intrinsic Constituents(V::LatLat) -> []
{The constituents used for constructing the lattice V of sublattices.}
  return V`Constituents;
end intrinsic;

intrinsic NumberOfLevels(V::LatLat) -> RngIntElt
{The number of different levels (layers) stored in the lattice V.}
  return #V`Index-1;
end intrinsic;

intrinsic Levels(V::LatLat) -> []
{A sequence where the i-th entry contains the sublattices stored for the (i-1)-th level (layer).}
  idx:= V`Index;
  return [ [V | x: x in[idx[i]..idx[i+1]-1]] : i in [1..#idx-1] ];
end intrinsic;

intrinsic Level(V::LatLat, i::RngIntElt) -> []
{The sublattices stored in the i-th layer.}
  idx:= V`Index;
  requirerange i, 0, #idx-2;
  return ChangeUniverse([idx[i+1]..idx[i+2]-1], V);
end intrinsic;

intrinsic MaximalSublattices(x::LatLatElt) -> [], []
{The maximal sublattices of the element x in a lattice of sublattices.}
  V:= x`Parent;
  lats:= [V| ];
  consts:= [];
  e:= assigned(x`Endo) select x`Endo else 1;
  for ci in V`Children[x`Number] do
    Append(~lats, ci[1]);
    ee:= e * ci[2];
    if ee cmpne 1 then lats[#lats]`Endo:= ee; end if;
    Append(~consts, ci[3]);
  end for;
  return lats, consts;
end intrinsic;

intrinsic MinimalSuperlattices(x::LatLatElt) -> [], []
{The minimal superlattices of the element x in a lattice of sublattices.}
  V:= x`Parent;
  lats:= [V| ];
  consts:= [];
  e:= assigned(x`Endo) select x`Endo else 1;
  for pi in Sort(V`Parents[x`Number]) do
    Append(~lats, pi[1]);
    ee:= e / pi[2];
    if ee cmpne 1 then lats[#lats]`Endo:= ee; end if;
    Append(~consts, pi[3]);
  end for;
  return lats, consts;
end intrinsic;

intrinsic Morphism(x::LatLatElt) -> Mtrx
{The morphism (basis matrix) of the element x in a lattice of sublattices.}
  lat:= x`Parent`Lattices[x`Number];
  if not assigned(x`Endo) or x`Endo cmpeq 1 then
    return lat;
  else
    return lat * x`Endo;
  end if;
end intrinsic;

intrinsic BasisMatrix(x::LatLatElt) -> Mtrx
{"} // "
  return Morphism(x);
end intrinsic;

intrinsic Lattice(x::LatLatElt) -> Lat
{The lattice corresponding to the element x in a lattice of sublattices.}
  lat:= x`Parent`Lattices[x`Number];
  if assigned(x`Parent`G) then
    lat:= LatticeWithBasis(x`Parent`G, lat : CheckIndependent:= false);
  else
    lat:= LatticeWithBasis(lat : CheckIndependent:= false);
  end if;
  if assigned(x`Endo) and x`Endo cmpne 1 then
    lat:= lat * x`Endo;
  end if;
  return lat;
end intrinsic;

intrinsic '+'(x::LatLatElt, y::LatLatElt) -> LatLatElt
{internal}
  require IsIdentical(x`Parent, y`Parent): "The lattices must lie in the same structure.";
  X:= Lattice(Morphism(x));
  Y:= Lattice(Morphism(y));
  ok, x:= MtrxToElt(x`Parent, BasisMatrix(X+Y) );
  if ok then return x; end if;
  error "Sum is not a multiple of a precomputed lattice.";
end intrinsic;

intrinsic 'meet'(x::LatLatElt, y::LatLatElt) -> LatLatElt
{internal}
  require IsIdentical(x`Parent, y`Parent): "The lattices must lie in the same structure.";
  X:= Lattice(Morphism(x));
  Y:= Lattice(Morphism(y));
  ok, x:= MtrxToElt(x`Parent, BasisMatrix(X meet Y) );
  if ok then return x; end if;
  error "Intersection is not a multiple of a precomputed lattice.";
end intrinsic;

intrinsic 'eq'(x::LatLatElt, y::LatLatElt) -> LatLatElt
{internal}
  require IsIdentical(x`Parent, y`Parent): "The lattices must lie in the same structure.";
  X:= Lattice(Morphism(x));
  Y:= Lattice(Morphism(y));
  return X eq Y;
end intrinsic;

intrinsic '!'(R::RngInt, x::LatLatElt) -> RngIntElt
{internal}
  return x`Number;
end intrinsic;



// the sublattice algorithm starts here.

Homs := function(H, E)
// compute orbit representatives for the action of E:= End(N) on H:= Hom(M,N)
// where M and N are both over a finite field and N is simple

// get a basis for the homomorphisms
  B := Basis(H);
  if IsEmpty(B) then return []; end if;

// two homomorphisms differ only by an endomorphism if their column spaces
// are the same
// first extract the homomorphisms having different column images
  T := [ B[1] ];
  I := Image( Transpose(B[1]) );
  for i in [2..#B] do
    J:= Image( Transpose(B[i]) );
    if not J subset I then
      Append(~T, B[i]);
      I := I + J;
    end if;
  end for;

// every homomorphism can be written as sum over T[i]*e, the first non-zero e
// can be normalized to 1
  M := Parent(T[1]);
  HH := [ T[1] ];
  for i in [2..#T] do
    HH := [ h + M!(T[i]*e) : h in HH, e in E ] cat [ T[i] ];
  end for;

  return HH;
end function;

mat:= function(c, T, S)
  X:= T[c[1]];
  if c[2] lt 0 then 
    return HermiteForm(Matrix(ZZ, Matrix(QQ, X) * S[-c[2]]));
  end if;
  return X * c[2];
end function;

sanity_check:= procedure(G, Q, T, P, C, S, Lvlidx, complete)
  n:= #T;
  print "#P == #C == #T:";
  assert( {#P, #C} eq {n} );
  print "parents information is compact:";
  assert( forall{p: p in P | #p eq #Seqset(p)} );
  print "same number of entries in P and C:";
  assert( &+[#c: c in C] eq &+[#p: p in P] ); 
  print "P and C give the same information:";
  assert(
    forall{<i, x> : x in P[i], i in [1..n] | [i, x[2], x[3]] in C[x[1]]} and
    forall{<i, x> : x in C[i], i in [1..n] | [i, x[2], x[3]] in P[x[1]]});
  print "C contains only children:"; assert (forall{<i, x> : x in C[i], i in [1..n] | Image(mat(x, T, [])) subset Image(T[i]) });	// ??

  MZ:= Parent(T[1]);
  if not complete then n:= Lvlidx[#Lvlidx-1]-1; end if;
  for i in [1..n] do
    L:= Matrix(QQ, T[i])^-1;
    CC:= {@ mat(c, T, []) : c in C[i] @};  // ??
    tmp:= [c[3]: c in C[i]];
    assert(#CC eq #C[i]);
    count:= 0;
    for p in Q do
      K:= GF(p);
      M:= RModule([Matrix(K, T[i] * g * L) : g in G]);
      MM:= MaximalSubmodules(M);
      for m in MM do
        Lnew:= HermiteForm( BasisMatrix(Image(VerticalJoin(MZ ! p, Matrix(ZZ, Morphism(m, M))))) * T[i] );
        k:= Index(CC, Lnew);
        assert(k ne 0);
        assert( IsIsomorphic(M/m, S[tmp[k]]) );
      end for;
      count+:= #MM;
    end for;
    assert(#C[i] eq count);
  end for;
  print "all tests passed";
end procedure;


function orbit(X, gens)
  Result:= {@ X @};
  i:= 0;
  while i lt #Result do
    i +:= 1;
    for g in gens do
      Include(~Result, HermiteForm(Result[i] * g));
    end for;
  end while;
  return Result;
end function;

change_basis:= func< G, B | ChangeRing(ChangeRing(G, QQ)^((GL(Degree(G), QQ) ! ChangeRing(B, QQ))^-1), ZZ) >;


function sublattices(G, Q, Limit, Levels : needint, zclass:= false, proj:= [], action:= [], ideals:= [], order:= [])

  // old intrinsic counted Levels differently. So adjust.
  if Type(Levels) ne Infty then Levels +:= 1; end if;

  if zclass cmpne false then
    // We have to find all "almost - decomposable" G-inv. lattices L
    // and return the corresponding groups G(L) up to conjugacy in GL(n,Z).
    Classes:= [ zclass ];
    GG:= [ Matrix(QQ, g) : g in Generators(zclass) ];
    zclass:= true;
    needint:= false;
  end if;
  needint and:= action cmpeq [] and IsEmpty(ideals);

  Mn:= MatrixRing(ZZ, Nrows(G[1]));
  Fp:= [ GF(p): p in Q ];
  T:= {@ Mn | 1 @};			// the sublattices will go here
  pLats:= [ [ <1,1> ] : p in Q ];	// pLat[q, i] == lattices of level i whose index in Z^n is a Q[q]-power
  Lvlidx:= [1,2];			// the i-th level starts with T[Lvlidx[i]]

  if needint then
    Parents := [[]];			// we need only one of them, but to make life easier ... 
    Children:= [[]];
    IdxToInt_p:= {@ {ZZ | } @};		// T[i] == &meet T[IdxToInt_p[Setseq(i)]];
    IdxToInt:= [ <1,1> ];		// T[i] == T[IdxToInt[i,1]] meet T[IdxToInt[i,2]];
    Primes:= [ {Integers() | } ];
  end if;
  
  S:= [];
  Sidx:= [1];
  for i in [1..#Q] do
    S cat:= Constituents(RModule(ChangeUniverse(G, ChangeRing(Mn, Fp[i]))));
    Append(~Sidx, #S+1);
  end for;
  E:= [ EndomorphismRing(s): s in S ];

  Eltproj:=[ ElementaryDivisors(p): p in proj ];

  if action cmpne [] then
    if Type(action) eq GrpMat then
      action:= Generators(action);
    end if;
    action:= [ Matrix(ZZ, a): a in action ];		// Magma does not like the product of matrix * element of GL(n,Z)!
    Orbits:= {@ @};
  end if;

  if IsEmpty(Q) then
    if needint then
      return T, Parents, Children, S, Lvlidx, true;
    else
      return T, true;
    end if;
  end if;

  leave:= false;
  complete:= true;
  currentp:= 1;		// current prime we are working on.
  lvl:= 2;

  repeat
    
    p:= Q[currentp];
    startidx:= #T+1;
    for i in [pLats[currentp, lvl-1,1] .. pLats[currentp, lvl-1,2]] do
      vprintf Sublattices: "constructing maximal sublattices of %o at %o\n", i, p;
      L:= T[i];
      LI:= Matrix(QQ, L)^-1; 
      GM := RModule( [ChangeRing(L*g*LI, Fp[currentp]): g in G] );
      for j in [Sidx[currentp] .. Sidx[currentp+1]-1] do
        H := Homs(AHom(GM, S[j]), E[j]);
        vprint Sublattices: #H, "maximal sublattices with constituent", j;
        for h in H do
          A:= VerticalJoin( ChangeRing(KernelMatrix(h), ZZ), Mn!p );
          Lnew:= HermiteForm( BasisMatrix(Image(A)) * L );

          // first we try to find Lnew or 1/p*Lnew
          elt:= GCD(Eltseq(Lnew));
          if elt ne 1 then
            assert(elt eq p);
            if not needint then continue; end if;
            Lnew div:= p;
          end if;
          k:= Index(T, Lnew);
          if k ne 0 then
            vprintf Sublattices: "Lattice is equal to nr %o times %o\n", k, elt;
            if needint then
              Append(~Parents[k] , [i, elt, j]);
              Append(~Children[i], [k, elt, j]);
            end if;
            continue;
          end if;

          // Is Lnew*order == Z^n?
          if not IsEmpty(order) then
            if HermiteForm(BasisMatrix(Image(VerticalJoin([Lnew * b : b in order])))) ne T[1] then
              vprint Sublattices: "Lattice*order is not L";
              continue;
            end if;
          end if;

          // Does the lattice project correctly?
          if not IsEmpty(proj) and
              exists{j: j in [1..#proj] | ElementaryDivisors(Lnew*proj[j]) ne Eltproj[j]} then
            continue;
          end if;

          // Let's see if Lnew*P^-1 has already been found
          if not IsEmpty(ideals) then
            LQ:= Matrix(QQ, Lnew);
            for PI in ideals[currentp] do
              // if the result is integral, it is above Lnew and under Z^n. Hence already there.
              if forall{b : b in PI | IsCoercible(Mn, LQ * b)} then continue h; end if;
            end for;
          end if;

          // Is the lattice in the orbit of the current level?
          if not IsEmpty(action) then
            if Lnew in Orbits then continue; end if;
            O:= orbit(Lnew, action);
            if #O gt 1 then
              Orbits join:= O;
            end if;
            delete O;
          end if;

          // The lattice is new.
          assert(elt eq 1);

          // Does it give rise to a new Z-class of G?
          if zclass then
            tmp:= change_basis(Classes[1], Lnew);
            if exists{C: C in Classes | IsGLZConjugate(tmp, C) } then
              continue;
            end if;
            Append(~Classes, tmp);
          end if;

          // Are we allowed to insert the new lattice?
          idx:= #T + 1;
          if (idx gt Limit) or (lvl gt Levels) then
            vprintf Sublattices: "Found %o lattices on %o levels. But the given limits were [%o, %o]. Enumeration is incomplete!\n", idx, lvl, Limit, Levels;
            leave:= true;
            complete:= false;
            break i;
          end if;

          vprintf Sublattices: "Found %o under %o with constituent %o at level %o\n", idx, i, j, lvl;
          Include(~T, Lnew);
          if needint then
            Include(~IdxToInt_p, {idx});
            Append(~Parents, [[i, 1, j]]);
            Append(~Children[i], [idx, 1, j]);
            Append(~Children, []);
            Append(~IdxToInt, <1, idx>);
            Append(~Primes, {p});
          end if;
        end for;
      end for;
    end for;
    Append(~pLats[currentp], <startidx, #T>);

    // Now we intersect all lattices I with index a product of previous primes with p-power lattices J.
    // pLat stores the necessary indices to do that
    if currentp ne 1 then 
      lvls:= [i: i in [2..lvl-1] | pLats[currentp, i,1] ne Lvlidx[i] ];
      vprintf Sublattices: "intersecting in level %o up to the prime %o\n", lvl, p;
      for lvlI in lvls do
        lvlJ:= lvl-lvlI+1;
        for i in [Lvlidx[lvlI]..pLats[currentp,lvlI,1]-1] do
          I:= Image(T[i]);
          for j in [pLats[currentp, lvlJ,1] .. pLats[currentp, lvlJ,2]] do
            Lnew:= HermiteForm(BasisMatrix(I meet Image(T[j])));

            // Does the lattice project correctly?
            if not IsEmpty(proj) and
                exists{j: j in [1..#proj] | ElementaryDivisors(Lnew*proj[j]) ne Eltproj[j]} then
              continue;
            end if;

            if not IsEmpty(action) then
              if Lnew in Orbits then continue; end if;
              Orbits join:= orbit(Lnew, action);
            end if;

            // A new class?	(this test cannot be removed (see group #3232))
            if zclass then
              tmp:= change_basis(Classes[1], Lnew);
              if exists{C: C in Classes | IsGLZConjugate(tmp, C) } then
                continue;
              end if;
              Append(~Classes, tmp);
            end if;

            // The lattice is new. Are we allowed to insert it?
            if (#T ge Limit) or (lvl gt Levels) then
              vprintf Sublattices: "Found %o lattices on %o levels. But the given limits were [%o, %o]. Enumeration is incomplete!\n", #T+1, lvl, Limit, Levels;
              leave:= true;
              complete:= false;
              break lvlI;
            end if;

            assert(Lnew notin T);
            Include(~T, Lnew);
            if needint then
              Include(~IdxToInt_p, IdxToInt_p[i] join IdxToInt_p[j]);
              Append(~Primes, Include(Primes[i], p));
              Append(~IdxToInt, <i,j>);
              Append(~Parents, []);		// will be updated at the end
              Append(~Children, []);
            end if;
          end for;
        end for;
      end for;
    end if;

    currentp:= 1 + (currentp mod #Q);
    // Level complete. So adjust.
    // Note that we CANNOT check (lvl ge Level) to bail out since we don't know if the next level 
    // gives new lattices or not, i.e. are we complete?
    if currentp eq 1 then
      Orbits:= {@ @};			// The group action is currently supposed to act on layers. Hence we can reset the Orbits.
      if Lvlidx[lvl] eq #T+1 then
        leave:= true;			// there are no more lattices to go.
      else
        Append(~Lvlidx, #T+1);
        lvl+:= 1;
      end if;
    end if;

  until leave;

  if Lvlidx[#Lvlidx] ne #T+1 then
    Append(~Lvlidx, #T+1);
  end if;
 
  if (#Q gt 1) and needint then
    // update parent information top to bottom
    for idx in [2..#T] do
      i,j:= Explode(IdxToInt[idx]);

      p:= Rep(Primes[j]); 
      assert(Primes[j] eq {p});

      parents:= {@ @};
      assert({j} eq IdxToInt_p[j]);
      for p1 in Parents[i] do
        assert p1[2] ge 0;
        if (p eq p1[2]) or (p in Primes[p1[1]]) then continue; end if;
        x:= Index(IdxToInt_p, Include(IdxToInt_p[p1[1]], j));
        if (x ne 0) then
          Include(~parents, [x, p1[2], p1[3]]);
          Include(~Children[x], [idx, p1[2], p1[3]]);
        end if;
      end for;
      Int:= IdxToInt_p[i];
      for p2 in Parents[j] do
        assert p2[2] ge 0;
        if not IsDisjoint(Primes[i], p2[2] lt 0 select Primes[p2[1]] else Include(Primes[p2[1]], p2[2])) then continue; end if;
        x:= Index(IdxToInt_p, IdxToInt_p[p2[1]] join Int);
        if (x ne 0) then 
          Include(~parents, [x, p2[2], p2[3]]);
          Include(~Children[x], [idx, p2[2], p2[3]]);
        end if;
      end for;

      Parents[idx]:= Sort(Setseq(parents));
      delete parents;
    end for;
  end if;

  if zclass then
    return T, Classes;
  elif needint then
//    sanity_check(G, Q, T, Parents, Children, S, Lvlidx, complete);
    return T, Parents, Children, S, Lvlidx, complete;
  else
    return T, complete;
  end if;
end function;


// user interface

UniverseZ:= func< X | Type(Universe(X)) eq RngInt >;
BaseRingZ:= func< X | Type(BaseRing(X)) eq RngInt >;
BRUZ:= func< X | not IsEmpty(X) and Type(BaseRing(Universe(X))) eq RngInt >;

function proj_ok(p, n: B:= 1)
  if Type(p) ne SeqEnum then return false, _; end if;
  if IsEmpty(p) then return true, []; end if;
  if not ISA(Type(p[1]), Mtrx) or Type(BaseRing(p[1])) notin {FldRat, RngInt} or Nrows(p[1]) ne n then
    return false, _;
  end if;
  if B cmpne 1 then 
    B:= Matrix(QQ, B);
    m:= Nrows(B);
    R:= RowSpace(B);
    BB:= BasisMatrix(Complement(Generic(R), R));
    B:= VerticalJoin(B, BB);
    p:= [ B * Matrix(QQ, x) * BI : x in p ] where BI:= B^-1;
    if exists{x: x in p | not IsZero(Submatrix(x, 1, m+1, m, n-m)) } then
      return false, _;
    end if;
    p:= [ Submatrix(x, 1,1, m,m) : x in p ];
    n:= m;
  end if;
  return CanChangeUniverse(p, MatrixRing(ZZ, n));
end function;

intrinsic Sublattices( G::GrpMat, Q::Setq: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> [], BoolElt
{ The G-invariant sublattices of some G-lattice L which are not
  contained in p*L for any p in Q and whose index in L is a product of elements of Q.
  G must be a subgroup of GL(n,Z) or generators of some Z-order in M(n,Z).
  If L is not provided then the standard lattice Z^n is chosen.
  The second return value indicates whether the enumeration is complete or not.
}

  require BaseRingZ(G): "Base ring of argument 1 must be Z";
  require UniverseZ(Q) and forall{p: p in Q | p ge 1 and IsPrime(p)}:
      "Argument 2 must contain positive primes";
  if Type(Limit) ne Infty then requirege Limit, 1; end if;
  if Type(Levels) ne Infty then requirege Levels, 0; end if;
  ok, Projections:= proj_ok(Projections, Degree(G));
  require ok: "The projections are not valid.";

  Q:= Setseq(Set(Q));
  Gen:= IsTrivial(G) select [G ! 1] else GeneratorsSequence(G); 
  S, complete:= sublattices(Gen, Q, Limit, Levels : needint:= false, proj:= Projections);
  return [LatticeWithBasis(G, s: CheckIndependent:= false) : s in S], complete;
end intrinsic;

intrinsic Sublattices( G::GrpMat, p::RngIntElt: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> [], BoolElt
{"} // "
  // Delegate all checks. I am tired of all this.
  return Sublattices(G, [p] : Limit:= Limit, Levels:= Levels, Projections:= Projections);
end intrinsic;

intrinsic Sublattices( G::GrpMat: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> [], BoolElt
{"} // "
  return Sublattices(G, PrimeDivisors(#G): Limit := Limit, Levels := Levels, Projections:= Projections);
end intrinsic;


// Lattice versions

// Make sure L and its sublattices have the same "NaturalGroup".
// Make sure the sublattices of L are actually sitting below L !!!
intrinsic Sublattices( L::Lat, Q::Setq: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> [], BoolElt
{"} // "
  require IsGLattice(L): "Argument 1 must be a G-lattice";
  require UniverseZ(Q) and forall{p: p in Q | p ge 1 and IsPrime(p)}:
      "Argument 2 must contain positive primes";
  if Type(Limit) ne Infty then requirege Limit, 1; end if;
  if Type(Levels) ne Infty then requirege Levels, 0; end if;
  B:= BasisMatrix(L);
  ok, Projections:= proj_ok(Projections, Degree(L) : B:= B);
  require ok: "The projections are not valid.";
 
  // First get sublattices with respect to the basis B. Then transform.
  G:= Group(L);
  Q:= Setseq(Set(Q));
  Gen:= IsTrivial(G) select [G ! 1] else GeneratorsSequence(G);
  S, complete:= sublattices(Gen, Q, Limit, Levels : needint:= false, proj:= Projections);
  G:= NaturalGroup(L);
  F:= InnerProductMatrix(L);
  return [ LatticeWithBasis(G, s*B, F: CheckIndependent:= false) : s in S ], complete;
end intrinsic;

intrinsic Sublattices( L::Lat, p::RngIntElt: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> [], BoolElt
{"} // "
    return Sublattices(L, [p]: Limit := Limit, Levels := Levels, Projections:= Projections);
end intrinsic;

intrinsic Sublattices( L::Lat: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> [], BoolElt
{"} // "
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return Sublattices(L, PrimeDivisors(#NaturalGroup(L)): Limit := Limit, Levels := Levels, Projections:= Projections);
end intrinsic;


// Matrix versions
intrinsic Sublattices( G::[Mtrx], Q::Setq: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> [], BoolElt
{"} // "
  require BRUZ(G): "Base ring of argument 1 must be Z";
  require UniverseZ(Q) and forall{p: p in Q | p ge 1 and IsPrime(p)}:
      "Argument 2 must contain positive primes";
  if Type(Limit) ne Infty then requirege Limit, 1; end if;
  if Type(Levels) ne Infty then requirege Levels, 0; end if;
  ok, Projections:= proj_ok(Projections, Ncols(G[1]));
  require ok: "The projections are not valid.";

  Q:= Setseq(Set(Q));
  S, complete:= sublattices(G, Q, Limit, Levels : needint:= false, proj:= Projections);
  return [LatticeWithBasis(s: CheckIndependent:= false) : s in S], complete;
end intrinsic;

intrinsic Sublattices( G::[Mtrx], p::RngIntElt: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> [], BoolElt
{"} // "
  return Sublattices(G, [p] : Limit:= Limit, Levels:= Levels, Projections:= Projections);
end intrinsic;


// SublatticeLattice

intrinsic SublatticeLattice( G::[Mtrx], Q::Setq: Limit := Infinity(), Levels := Infinity(), Projections:= [] ) -> LatLat, BoolElt
{ The G-invariant sublattices of the standard lattice L=Z^n which are not
  contained in p*L for any p in Q and whose index in L is a product of elements of Q.
  G must be a subgroup of GL(n,Z) or generators of some Z-order in M(n,Z).
  The second return value indicates whether the enumeration is complete or not.
}

  require BRUZ(G): "Base ring of argument 1 must be Z";
  require UniverseZ(Q) and forall{p: p in Q | p ge 1 and IsPrime(p)} :
      "Argument 2 must contain positive primes";
  if Type(Limit) ne Infty then requirege Limit, 1; end if;
  if Type(Levels) ne Infty then requirege Levels, 0; end if;
  ok, Projections:= proj_ok(Projections, Ncols(G[1]));
  require ok: "The projections are not valid.";

  Q:= Setseq(Set(Q));
  S, P, C, consts, idx, complete:= sublattices(G, Q, Limit, Levels: proj:= Projections);

  SL:= New(LatLat);
  SL`Primes:= Q;
  SL`Complete:= complete;
  SL`Constituents:= consts;
  SL`Index:= idx;
  SL`Lattices:= S;
  SL`Parents:= P;
  SL`Children:= C;

  return SL, complete;
end intrinsic;

intrinsic SublatticeLattice( G::[Mtrx], p::RngIntElt: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> LatLat, BoolElt
{"} // "
  return SublatticeLattice(G, [p]: Limit:= Limit, Levels:= Levels, Projections:= Projections);
end intrinsic;

intrinsic SublatticeLattice( G::GrpMat, Q::Setq: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> LatLat, BoolElt
{"} // "
  Gen:= IsTrivial(G) select [G ! 1] else GeneratorsSequence(G);
  SL, complete:= SublatticeLattice(Gen, Q: Limit:= Limit, Levels:= Levels, Projections:= Projections);
  SL`G:= G;
  return SL, complete;
end intrinsic;

intrinsic SublatticeLattice( G::GrpMat, p::RngIntElt: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> LatLat, BoolElt
{"} // "
  return SublatticeLattice(G, [p] : Limit:= Limit, Levels:= Levels, Projections:= Projections);
end intrinsic;

intrinsic SublatticeLattice( G::GrpMat: Limit := Infinity(), Levels := Infinity(), Projections:= []) -> LatLat, BoolElt
{"} // "
  return SublatticeLattice(G, PrimeDivisors(#G) : Limit:= Limit, Levels:= Levels, Projections:= Projections);
end intrinsic;

// This function assumes that E is a field!!!
function identify_field(E)
  d:= Dimension(E);
  if d eq 1 then return hom< Rationals() -> E | >; end if;
  B:= Basis(E);
  P:= PolynomialRing(Rationals());
  repeat
    x:= &+[Random([-10..10]) * b : b in B];
    m:= P ! MinimalPolynomial(x);
    if m mod P.1 eq 0 then
      m div:= P.1;
    end if;
  until Degree(m) eq d;
  K:= NumberField(m);
  return hom< K -> E | x >;
end function;

intrinsic SublatticeClasses( G::GrpMat : MaximalOrders:= false ) -> SeqEnum
{Returns the isomorphism classes of ZG-lattices. Currently it assumes that End(G) is a field!} 
  require Type(BaseRing(G)) eq RngInt and IsFinite(G) : "G must be a finite integral matrix group.";
  GM:= GModule(ChangeRing(G, Rationals()));
  E:= EndomorphismRing(GM);
  if Dimension(E) eq 1 then S:= Sublattices(G); return S; end if;

  require #CentralIdempotents(E) eq 1: "The group must be irreducible.";
  require IsCommutative(E) : "Currently only fields are supported.";
  delete GM;
  
  Mn:= MatrixRing(ZZ, Degree(G));
  h:= identify_field(E);
  K:= Domain(h);
  R:= MaximalOrder(K);
  B:= Basis(R) @ h;
  d:= LCM({ Denominator(b) : b in B });
  if Abs(d) ne 1 then
    B:= VerticalJoin( [ Matrix(ZZ, d*b) : b in B ] );
    B:= BasisMatrix(Image(B));
    S:= SublatticeClasses(change_basis(G, B));
    return [ LatticeWithBasis(G, BasisMatrix(s) * B) : s in S ];
  end if;
  B:= ChangeUniverse(B, Mn);

  P:= PrimeDivisors( #G );
  DP:= [ Decomposition(R,p) : p in P ];

  // Step 1a) Find all RG-invariant lattices modulo ideals of R
  Ideals:= [];
  for D in DP do
    Ps:= [];
    if #D ne 1 or D[1,2] ne 1 then
      for d in D do
        Append(~Ps, Generators(d[1]^-1) @ h);
      end for;
    end if;
    Append(~Ideals, Ps);
  end for;
  if forall{Ps: Ps in Ideals | IsEmpty(Ps)} then Ideals:= []; end if;
  S:= sublattices([ Mn | G.i : i in [1..Ngens(G)] ] cat B,  P, Infinity(), Infinity() : ideals:= Ideals);
  S:= Setseq(S);

  // Step 1b) Add ideals of R back into S.
  // We try to use ideals over #G first. Since this is what users would expect.
  Cl, Clh:= ClassGroup(R);
  Q, hh:= quo< Cl | >;
  nr:= #S * #Cl;
  used:= [];
  if #Q ne 1 then
    for D in [ D : D in DP | #D ne 1 or D[1,2] ne 1 ] do
      for I in D do
        g:= I[1] @@ Clh;
        o:= Order(g @ hh);
        if o eq 1 then continue; end if;
        Range:= [1..#S];
        for j in [1..o-1] do
          BI:= [ Mn | b @ h : b in Generators(I[1]^j) ];
          for i in Range do
            Append(~S, BasisMatrix(Image(VerticalJoin([ S[i] * b : b in BI ]))));
          end for;
        end for;
        Append(~used, g);
        Q, hh:= quo< Cl | used >;
        if #Q eq 1 then break; end if;
      end for;
    end for;
  end if;

  // This case is rare. The class group is not generated by prime ideals over #G.
  Range:= [1..#S];
  for g in Q do
    if g eq (Q ! 0) then continue; end if;
    I:= g @@ hh @ Clh;
    BI:= [ Mn | b @ h : b in Basis(I) ];
    for i in Range do
      Append(~S, BasisMatrix(Image(VerticalJoin([ S[i] * b : b in BI ]))));
    end for;
  end for;

  assert nr eq #S;
  if MaximalOrders then return [ LatticeWithBasis(G, s) : s in S ]; end if;

  // Step 2) Add lattices which are only fixed by some suborder of R
  U, Uh:= UnitGroup(R);
  Units:= [ u @ Uh @h : u in Generators(U) ];
  List:= [];
  for s in S do
    sQ:= Matrix(QQ, s); sQI:= sQ^-1;
    H:= change_basis(G, sQ);
    B2:= [ Mn | sQ * b * sQI : b in B ];
    Units2:= [ Mn | sQ * u * sQI : u in Units ];
    // This is very inefficient since we recompute the constituents a lot of times.
    // Better: Constituents as an additional argument (but that function already supports so many...)
    S2:= sublattices(GeneratorsSequence(H), P, Infinity(), Infinity() : order:= B2, action:= Units2);
    List cat:= [ LatticeWithBasis(G, IntegralMatrix(s2 * sQ)) : s2 in S2 ];
  end for;
  return List;
end intrinsic;
