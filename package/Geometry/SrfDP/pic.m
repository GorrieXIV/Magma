freeze;

/***********************************************************************
 *  Lines and Picard lattice (with Galois action) for general schemes
 *  
 *  Much of this is based on Stephan Elsenhans' code for cubic surfaces
 *  
 *  Steve Donnelly, March 2011
 ***********************************************************************/

declare attributes Sch : scheme_of_lines, lines_over_internal_field;

debug := true;

/* 
  The stuff here for lines in projective schemes duplicates the routine
  FindLines in Beck's package.  (The implementation there is not great:
  it covers the whole Grassmannian in one piece, but this means using
  extra variables which then have to be eliminated, and overall it's
  awkward to use.)

  Lines in ordinary projective space P^n are expressed as follows: 
  (1) Lines of the form
        [1 : s : l_2(s) : ... : l_n(s)] 
      where l_i(s) = ai + s*bi
  (2) Lines not intersecting the first affine patch of P^n
  (3) Lines in the first affine patch of P^n that are "vertical" 
      in the first j affine coords, ie lines of the form
        [1 : c_1 : ... : c_{j-1} : s : l_{j+1}(s) : ... : l_n(s)]
      for 2 <= j <= n
  Note: case (1) is actually case (3) with j = 1.
*/

// The points s=0 and s=1 on a line parametrized by s

function two_points(l)
   return [[Evaluate(f,s) : f in l] : s in [0,1]];
end function;


// Convert a parametrized line l into an actual line in P^n

function line_as_scheme(Pn, l)
   B := Basis(Kernel(Transpose(Matrix(two_points(l)))));
   return Scheme(Pn, [&+[b[i]*Pn.i : i in [1..#l]] : b in B]);
end function;


// Determine whether parametrized lines l1 and l2 in P^n intersect
// Return 2 if they coincide, 1 if they intersect, 0 otherwise

function intersection_number(l1, l2)
   span := Matrix(two_points(l1) cat two_points(l2));
   R := BaseRing(span);
   if not IsField(R) then
      span := ChangeRing(span, FieldOfFractions(R));
   end if;
   r := Rank(span);
   error if r notin {2,3,4},
        "intersection of lines should have dimension 1, 0 or -1";
   return 4 - r;
end function;


// This does not calculate the self-intersections!

function intersection_matrix(lines)
   l := #lines;
   IP := MatrixRing(Integers(), l) ! 0;
   for i in [1..l], j in [i+1..l] do 
      m := intersection_number(lines[i], lines[j]);
      assert m eq 0 or m eq 1;
      IP[i,j] := m;
      IP[j,i] := m;
   end for;
   return IP;
end function;


// Here lgen is a sequence of elements of Pgen = R[t]
// where R is the coordinate ring of an affine space,
// and coords is a point in that affine space.

function specialize_line(lgen, coords)

   K := Ring(Parent(coords));
   P := PolynomialRing(K);
   Pgen := Universe(lgen);
   assert Type(Pgen) eq RngUPol;
   seq := Eltseq(coords);
   if #seq eq 0 then 
      l := lgen;
   else
      R := BaseRing(Pgen);
      assert Type(R) eq RngMPol and Rank(R) eq #seq;
      l := [P| [Evaluate(c,seq) : c in Eltseq(f)] : f in lgen];
   end if;

   return l;
end function;


intrinsic UnionOfLines(P::Prj, L::Setq[RngUPol]) -> Sch
{A scheme in the projective space P which is the (scheme-theoretic) union 
of the lines in L.  The lines should be given in parametrized form, 
each line as a sequence of linear polynomials (the coefficients may be in
an extension of the base field of P).  The lines are assumed to be distinct}

   Pol := Universe(L);
   s := Pol.1;

   // The union of d geometric lines is cut out by the forms of degree d
   // that vanish on them 
   // (for instance, products of linear forms with one vanishing on each line)
   d := #L;
   LS := LinearSystem(P, d);

   return "Not finished";

end intrinsic;


intrinsic LinesInScheme(X::Sch : Number:=Infinity()) -> SeqEnum, List

{Computes the geometric lines contained in the scheme X.  
Returns a list of schemes whose points correspond to lines, 
together with a corresponding list of parametrized lines
(one line for each scheme, expressed generically using the coordinates of that scheme).
There may be infinitely many lines.}

   if assigned X`scheme_of_lines then
      return Explode(X`scheme_of_lines);
   end if;

   if ISA(Type(X), SrfDelPezzo) then
      if Number cmpeq Infinity() then
         Number := NumberOfLines(X);
      else
         require Number eq NumberOfLines(X) : "Incorrect value of optional argument 'Number'";
      end if;
   end if;

   F := BaseField(X);
   assert IsOrdinaryProjective(X);
   n := Dimension(AmbientSpace(X));

   if Dimension(X) le 0 then
      return [PowerStructure(Sch)| ], [* *];
   elif n eq 1 then // X = P^1
      AL<[x]> := AffineSpace(F, 1);
      ALP := PolynomialRing(CoordinateRing(AL)); s := ALP.1;
      Ls := [Scheme(AL, AL.1)];
      ls := [* [1,s] *];
      X`scheme_of_lines := [* Ls, ls *];
      return Ls, ls;
   end if;

   d := Degree(X);

   count := Number lt Infinity();
   num_found := 0;

   // A line lies in X iff it has > d distinct geometric points in common with X
   // Choose d+1 test values in F 
   vals := {F| v : v in [0..d]};
   if #vals lt d+1 then 
      // TO DO: in small characteristic, use values in extensions
      error "Not yet handled (characteristic is too small)";
   end if;

   // See comment above regarding how the lines are expressed
   Ls := [];
   ls := [* *];

   // Cases (1) and (3)
   for j := 1 to n do 
      if num_found ge Number then 
         break;
      end if;
      AL<[x]> := AffineSpace(F, 2*n-j-1);
      ALP := PolynomialRing(CoordinateRing(AL)); s := ALP.1;
      lgen := [ALP|1] cat [ALP|x[i] : i in [1..j-1]] cat [ALP|s] 
              cat [ALP|x[2*i-j-2] + s*x[2*i-j-1] : i in [j+1..n]];
      tests := [[Evaluate(li,v) : li in lgen] : v in vals];
      L := Scheme(AL, [Evaluate(f,l) : f in Basis(Ideal(X)), l in tests]);
      if Dimension(L) ge 0 then
         Append(~Ls, L);
         Append(~ls, lgen);
         if count then
            assert Dimension(L) eq 0;
            num_found +:= Degree(L);
         end if;
      end if;
   end for;

   // Case (2), hyperplane at infinity
   if num_found lt Number then
      P_inf := ProjectiveSpace(F, n-1);
      subst := [0] cat [P_inf.i : i in [1..n]];
      X_inf := Scheme(P_inf, [Evaluate(f, subst) : f in Basis(Ideal(X))]);
      Ls_inf, ls_inf := LinesInScheme(X_inf);
      Ls cat:= Ls_inf;
      ls cat:= [* [0] cat l : l in ls_inf *];
      if count then
         for L in Ls_inf do 
            assert Dimension(L) eq 0;
            num_found +:= Degree(L);
         end for;
      end if;
   end if;

   error if count and Number ne num_found, "Wrong number of lines found!";  

   X`scheme_of_lines := [* Ls, ls *];
   return Ls, ls;
end intrinsic;


function orbits_of_lines(X : num:=Infinity())
  
   F := BaseField(X);
   Ls, ls := LinesInScheme(X : Number:=num);

   error if not forall{L: L in Ls | Dimension(L) eq 0},
        "X contains infinitely many lines";

   rep_pts := [* *];
   rep_lines := [* *];

   for i := 1 to #Ls do 
      L := Ls[i];
      for pt in RepresentativePoints(L : Simple) do 
         Append(~rep_pts, pt);
         Append(~rep_lines, specialize_line(ls[i], pt));
      end for;
   end for;

   return rep_pts, rep_lines;
end function;


// Find a field where all the geometric lines are defined.
// This will be used for the GaloisGroup of each field,
// and for other internal calculations with the lines.

function lines_over_internal_field(X : num:=Infinity())

   if assigned X`lines_over_internal_field then 
      return Explode(X`lines_over_internal_field);
   end if;

   F := BaseField(X);
   type := Type(F); // TO DO: type check
   use_galois_data := type in {FldRat, FldFunRat, FldFun} or ISA(type, FldAlg);

   pts, lines := orbits_of_lines(X : num:=num);
   fields := [* Ring(Parent(pt)) : pt in pts *];
   assert forall{K : K in fields | K eq F or BaseField(K) eq F};
   degrees := [Integers()| Degree(K,F) : K in fields];

   if num cmpeq Infinity() then
      num := &+ degrees; 
   else
      assert num eq &+ degrees; 
   end if;
 
   if Seqset(degrees) eq {1} then
      // All the lines are rational over F, just use F as the internal field
      RR := F;
      orbits := [[i] : i in [1..num]];
      homs := [* *]; // coercion is used instead
      GD := 0;

   elif not use_galois_data then
      // General case + FldFin case: use the splitting field of all the polys
      // TO DO: for certain types, use a residue field as the internal field
      RR := F;
      roots := [F| ];
      for K in fields do
         if K cmpeq F then
            Append(~roots, 0);
            continue;
         end if;
         f := DefiningPolynomial(K);
         assert Degree(f) eq Degree(K,F);
         while true do
            ff := Factorization(PolynomialRing(RR)!f);
            if exists(g){t[1] : t in ff | Degree(t[1]) ne 1} then
               RR := ext<RR|g>;
            else
               break;
            end if;
         end while;
         ChangeUniverse(~roots, RR);
         roots cat:= [RR| Roots(t[1])[1][1] : t in ff];
      end for;
      // create homs K -> RR defined by the roots
      homs := [* *];
      for i := 1 to #roots do
         k := Min([k: k in [1..#fields] | &+degrees[1..k] ge i]);
         K := fields[k];
         if K cmpeq F then
            h := Coercion(K, RR);
         else  
            assert roots[i] ne 0;
            h := hom< K -> RR | roots[i] >;
         end if;
         Append(~homs, h);
      end for;
      orbits := []; // not used
      GD := 0;

   else
      // create extension using the distinct defining polys
      pols := {PolynomialRing(F)| DefiningPolynomial(K) : K in fields | K cmpne F};

      // Sigh... should be able to use ext, but it only has the Check option over Q
      // TO DO...
      if ISA(Type(F), FldFunG) then
         KK := FunctionField(&* pols : Check:=false);
      else
         KK := ext< F | &* pols : Check:=false >;
      end if;

      if Type(F) eq FldRat then
         GD := GaloisData(KK : Subfields:=false);
      else
         GD := GaloisData(KK);
      end if;

      assert assigned GD`KnownSubgroup; // TO DO: GaloisData should handle this?

      type_Qt := ISA(Type(F), FldFunG) and Characteristic(F) eq 0; // TO DO: fix

      RR := GD`Ring;
      RR := FieldOfFractions(RR); // because the lines can involve denominators
      if not assigned GD`BaseMap then
         FtoRR := Coercion(F, RR);
      else   
         FtoRRprec := type_Qt select <3,3> else 10;
         FtoRR := map< F -> RR | x :-> RR! GD`BaseMap(x, FtoRRprec) >;
      end if;

      homs := [* *]; // K --> RR
      orbits := [];

      for K in fields do 
         if K cmpeq F then
            Append(~orbits, [0]);
            Append(~homs, FtoRR);
         else
            f := DefiningPolynomial(K);
            cRR := [FtoRR(c) : c in Coefficients(f)];
            fRR := Polynomial(cRR);
            vals := [Evaluate(fRR,r) : r in GD`Roots];
            inds := type_Qt select [i : i in [1..#vals] | forall{c : c in Coefficients(vals[i]) | Valuation(c) ge 1}]
                             else  [i : i in [1..#vals] | Valuation(vals[i]) ge 1];
            assert #inds eq Degree(f);
            Append(~orbits, inds);
            for i in inds do
               Append(~homs, hom< K -> RR | FtoRR, GD`Roots[i] >); 
            end for;
         end if;
      end for;

   end if;

   // Get lines over RR corresponding to the roots
   PRR := PolynomialRing(RR);
   linesRR := [];
   for i := 1 to num do
      k := Min([k: k in [1..#fields] | &+degrees[1..k] ge i]);
      K := fields[k];
      l := lines[k];
      h := #homs gt 0 select homs[i] else Coercion(K, RR);
      Append(~linesRR, [PRR| [c@h : c in Eltseq(f)] : f in l]);
   end for;

   X`lines_over_internal_field := [* linesRR, homs, orbits, GD *];
   return linesRR, homs, orbits, GD;
end function;


// TO DO: more general (surface?)

intrinsic IntersectionMatrix(X::SrfDelPezzo) -> Mtrx
{A matrix giving the intersection numbers of the (geometric) lines 
on the del Pezzo surface X}

   lines := lines_over_internal_field(X);
   I := intersection_matrix(lines);
   for i := 1 to #lines do 
      I[i,i] := -1;
   end for;

   return I;
end intrinsic;


intrinsic NumberOfLines(X::SrfDelPezzo) -> RngIntElt
{The number of geometric lines in (the standard pluri-canonical embedding of)
the Del Pezzo surface X}

   case Degree(X):
      when 1: return 240;
      when 2: return 56;
      when 3: return 27;
      when 4: return 16;
      when 5: return 10;
      when 6: return 6;
      when 7: return 3;
      when 8: return 1;
      when 9: return 0;
   end case;
end intrinsic;


// GaloisGroup of the GaloisData GD, where
// G is known to contain the Galois group

function galois_group(GD, G)

   prec := 10; // TO DO (?)

   norbits := #Orbits(G);
   if debug then
      assert norbits eq #Factorization(GD`f);
   end if;

   while true do
      if #G eq 1 or assigned GD`KnownSubgroup and GD`KnownSubgroup eq G then
         break;
      end if;
      descended := false;
      for Hrec in MaximalSubgroups(G) do
         H := Hrec`subgroup;
         if #Orbits(H) eq norbits then
            b, c := Stauduhar(G, H, GD, prec : 
                    PreCompInvar := RelativeInvariant(G, H : IsMaximal:=true));
            error if b lt 0, "Stauduhar could not decide";
            if b eq 1 then
               G := H^c[1];
               assert assigned GD`KnownSubgroup and GD`KnownSubgroup subset G;
               descended := true;
               break;
            end if;
         end if;
      end for;
      if not descended then
         break;
      end if;
   end while;

   return G;
end function;


function big_perm(p, orbits)
   p := Eltseq(p);
   bp := [];
   for o in orbits do 
      if o eq [0] then
         bp cat:= [#bp + 1];
      else
         po := [Index(o,p[i]) : i in o];
         bp cat:= [#bp + i : i in po];
      end if;
   end for;
   return bp;
end function;


intrinsic GaloisActionOnLines(X::Sch : Number:=Infinity()) -> GrpPerm
{A permutation group which gives the Galois action on the (finite) set 
of lines in the scheme X}

   lines, homs, orbits, GD := lines_over_internal_field(X : num:=Number);

   // In all cases, #lines should be the number of geometric lines

   if GD cmpeq 0 then
      if #orbits eq #lines then
         // trivial galois action
         G := sub< Sym(#orbits) | >; 
         return G;
      elif Type(BaseField(X)) eq FldFin then
         K := Codomain(homs[1]);
         G := GaloisGroup(K, BaseField(X));
         return G;
      else
         require false: "Not implemented for schemes over fields of type", 
                                                         Type(BaseField(X));
      end if;
   end if;

   // The Galois group must respect intersection numbers
   l := #lines;
   IP := intersection_matrix(lines);
   IPG := Graph< l | { {i,j} : i,j in [1..l] | IP[i,j] gt 0 }>;
   AutIP := AutomorphismGroup(IPG);

   // Convert between the l lines and the internal extension of degree d
   // We return a subgroup of Sym(l) giving the action on the lines, 
   // but we have to compute it inside Sym(d) acting on the roots
   d := Degree(GD`f);
   if d eq l then
      // lines[i] corresponds to GD`Roots[perm[i]]
      perm := Sym(d)! &cat orbits;
      G0 := AutIP^perm meet Stabilizer(Sym(d), [Seqset(o) : o in orbits]);
      Gperm := galois_group(GD, G0);
      G := Gperm ^ (perm^-1);
   else
      // there were repeated fields or degree 1 fields
      orbits1 := [o : o in orbits | o ne [0]];
      Sd := Stabilizer(Sym(d), [Seqset(o) : o in orbits1]);
      Sl := Sym(l);
      h := hom< Sd -> Sl | [big_perm(p,orbits) : p in GeneratorsSequence(Sd)] >;
      G0 := (Image(h) meet AutIP) @@ h;
      G := galois_group(GD, G0);
      G := G @ h;
   end if;

   // Cheap sanity check
   for i := 1 to Ngens(G) do 
      g := PermutationMatrix(Integers(), G.i);
      assert IP eq g*IP*Transpose(g); // Transpose(g) = g^-1
   end for;
 
   return G;
end intrinsic;


// TO DO: allow other types of surfaces

intrinsic PicardGroupGeometric(X::SrfDelPezzo) -> ModRng, Mtrx

{The Picard group of the Del Pezzo surface X (over the 
 algebraic closure of its base field), returned as a Z-module.  
 Also returns a matrix giving the intersection pairing on the 
 geometric Picard group}

   return GeometricPicardGroup(X);
end intrinsic;

intrinsic GeometricPicardGroup(X::SrfDelPezzo) -> ModRng, Mtrx
{"} // "
   if assigned X`GeometricPicardGroup then
      M, I := Explode(X`GeometricPicardGroup);
      return M, I;
   end if;

   Z := Integers();
   d := Degree(X);
   require d ge 3 : "Not implemented for Del Pezzo surfaces of degree 1 or 2"; // TO DO

   I := IntersectionMatrix(X);
   assert BaseRing(I) cmpeq Z;

   V := RModule(Z, Nrows(I));
   K := Kernel(I);
   M, m := quo<V|K>;
   assert #Basis(M) eq 10-d;

   // Choose standard basis of the lattice L_{1,9-d}
   // TO DO: properly
   n := Nrows(I);
   for i1 := 1 to n do 
      inds := [Z| i1];
      for i := 1 to Nrows(I) do 
         if #inds eq 9-d then
            break i1;
         end if;
         if forall{ii: ii in inds | I[i,ii] eq 0} then
            Append(~inds, i);
         end if;
      end for;
   end for;
   error if #inds ne 9-d, "Failed to find a standard basis of the Picard group";
   // Now find vector spanning the complement in M of these 9-d lines
   K := Kernel(I);
   assert #Basis(K) eq Nrows(I) - (10-d);
   K0 := Kernel(ColumnSubmatrix(I, inds)); // obviously contains K
   K1, m := quo<K0|K>;
   assert #Basis(K1) eq 1;
   v0 := V! (K1.1@@m);
   B := [v0] cat [V.i : i in inds];
   if debug then
      assert V eq sub<V|B,K>;
   end if;

   M := RModule(Z, #B);
   T := Matrix(B); // defines a section M --> V
   IB := T * I * Transpose(T);

   X`GeometricPicardGroup := [* M, IB, T, K *];
   return M, IB;
end intrinsic;


intrinsic PicardIntersectionPairing(X::SrfDelPezzo) -> Mtrx
{A matrix giving the intersection pairing on the GeometricPicardGroup of X}

   _, I := GeometricPicardGroup(X);
   return I;
end intrinsic;


intrinsic PicardGaloisModule(X::SrfDelPezzo) -> ModGrp
{A G-module giving the Galois action on the GeometricPicardGroup of X}

   if assigned X`PicardGaloisModule then
      return X`PicardGaloisModule;
   end if;

   Z := Integers();

   _ := GeometricPicardGroup(X);
   _, _, T, K := Explode(X`GeometricPicardGroup);
assert BaseRing(T) cmpeq Z;
assert BaseRing(K) cmpeq Z;

   // Find TT mapping the large space to the Picard group M
   // (T is a section mapping the other way, K is the kernel)
   V := RModule(Z, Ncols(T));
   M, m := quo<V|K>;
   MM := Matrix([v@m : v in Basis(V)]);
   BM := T * MM;
   TT := MM * BM^-1;
assert BaseRing(TT) cmpeq Z;
assert IsIdentity(MatrixRing(Z,Nrows(T))! (T*TT));

   G := GaloisActionOnLines(X);
   action := [T * PermutationMatrix(Z,g) * TT : g in GeneratorsSequence(G)];
   assert forall{U : U in action | BaseRing(U) cmpeq Z};
   GM := GModule(G, action);

   X`PicardGaloisModule := GM;
   return GM;
end intrinsic;


/*
What's next?

Need to access the field (as well as its Galois group)
Need to access the isomorphism of the two Sym's

PicardGroup : Z-module with chosen basis
(Geometric)PicardLattice : the complement of the hyperplane
*/

