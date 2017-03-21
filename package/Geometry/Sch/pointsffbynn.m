freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Listing points on schemes by fibrations
// January 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// We list points on a scheme X defined over a finite field by computing a 
// Noether normalization, which gives a (rational) map X -> H where H is
// a hypersurface; we list points by listing points in each fiber.
//
// This method follows a suggestion of Stamminger.
//
//-------------
//
// Some changes by mch - 06/06 - small change to handle X=hypersurface
// and addition of option to not use H but the actual "Noether hyperplane"
//
//-------------

// produces a map on points (as sequences) from a linear map on
// polynomials
function h_to_map(h)
    R := Generic(Domain(h));
    n := Rank(R);
    seq := [h(R.i): i in [1..n]];

    // common special cases
    if &and[seq[i] eq R.i : i in [1..n]] then
	return func<x | x>; // identity
    end if;
    if &and[#Terms(s) eq 1 : s in seq] then
    // permutation map
	p_seq := [Index(vars,s) : s in seq] where vars is [R.i:i in [1..n]];
	return func<x | [e[p] : p in p_seq] where e is Eltseq(x)>;
    end if;

    vecs := [[MonomialCoefficient(s,R.i): i in [1..n]] : s in seq];
    ze := BaseRing(R)!0;
    return func< x | [ &+[u*e[i] : i in [1..n] | u ne ze where u is v[i]]
		where v is vecs[j] : j in [1..n] ] where e is Eltseq(x) >;
end function;

// Branch of the below intrinsic which doesn't use the hypersurface.
// Code is a simplified copy - see code comments in main intrinsic
function withoutHypersurface(X,GJ,d,hmap : Max:=Infinity())
  n := Rank(Generic(Ideal(X)));
  m := n-d;
  k := BaseRing(X);

  Rlift := PolynomialRing(k, m);
  RliftA := AffineSpace(Rlift);
  Rliftvars := [Rlift.i : i in [1..m]];
  allPts := {@ @};

  if IsOrdinaryProjective(X) then 
    for j := 1 to n-m do
      t0 := [0 : i in [1..j-1]] cat [1];
      for s in CartesianPower(k,n-m-j) do
        t0s0 := t0 cat [s[i] : i in [1..n-m-j]];
        GJP := [ Evaluate(f, Rliftvars cat t0s0) : f in GJ];
        Cliftpts := Points(Cluster(RliftA, GJP));
        for Plift in Cliftpts do
          Include(~allPts,X ! hmap(Eltseq(Plift) cat t0s0));
          if #allPts ge Max then break j; end if;
        end for;
      end for;
    end for;
    
    // Last case: All c_j = 0, but not also a_j = b = 0.
    t0 := [0 : i in [1..n-m]];
    GJP := [ Evaluate(f, Rliftvars cat t0) : f in GJ];
    Cliftpts := Points(Cluster(RliftA, GJP));
    for Plift in Cliftpts do
      Q := Eltseq(Plift) cat t0;
      if Q ne [0 : i in [1..n]] then
        Include(~allPts,X ! hmap(Q));
        if #allPts ge Max then break; end if;
      end if;
    end for;

  else //IsAffine(X)
    for s in CartesianPower(k,n-m) do
      s0 := [s[i] : i in [1..n-m]];
      GJP := [ Evaluate(f, Rliftvars cat s0) : f in GJ];
      Cliftpts := Points(Cluster(RliftA, GJP));
      for Plift in Cliftpts do
        Include(~allPts,X ! hmap(Eltseq(Plift) cat s0));
        if #allPts ge Max then break s; end if;
      end for;
    end for;
  end if;

  return allPts;

end function;

// Max option added Feb 2010, SRD 
// TO DO: Max is ignored by some cases

intrinsic RationalPointsByFibration(X::Sch[FldFin] : Max := Infinity(), 
                                                     UseHypersurface := false) 
       -> SeqEnum
  {An indexed set of the rational points of X over its base field, which
   must be a finite field.}

  k := BaseField(X);
  require Type(k) eq FldFin : 
    "X must be defined over a finite field";

  require IsAffine(X) or IsOrdinaryProjective(X):
    "X must lie in affine or ordinary projective space.";

  I := Ideal(X);
  R := Generic(I);
  n := Rank(R);

  // Start by computing a Noether normalization.
  // Now h(X) has coordinate ring R/h(I), and the variables
  // x_(m+1), ..., x_n are a Noether normalization.  Therefore
  // the projection to the hypersurface H in the variables
  // x_m, ..., x_n is quasi-finite.
  noeth, h := NoetherNormalization(I);
  hmap := h_to_map(h);
  noeth := [h(x) : x in noeth];
  hI := [h(f) : f in Generators(I)];
  d := #noeth;
  m := n-d; // Codimension

  //special cases
  if m eq 0 then //I=0, X = whole space
    return Ratpoints(X); //does it quickly in this case!
  elif m eq n then //Dim(X) eq 0
    return Points(X); // works fine for clusters
  end if;

  if (m gt 1) and (UseHypersurface eq false) then
    GJ := DefiningEquations(X);
    if #GJ ge #hI then
	GJ := hI;
    else
	GJ := [h(f) : f in GJ];
    end if;
    return withoutHypersurface(X,GJ,d,hmap : Max:=Max);
  end if;

  // Compute the projection if X not already a hypersurface
  if m gt 1 then
    bHyp := false;
    Relim := PolynomialRing(k, n, "elim", [1..m-1], [m..n]);
    Relimvars := [Relim.i : i in [1..n]];
    J := [ Evaluate(f, Relimvars)  : f in hI ];
    GJ := GroebnerBasis(J);
    // The last element of the elimination ideal is the hypersurface H
    H := GJ[#GJ];
  else // X = H a hypersurface
    H := h(GroebnerBasis(I)[1]);
    bHyp := true;
  end if; 
  Rhyp := AffineSpace(k, 1);

  // Create a new affine space in which the fibers of the map
  // X -> H will be contained
  if m gt 1 then
    Rlift := PolynomialRing(k, m-1);
    RliftA := AffineSpace(Rlift);
    Rliftvars := [Rlift.i : i in [1..m-1]];
  end if;
  allPts := {@ @};

  if IsProjective(X) then 
    // One possibility would be to reduce to the affine case by cutting
    // by a hypersurface and then calling the function recursively--
    // this could prove to be very expensive, though, unless care is taken
    // not to recompute a Grobner basis, for example.
    // We find it more efficient in practice to hard code this recursion.
 
    // A point on X is of the form (a_1:...:a_{m-1} : b : c_1:...:c_{n-m} )
    // where the coordinates (b : c_i) are a point on H in the fibration
    // X -> H, with H a hypersurface.  
    // Thus we run over all possibilities for the c_i (projectively), leaving
    // a_i and b undetermined, but giving a zero-dimensional scheme.  
    // We take j to be the index of c_j, the first coordinate which is nonzero.
    for j := 1 to n-m do
      t0 := [0 : i in [1..j-1]] cat [1];

      // H is still considered a polynomial in all the many variables, so
      // we have to "evaluate" it with zeros for the a_i
      t := [0 : i in [1..m-1]] cat [Rhyp.1] cat t0;
      for s in CartesianPower(k,n-m-j) do
        s0 := [s[i] : i in [1..n-m-j]];
        Hhyp := Evaluate(H,t cat s0);
        // Hhyp is now a polynomial in one variable, so we can easily find the
        // points on it!
        Chyppts := Points(Cluster(Rhyp,Hhyp));
        // For each point (b : c_i) on H, list the lifts to X.
        t0s0 := t0 cat s0;
	if bHyp then // m=1, X = H 
	  allPts join:= {@ X!hmap(Eltseq(P) cat t0s0) : P in Chyppts @}; 
          if #allPts ge Max then break j; end if;
	else
          for P in Chyppts do
            // Eltseq(P) is the value of b
            GJP := [ Evaluate(f, Rliftvars cat Eltseq(P) cat t0s0) : f in GJ];
            Cliftpts := Points(Cluster(RliftA, GJP));
            for Plift in Cliftpts do
              Include(~allPts, X!hmap(Eltseq(Plift) cat Eltseq(P) cat t0s0));
              if #allPts ge Max then break j; end if;
            end for;
          end for;
	end if;
      end for;
    end for;
    
    // Last case: All c_j = 0, but not also a_j = b = 0.
   if bHyp then // m=1, X = H
    t := [k!1] cat [0 : i in [1..n-m]];
    if Evaluate(H,t) eq 0 then
      Include(~allPts,X!hmap(t));
    end if;
   else
    t0 := [0 : i in [1..n-m]];
    t := [0 : i in [1..m-1]] cat [Rhyp.1] cat t0;
    Hhyp := Evaluate(H,t);
    Chyppts := Points(Cluster(Rhyp,Hhyp));
    for P in Chyppts do
      GJP := [ Evaluate(f, Rliftvars cat Eltseq(P) cat t0) : f in GJ];
      Cliftpts := Points(Cluster(RliftA, GJP));
      for Plift in Cliftpts do
        Q := Eltseq(Plift) cat Eltseq(P) cat t0;
        if Q ne [0 : i in [1..n]] then
          Include(~allPts, X!hmap(Q));
          if #allPts ge Max then break P; end if;
        end if;
      end for;
    end for;
   end if;

  else //IsAffine(X)
    // Easier than the projective case:
    // A point on X is of the form (a_1,...,a_{m-1}, b, c_1,...,c_{n-m} )
    // and now we may just cycle through all possibilities for the c_i
    t := [0 : i in [1..m-1]] cat [Rhyp.1];
    for s in CartesianPower(k,n-m) do
      s0 := [s[i] : i in [1..n-m]];
      Hhyp := Evaluate(H,t cat s0);
      Chyppts := Points(Cluster(Rhyp,Hhyp));
      for P in Chyppts do
	if bHyp then // m=1, X = H 
	  allPts join:= {@ X!hmap(Eltseq(P) cat s0) : P in Chyppts @}; 
          if #allPts ge Max then break s; end if;
	else
          GJP := [ Evaluate(f, Rliftvars cat Eltseq(P) cat s0) : f in GJ];
          Cliftpts := Points(Cluster(RliftA, GJP));
          for Plift in Cliftpts do
            Include(~allPts, X!hmap(Eltseq(Plift) cat Eltseq(P) cat s0));
            if #allPts ge Max then break s; end if;
          end for;
	end if;
      end for;
    end for;
  end if;

  return allPts;
end intrinsic;


intrinsic Random(S::SetPt) -> Pt
{A random point in S, where S is a pointset X(k) for a scheme X and a finite field k}

  X := Scheme(S);  k := Ring(S);
  require IsFinite(BaseRing(X)) and IsFinite(k): 
         "The argument must be a pointset X(k) where X is a scheme "*
         "defined over a finite field and where k is a finite field";
  require IsAffine(X) or IsProjective(X): "The scheme must be affine or projective";
  
  if IsCluster(X) then 
    return Random(Points(X,k)); 
  // TO DO:
  //elif k is small then ... 
  //elif X has codimenion 1 then ...
  end if;

  R := ChangeRing(Generic(Ideal(X)),k);
  I := ideal<R| [R!pol : pol in Basis(Ideal(X))] >;
  A := IsAffine(X) select AffineSpace(R) else ProjectiveSpace(R);
  NN := NoetherNormalisation(Ideal(X)); // this is stored on the ideal
  ChangeUniverse(~NN,R);

  count := 0;
  cutoff := 5*#k^dim where dim := (IsAffine(X) select #NN else #NN-1);
  while count lt cutoff do 
    count +:= 1;
    if IsAffine(X) then
      eqns := [R| f - Random(k) : f in NN];
    elif IsProjective(X) then 
      assert #NN gt 1;
      i0 := Random([1..#NN]);  
      eqns := [R| NN[i] - Random(k)*NN[i0] : i in [1..#NN] | i ne i0];
    end if;
    C := Scheme(A, Basis(I) cat eqns);  bool,C := IsCluster(C);
    error if not bool, "The NoetherNormalisation map seems to have some infinite fibres";
    pts := Points(C,k);
    if not IsEmpty(pts) then 
      return S! Eltseq(Random(pts));
    end if;
  end while;

  // Looks like there are no rational points in S
  pts := Points(X,k);
  error if IsEmpty(pts), "The given pointset is empty";
  return Random(pts);
end intrinsic;
