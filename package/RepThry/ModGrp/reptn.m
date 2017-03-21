freeze;
 
/* In following functions, G should be a a group, chi a character of
 * G and H a subgroup of G such that the restriction of chi to H has a
 * constituent theta of degree 1 and multiplicity 1.
 */

declare attributes ModGrp : Character;
declare verbose GModule, 1;

IsHGood := function(G,chi,H)
/* tests whether subgroup H has required property w.r.t. chi  -
 * if so it returns true and theta
 */
  local T, chiH, q;
  T := LinearCharacters(H);
  chiH:=Restriction(chi,H);
  chi_order := CyclotomicOrder(CoefficientField(chi));
  q,_ := Decomposition(T,chiH);
  best_i := 0;
  best_order := 0;
  for i  := 1 to #T do
    if  q[i] eq 1 then
      i_order := CyclotomicOrder(CoefficientField(T[i]));
      if chi_order mod i_order eq 0 then
	  return true, T[i];
      end if;
      i_order := EulerPhi(LCM(i_order, chi_order));
      if i_order lt best_order or best_order eq 0 then
	  best_order := i_order;
	  best_i := i;
      end if;
    end if;
  end for;
  if best_i eq 0 then
      return false,_;
  else
      return true, T[best_i];
  end if;
end function;

LookForSmallestH := function(G,chi)
  local S, fl, min,  H, theta;
  S := Subgroups(G);
  min := #G + 1;
  found := false;
  for s in S do
    if s`order lt min then
	fl, temp := IsHGood(G,chi,s`subgroup);
	if fl then
	    H := s`subgroup;
	    theta := temp;
	    min := s`order;
	    found := true;
	end if;
    end if;
  end for;
  if found then
    return H, theta;
  else
    "No subgroup found";
    return false, _;
  end if;
end function;
  
LookForH := function(G,chi)
  local fac, P, trymax, M, MS, H, isgood, theta, newtheta;
  fac := Factorisation(#G);
  // try Sylow subgroups
  for f in fac do
    P := Sylow(G,f[1]);
    isgood, theta := IsHGood(G,chi,P);
    if isgood then
      H := P;
      trymax := true;
      while trymax do
        M := MaximalSubgroups(H);
	if ISA(Type(M[1]), Rec) then
	    M := [m`subgroup:m in M];
	end if;
        for m in M do
          isgood, newtheta := IsHGood(G,chi,m);
          if isgood then
             H:=m;
             theta := newtheta;
             break;
          end if;
          trymax := false;
        end for;
      end while;
      return H, theta;
    end if;
  end for;
  // try all maximals
  MS := MaximalSubgroups(G);
  if ISA(Type(MS[1]), Rec) then
    MS := [m`subgroup:m in MS];
  end if;
  for P in MS do
    isgood, theta := IsHGood(G,chi,P);
    if isgood then
      H := P;
      trymax := true;
      while trymax do
        M := MaximalSubgroups(H);
        if ISA(Type(M[1]), Rec) then
	  M := [m`subgroup:m in M];
	end if;
        for m in M do
          isgood, newtheta := IsHGood(G,chi,m);
          if isgood then
             H:=m;
             theta := newtheta;
             break;
          end if;
          trymax := false;
        end for;
      end while;
      return H, theta;
    end if;
  end for;
  "No subgroup found";
  return false, _;
end function;

Alpha := function (chi,H,theta,K,g)
/* g in G */
  res := K!0;
  for h in H do res +:= theta(h^-1)*chi(h*g); end for;
  return res;
end function;

function ModField(K, np)
    // Return tuple of sequence of homs into finite fields, using (np) primes.
    n := Conductor(K);
    if n eq 1 then
	return [];
    end if;

    k := Ceiling(2^21.5/n);

    H := <>;
    for c := 1 to np do
	repeat
	    k -:= 1;
	    p := k*n + 1;
	until IsPrime(p);

	FF := GF(p);
	PFF := PolynomialRing(FF);
	D := DefiningPolynomial(K);
        if Type(D) eq RngUPolElt then
          D := [D];
        end if;
	roots := [Roots(PFF!f): f in D];

	h := [hom<K -> FF | [r[1]: r in t]>: t in CartesianProduct(roots)];
	Append(~H, h);
    end for;

    return H;
end function;

function MyRank(A, H)
    if #H eq 0 then
	return Rank(A);
    end if;
    n := Ncols(A);
    Ae := Eltseq(A);
    r := 0;
    for hq in H do
	for h in hq do
	    Ah := Matrix(n, [h(x): x in Ae]);
	    r := Max(r, Rank(Ah));
	    if r eq n then
		return r;
	    end if;
	end for;
    end for;
    return r;
end function;

NsElts := function(G,chi,H,theta:SparseCyclo := true)
/* returns Degree(chi) elements  giving nonsingular matrix */
  local A1, deg, elts, K, T, seeking, keep, x;
  
  deg := Integers()!chi[1];
  K := Universe([chi[i] : i in [1..#chi]] cat [theta[i]:i in [1..#theta]]);

  if not SparseCyclo then
    K := CyclotomicField(Conductor(K):Sparse := false);
  end if;

  FF_homs := ModField(K, 2);

  // representation returned will be over K
  A1:=ScalarMatrix(deg,K!0);

  //choose deg random elements of G to start off with.
  elts:=[];
  while #elts lt deg do
    x := Random(G);
    keep := true;
    for y in elts do if x*y^-1 in H then keep:=false; break; end if; end for;
    if keep then Append(~elts,x); end if;
  end while;

  for i := 1 to deg do
    seeking := true;
    while seeking do
      eii := elts[i]^-1;
      for j := 1 to i do
        A1[j][i] := Alpha(chi,H,theta,K,elts[j]*eii);
      end for;
      for j := 1 to i-1 do
        A1[i][j] := Alpha(chi,H,theta,K,elts[i]*elts[j]^-1);
      end for;
      //if Rank(A1) lt i then
      if MyRank(A1, FF_homs) lt i then
        //try replacing i-th element of elts.
        keep:=false;
        while not keep do
          keep := true;
          x := Random(G);
          // x := Random(T);
          for y in elts do
	      if x*y^-1 in H then
		  keep:=false;
		  break;
	      end if;
	  end for;
        end while;
        elts[i] := x;
      else seeking := false;
      end if;
    end while;
  end for;
  return elts, A1, K;
end function;

RepOfChiOnElt := function (G,chi,H,theta,elts,A1,K,g)
/* g in G - elts, A1 as returned by NsElts
 * returns representation of g.
 */
  local A, deg;
  
  deg := Integers()!chi[1];
  A:=ScalarMatrix(deg,K!0);
  gi := g^-1;
  for i := 1 to deg do
    eigi := elts[i]*gi;
    for j := 1 to deg do
	A[i][j] := Alpha(chi,H,theta,K,eigi*elts[j]^-1);
  end for; end for;

  return A1*A^-1;
end function;

intrinsic GModuleConductorOfCoefficientField(
    chi::AlgChtrElt: H:="none",
    Best:=false, BestField:=false,
    FieldDegreeLimit := 0
) -> RngInt
{Return the conductor of the coefficient field that GModule for this character would return (false on failure)}

/* returns a reptn. of G over a cyclotomic field affording character chi
 * User can supply H - if so, IsHGood must return true.
 * Usually the smallest good subgroup H is the best, but sometimes
 * a larger subgroup results in a better field.
 * If Best is true, then the whole subgroup lattice is searched for the
 * best H. This is probably a good idea for small groups.
 */
  local theta,elts,A1,genims, deg,K;

  if Degree(chi) eq 1 then
    return Conductor(CoefficientField(chi));
  end if;

  require Norm(chi) eq 1:"Character must be irreducible";
  
  G := Group(Parent(chi));
  if H cmpeq "none" then
    H:=sub<G|>;
  end if;

  deg := Integers()!chi[1];
  K := Universe([chi[i] : i in [1..#chi]]);

  if #H gt 1 then
     isgood, theta := IsHGood(G,chi,H);
     if not isgood then error "Subgroup supplied is not good."; end if;
  else
     if Best then
       H, theta := LookForSmallestH(G,chi);
     else 
       H, theta := LookForH(G,chi);
     end if;
     if H cmpeq false then
       return false;
     end if;
     if
	 FieldDegreeLimit gt 0 and
	 Degree(Universe([theta[i] : i in [1..#theta]])) gt FieldDegreeLimit
     then
        return false;
     end if;
  end if;

  return LCM(Conductor(CoefficientField(theta)), Conductor(CoefficientField(chi)));
end intrinsic;

/*
intrinsic CoefficientRing(M::ModGrp) -> Rng
{The coefficient ring of the matrices}
  return CoefficientRing(ActionGenerators(M)[1]);
end intrinsic;
*/

intrinsic GModule(
    chi::AlgChtrElt: H:="none",
    Best:=false, BestField:=false,
    FieldDegreeLimit := 0,
    SparseCyclo := false
) -> ModGrp
{Return a GModule affording the character chi (false on failure)}

/* returns a reptn. of G over a cyclotomic field affording character chi
 * User can supply H - if so, IsHGood must return true.
 * Usually the smallest good subgroup H is the best, but sometimes
 * a larger subgroup results in a better field.
 * If Best is true, then the whole subgroup lattice is searched for the
 * best H. This is probably a good idea for small groups.
 */
  local theta,elts,A1,genims, deg,K;

  if Degree(chi) eq 1 then
    R := GModuleLinear(chi);
    R`Character := chi;
    if SparseCyclo then
      return R;
    end if;
    K := CoefficientRing(R);
    K := CyclotomicField(Conductor(K):Sparse := false);
    return ChangeRing(R, K);
  end if;

  require Norm(chi) eq 1:"Character must be irreducible";
  
  G := Group(Parent(chi));
  if H cmpeq "none" then
    H:=sub<G|>;
  end if;

  deg := Integers()!chi[1];
  K := Universe([chi[i] : i in [1..#chi]]);
  if not SparseCyclo then
    K := CyclotomicField(Conductor(K):Sparse := false);
  end if;

  if #H gt 1 then
     isgood, theta := IsHGood(G,chi,H);
     if not isgood then error "Subgroup supplied is not good."; end if;
  else
     if Best then
       H, theta := LookForSmallestH(G,chi);
     else 
       H, theta := LookForH(G,chi);
     end if;
     if H cmpeq false then
       return false;
     end if;
     if
	 FieldDegreeLimit gt 0 and
	 Degree(Universe([theta[i] : i in [1..#theta]])) gt FieldDegreeLimit
     then
        return false;
     end if;
  end if;
  vprint GModule, 1: "Using subgroup of order",#H;
  elts,A1,K := NsElts(G,chi,H,theta:SparseCyclo := SparseCyclo);
  vprint GModule, 1: "Independent set found";
  
  genims := [];
  if Type(G) eq GrpPC then ngens := NPCgens(G); else ngens := Ngens(G); end if;
  for i := 1 to ngens do
    vprint GModule, 1: "Computing image of generator",i;
    vtime GModule, 1: r := RepOfChiOnElt(G,chi,H,theta,elts,A1,K,G.i);
    Append(~genims,r);
  end for;

   //res :=  hom<G -> GL(deg,K) | genims: Check := false>;

   res := GModule(G, genims: Check := false);

   if BestField then
     vprint GModule, 1: "Trying to find smaller field";
     vtime GModule, 1:
	 res := AbsoluteModuleOverMinimalField(res: Character := chi);
   end if;

   res`Character := chi;
   return res;
end intrinsic;
