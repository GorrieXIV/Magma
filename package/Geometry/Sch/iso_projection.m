freeze;

//////////////////////////////////////////////////////////////////////
//  Functions to find isomorphic projections of projective schemes  //
//   down to subspaces. Also functions for embedding curves as      //
//   non-singular schemes in 3-dimensional projective space.        //
//         Mike Harrison 05/2004                                    //
//////////////////////////////////////////////////////////////////////

/*********** Functions for iso projection to subspaces *************/

/*function ProjectDown(X)

   assert IsOrdinaryProjective(X);
   P := AmbientSpace(X);
   Prng := CoordinateRing(P);
   F := BaseRing(Prng);
   assert IsField(F);
   I_X := Ideal(X);
   n := Rank(Prng);
   rng_map := hom<Prng -> Prng | [Prng.i : i in [1..n]]>; //identity
   
   // find good index for dehomogenisation
   i := n;
   while i gt 0 do
     if Prng.i notin I_X then break; end if;
     i -:= 1;
   end while;
   error if i eq 0,
      "X is the empty variety!";
   
   // compute the ideal of the "bad" variety for projection 
printf "Computing secant variety...\n";     
   Secs := Secants(X: index := i);
printf "Computing tangent variety...\n";
   Tans := TangentsAff(X: index := i);
   I_bad := Ideal(Secs) meet Ideal(Tans);
   
   // We compute the linear space to project to in one go
   // using noether normalisation :
   // If, after a linear change of variables, d+1 is the dim
   // of I_bad and Prng.(n-d),Prnd.(n-d+1),..Prng.n is
   // a set of Noether Norm variables for Prng/I_bad, then
   // projecting down to the linear space Prng.i=0, i >= n-d,
   // one dimension at a time from 
   // [1:0:0:0...] to Prng.1=0, then
   //   [1:0:0...] to Prng.1=0,Prng.2=0, then
   //   .............
   // gives an IM of X to it's image Y, and the union of Y's
   // Tans space and (closed) Secs space fill up the linear
   // space.
printf "Computing Noether normalisation...\n";
   d, h, hinv := NoetherNormalisation(I_bad);
   if d eq n+1 then
      return X,IdentityMap(P);
   end if;
   I_X := ideal<Prng | [h(b) : b in Basis(I_X)]>;
   rng_map := hinv * rng_map;
 
   // do the projection.
   Prng1 := PolynomialRing(F,d);
   h := hom<Prng -> Prng1 | [0 : i in [1..n-d]] cat
                            [Prng1.i : i in [1..d]]>;
   hinv := hom<Prng1 -> Prng | [Prng.i : i in [n-d+1..n]]>;
printf "Doing projection by elimination...\n";
   I_X := EliminationIdeal(I_X,n-d);
printf "Done!\n";
   I_X := ideal<Prng1 | [h(b) : b in Basis(I_X)]>;
   rng_map := hinv * rng_map;
   
   // finish off
   P1 := Proj(Prng1);
   sch_map := map< P -> P1 | [rng_map(Prng1.i) : i in [1..Rank(Prng1)]]>;
   return Scheme(P1,I_X),sch_map;
   
end function;*/

declare verbose IsoToSub, 1;

// Looks for a point in the ambient space P of X not lying
// in the secant or tangent spaces of X.
// For char > 0 and non-finite base fields, only considers
// points with coordiantes in the (finite) chracteristic field.
// Gives up after so many random tries in the char >0 case.
function GoodProjector(X)

   P := AmbientSpace(X);
   F := BaseRing(X);
   n := Dimension(P);
   char := Characteristic(F);
   //first look for points of form (0:0..:0:1:0..:0)
   for i in [1..n+1] do
      pt := P![F| (j eq i) select 1 else 0 : j in [1..n+1]];
      if (not IsInSecantVariety(X,pt)) and
             (not IsInTangentVariety(X,pt)) then
          return pt,i;
      end if;
   end for;
   //now look for points with all coords 0,1,-1
   r := (char eq 2) select 2 else 3;
   for m in [1..n] do
     for N in [(r^m)+1 .. 2*(r^m)-1] do
      vec := [F|(k eq 2) select -1 else k : k in Intseq(N,r)];
      vec cat:= [F!0:j in [1..n-m]];
      pt := P!vec;
      if (not IsInSecantVariety(X,pt)) and
             (not IsInTangentVariety(X,pt)) then
          return pt,m+1;
      end if;
     end for;
   end for;
   // finally look for random coord points over finite fields
   // and "size" restricted ones over others.
   tries := 0;
   b_FF := IsFinite(F);
   if (char in [2,3]) and ((not b_FF) or (#F le 3)) then
      error "Failed to find good projection point!";
   end if;
   N := 4;
   while true do
      while true do
        if b_FF then
          seq := [Random(F):i in [1..n+1]];
        else
          seq := [F|Random([-N..N]):i in [1..n+1]];
        end if;
        if &or[c ne F!0 : c in seq] then
            pt := P!seq; break;
        end if;
      end while;
      if (not IsInSecantVariety(X,pt)) and
             (not IsInTangentVariety(X,pt)) then
          break;
      end if;
      tries +:= 1;
      if IsDivisibleBy(tries,50) then
          N *:= 2;
      end if;
      if (char gt 0) and (tries eq 1000) then
          error "Failed to find good projection point!";
      end if;
   end while;
   cs := Coordinates(pt);
   ind := Index(cs,F!1);
   if ind gt 0 then return pt,ind; end if; //should be true!
   ind := Min([i:i in [1..n+1] | cs[i] ne F!0]);
   return pt,ind;

end function;
 
intrinsic IsomorphicProjectionToSubspace(X::Sch) -> Sch, MapSch
{ Isomorphically maps scheme X of dimension d in ambient projective
  space of dimension n down to a projective space of dimension 2d+1
  (if n > 2d+1) by appropriate point projections. }

   require IsOrdinaryProjective(X):
                     "Scheme should be ordinary projective";
   P := AmbientSpace(X);
   F := BaseRing(P);
   require IsField(F): "Scheme should be defined over a field";
   
   d := Dimension(X);
   n := Dimension(P);
   mp := IdentityMap(P);
   X1 := X;
   while n gt 2*d+1 do
       vprintf IsoToSub:
          "Projection from dimension %o to dimension %o:\n",n,n-1;
       vprint IsoToSub: "Finding good projection point...";
       vtime IsoToSub: Pt,ind := GoodProjector(X1);
       vprint IsoToSub:"Performing projection...";
       tm := Cputime();
       coords := Coordinates(Pt);
       Prng := CoordinateRing(P);
       hm := hom<Prng->Prng | [(i eq ind) select Prng.i else
                      Prng.i + coords[i]*(Prng.ind) : i in [1..n+1]]>;
       I_X1 := ideal<Prng | [hm(b) : b in Basis(Ideal(X1))]>;
       mp := Expand(mp * map<P -> P | [(i eq ind) select P.i else
                         P.i - coords[i]*(P.ind) : i in [1..n+1]]>);
       if ind gt 1 then
           hm := hom<Prng->Prng | [Prng.ind] cat 
	   [(i eq ind) select Prng.1 else Prng.i : i in [2..n+1]]>;
           I_X1 := ideal<Prng | [hm(b) : b in Basis(I_X1)]>;
           mp := Expand(mp * map<P -> P | [P.ind] cat 
                   [(i eq ind) select P.1 else  P.i  : i in [2..n+1]]>);
       end if;
       Q := PolynomialRing(F,n);
       hm := hom<Prng->Q | [Q!0] cat [Q.i : i in [1..n]] >;
       I_X1 := ideal<Q | [hm(b) : b in Basis(J)]> where J is
                         EliminationIdeal(I_X1,1);
       P1 := ProjectiveSpace(Q);
       mp := Expand(mp * map<P->P1 | [P.i : i in [2..n+1]]>);
       P := P1;
       X1 := Scheme(P,I_X1);
       vprintf IsoToSub: "Time: %o\n",Cputime(tm);
       n -:= 1;
   end while;
   return X1, map<X->X1 | DefiningEquations(mp) : Check := false>;
			//Restriction(mp,X,X1);
   
end intrinsic;

/************* Functions for embedding Crv in P3 *****************/

declare verbose EmbCrv, 1;

// finds a small degree very ample rational divisor
// on genus 1 Crv C
function GenusOneDivisor(C)

    F<a,b> := FunctionField(C);
    DG := DivisorGroup(C);
    min_deg := 0;
    for fn in [a,b] do
       D := Divisor(DG,fn);
       plcs := Support(D);
       degs := [Degree(plc) : plc in plcs];
       // preference for degree 1 divisors
       i := Index(degs,1);
       if i gt 0 then return 3*(DG!plcs[i]); end if;
       i := Index(degs,3);
       if i gt 0 then return DG!plcs[i]; end if;
       for i in [1..#plcs] do
          deg := degs[i];
          E := DG!plcs[i];
          if min_deg eq 0 then
             div_min := E; min_deg := deg;
          else
             gcd,a,b := XGCD(deg,min_deg);
             if gcd lt min_deg then
                div_min := a*E+b*div_min;
                min_deg := gcd;
             end if;
          end if;
          if min_deg eq 1 then return 3*div_min; end if;
          if min_deg eq 3 then return div_min; end if;
        end for;
     end for;
     return ((min_deg eq 2) select 2*div_min else div_min);

end function;

intrinsic EmbedPlaneCurveInP3(C::Crv) -> Sch, MapSch
{ Finds an embedding of C as a non-singular subscheme X of
  ordinary 2- or 3-dimensional projective space.}

  /* Finds an embedding of C in some projective space by using
      some very ample divisor and then projects down to 3D if
      necessary. METHOD FOR HYPERELLIPTICS NEEDS IMPROVEMENT. */
    if IsAffine(C) then
      Cp := ProjectiveClosure(C);
      mp := Restriction(ProjectiveClosureMap(
                           AmbientSpace(C)),C,Cp);
    else // C projective
      Cp := C;
      mp := IdentityMap(Cp);
    end if;
    
    // test for geometric integrability
    require HasFunctionField(Cp) and 
      (DegreeOfExactConstantField(AlgorithmicFunctionField(FunctionField(Cp)))
      			eq 1) :
	"Curve must be geometrically integral";

    g := Genus(Cp);
    if g eq ArithmeticGenus(Cp) then // Cp nonsingular already!
      return Cp,IdentityMap(Cp);
    end if;
    if g eq 0 then
    vprint EmbCrv: "Curve of genus 0.",
       "Mapping to 2-space by -(canonical divisor) map";
      D := -CanonicalDivisor(Cp);
    elif g eq 1 then
      D := GenusOneDivisor(Cp);
      vprint EmbCrv:"Curve of genus 1.";
      vprintf EmbCrv:
       "Mapping to %o-space by small divisor map\n",Degree(D)-1;
    else
      vprintf EmbCrv:"Curve of genus %o.\n",g;
      vprintf EmbCrv:
        "Mapping to %o-space by canonical divisor map\n",g-1;
      D := CanonicalDivisor(Cp);
    end if;
    phi := DivisorMap(D);
    X := phi(Cp);
    gX := ArithmeticGenus(X);
    if gX eq g then // C not hyperelliptic
      vprint EmbCrv:
        "Map was an embedding (non-hyperelliptic curve).";
      if (g ge 5) or ((g eq 1) and (Degree(D) ge 5)) then
         vprint EmbCrv:"Beginning projection to 3-space.";
         Y,proj_map := IsomorphicProjectionToSubspace(X);
         phi := phi * proj_map;
      else
         Y := X;
      end if;
      return Y,mp*phi;
    end if;
    // hyperelliptic case
    assert gX eq 0;
    vprintf EmbCrv:"Curve hyperelliptic genus %o: recomputing.\n",g;
    if g eq 2 then
       vprint EmbCrv:"Mapping to 5-space by 3*(canonical divisor) map";
       D := 3*CanonicalDivisor(Cp);
    else
       vprintf EmbCrv:
         "Mapping to %o-space by 2*(canonical divisor) map\n",4*g-3;
       D := 2*CanonicalDivisor(Cp);
    end if;
    phi := DivisorMap(D);
    X := phi(Cp);
    vprint EmbCrv:"Beginning projection to 3-space.";
    Y,proj_map := IsomorphicProjectionToSubspace(X);
    assert ArithmeticGenus(Y) eq g;
    return Y,mp*phi*proj_map;
  
end intrinsic;
