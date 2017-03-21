freeze;
//////////////////////////////////////////////////////////////////////////////////
//   File for miscellaneous surface constructors - mch - 02/13			//
//    - currently, just have RationalRuledSurface to construct surface scrolls, //
//        a convenience function for the Kummer surface of a genus 2 curve      //
//      and the general (not just for surfaces) RandomCompleteIntersection      //
//////////////////////////////////////////////////////////////////////////////////
   
intrinsic RationalRuledSurface(P::Prj, n::RngIntElt) -> Srfc, MapSch
{Returns the rational ruled surface X (scroll) with parameters n,m-1-n in
 the ordinary projective space P of dimension m. Also returns the map from
 X to P^1 whose fibres are the lines giving the ruling on X.}
    require IsOrdinaryProjective(P):
	"P must be an ordinary projective space";
    R := CoordinateRing(P);    
    require Rank(R) ge 4:
	"P must have dimension at least 3";
    require (n ge 0) and (n+2 le Rank(R)):
	"n+1 must be positive and less than the dimension of P";

    r := Rank(R);
    m := r-2-n;
    M := HorizontalJoin(Matrix([[R|R.i : i in [1..n]],[R|R.i : i in [2..n+1]]]),
	   Matrix([[R|R.i : i in [n+2..r-1]],[R|R.i : i in [n+3..r]]]));
    mins := Minors(M,2);
    if m*n gt 0 then
       X := Surface(P,mins : Saturated := true, Check := false, Nonsingular := true);
    elif n eq 0 then
       X := Surface(P,mins : Saturated := true, Check := false, Nonsingular := false);
       X`SingularSubscheme := Scheme(X,[R.i : i in [2..r]]);
    else //m = 0
       X := Surface(P,mins : Saturated := true, Check := false, Nonsingular := false);
       X`SingularSubscheme := Scheme(X,[R.i : i in [1..r-1]]);
    end if;
    X`ACM := true;
    X`arith_gor := (r eq 4);
    mp := map<X -> P1 | [[M[1,i],M[2,i]] : i in [1..Ncols(M)]] : Check := false>
		where P1 := ProjectiveSpace(BaseRing(P),1);
    return X,mp;

end intrinsic;

intrinsic RandomCompleteIntersection(P::Prj, ds::SeqEnum[RngIntElt] : Nonsingular := true,
		RndP := 1) -> Sch
{ Returns a complete intersection scheme in ordinary projective space P defined by
  random homogeneous polynomials of degrees ds[1],..,ds[n]. If parameter Nonsingular is
  true (the default), a non-singular scheme will always be returned. The base field must
  be the rationals or a finite field. If it is the rationals, the coefficients of the
  polynomials will be random integers of absolute value <= parameter RndP, which has
  the default value 1. }

    require IsOrdinaryProjective(P):
	"P must be an ordinary projective space";
    R := CoordinateRing(P);
    k := BaseRing(R);
    require ISA(Type(k),FldFin) or ISA(Type(k),FldRat):
	"The base ring of P must be a finite field or the rationals";
    require &and[d gt 0 : d in ds]:
	"ds must be a sequence of positive integers";
    require #ds lt Rank(R):
	"The length of the sequence ds must be at most the dimension of P";

    d := Rank(R)-1-#ds;
    tries := 0;
    while tries lt 10 do
	tries +:= 1;
	Fs := [Random(d,R,RndP) : d in ds];
	X := Scheme(P,Fs);
	if Dimension(X) ne d then continue; end if;
	if Nonsingular then
	   if not IsNonsingular(X) then continue; end if;
	   if d eq 1 then 
	      return Curve(P,Fs : Nonsingular := true, GeometricallyIrreducible := true);
	   elif d eq 2 then
	      return Surface(P,Fs : Check := false, Nonsingular := true);
	   else
	      return X;
	   end if;
	else
	   if d eq 1 then 
	      return Curve(P,Fs);
	   else
	      return X;
	   end if;	
	end if;
    end while;
    error "Failed to generate non-singular complete intersection in 10 tries.";

end intrinsic;

intrinsic KummerSurfaceScheme(C::CrvHyp) -> Srfc
{ Returns the Kummer surface of the Jacobian of genus 2 hyperelliptic curve C as a
  (singular) quartic hypersurface in P^3 }

    require Genus(C) eq 2 : "Argument must be a genus 2 hyperelliptic curve";
    S := KummerSurface(Jacobian(C));
    f := DefiningPolynomial(S);
    R := Generic(Parent(f));
    return Surface(Proj(R),f : Check := false);

end intrinsic;
