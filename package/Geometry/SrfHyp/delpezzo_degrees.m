// *********************************************************************
// * Package: delpezzo_degrees.mag                                     *
// * =============================                                     *
// *                                                                   *
// * Author: Josef Schicho                                             *
// *                                                                   *
// * Email : Josef.Schicho@oeaw.ac.at                                  *
// *                                                                   *
// * Date  : March 2008                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Lie algebra method for Del Pezzo surfaces of degree 5-9,        *
// *   including singular cases.                                       *
// *                                                                   *
// *                                                                   *
// *   Degree 7 & 8 routines updated August 2009 + Deg 5 added.        *
// *   In fact intrinsics for degrees 5,7 & 8 moved to SrfDP folder    *
// *    deg 6 left here as separate from ParametrizeDegree6DelPezzo    *
// *    which doesn't contain a singularity check and deg 9 here for   *
// *    inverse		       					       *
// *   								       *
// * Dependencies:                                                     *
// * scroll.mag                                                        *
// *                                                                   *
// *********************************************************************
freeze;




// ======================
// = Exported functions =
// ======================


// parametrize Del Pezzo surfaces of degree 6

import "classify.m": ImageAndInverse;

intrinsic ParametrizeDelPezzoDeg6(X::Sch)
-> BoolElt, MapIsoSch
{
Find a parametrization of Del Pezzo surface of degree 6 anticanonically embedded in 6-dimensional projective space. X may be singular (degenerate case)
}
  Sg := SingularSubscheme(X);
  if IsEmpty(Sg) then
    return ParametrizeDegree6DelPezzo(X);
  else
    Spts := PrimeComponents(SingularSubscheme(X));
    Y := Spts[1];
    Q := CoefficientRing(X);
    P5<y1,y2,y3,y4,y5,y6> := ProjectiveSpace(Q,5);
    f := Basis(Ideal(Y));
    Y, m, mi := ImageAndInverse(X,P5,f: birational:=true);
    //I := Ideal(Y);
    boo, prm := ParametrizeScroll(Y,ProjectiveSpace(Q,2));
    if boo then
      return true, prm*mi;
    else
      return false, _;
    end if;
  end if;
end intrinsic;

// parametrize Del Pezzo surfaces of degree 9
intrinsic ParametrizeDelPezzoDeg9(X::Sch) -> BoolElt, MapIsoSch
{
Alternative name for ParametrizeDegree9DelPezzo.
}
  return ParametrizeDegree9DelPezzo(X);
         
end intrinsic;
