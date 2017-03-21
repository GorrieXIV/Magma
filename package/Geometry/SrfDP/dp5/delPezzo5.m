// *********************************************************************
// * Package: delpezzo_degrees.mag                                     *
// * =============================                                     *
// *                                                                   *
// * Author: Josef Schicho                                             *
// *                                                                   *
// * Email : Josef.Schicho@oeaw.ac.at                                  *
// *                                                                   *
// * Date  : August 2009                                               *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   A geometric method for Del Pezzo surfaces of degree 5.          *
// *                                                                   *
// *                                                                   *
// * Dependencies:                                                     *
// * none                                                              *
// *                                                                   *
// *********************************************************************
freeze;




// ======================
// = Exported functions =
// ======================


// parametrize Del Pezzo surfaces of degree 9
intrinsic ParametrizeDegree5DelPezzo(X::Sch)
-> MapIsoSch
{
find a parametrization of Del Pezzo surface of degree 5 
anticanonically embedded in 5-dimensional projective space.
The computed map will have degree 5, except in some luck cases.
This is not always the best possible, but it is best possible
if the surface is minimal.
}
  require IsOrdinaryProjective(X) and (Dimension(Ambient(X)) eq 5):
	"A variety in 5-dimensional projective space expected.";
  Qs := DefiningEquations(X);
  if (#Qs ne 5) or &or[TotalDegree(f) ne 2 : f in Qs] then
	Saturate(~X);
	Qs := [ p : p in Basis(Ideal(X)) | TotalDegree(p) eq 2 ];
  end if;

  P2 := ProjectiveSpace(BaseRing(X),2);
  // access of input structure
  R := Generic(Ideal(X));
  Q := BaseRing(R);
  Eqs := [ p : p in Qs | TotalDegree(p) eq 2 ]; //Eqs = Qs!
  P5 := AmbientSpace(X); 
  Par<s,t,u> := CoordinateRing(P2);
  V6 := VectorSpace(Q,6);

  // Compute a pair of points
  F4 := Ideal([ Eqs[i] : i in [1..4]]);
  Line := IdealQuotient(F4,Eqs[5]);
  if Dimension(Line) eq 3 then 
  // a special case. The syzygy defines a planar cone, we project from it
    pinv := map< X -> P2 | Basis(Line)>;
    chk, par := IsInvertible(pinv);
    if chk then
      return par;
    else
      error "special syzygy did not work";
    end if;
  end if;
  assert Dimension(Line) eq 2;
  Ptboth := Line + Ideal([Eqs[5]]);
  polraw := Basis(EliminationIdeal(Ptboth,4))[1];
  if TotalDegree(polraw) lt 2 then
  // bad projection, need to use different variables
    ok := Line;
    i := 1;
    while (R.i in ok) do i:=i+1; end while;
    ok := ok + Ideal([R.i]);
    j := i+1;
    while (R.j in ok) do j:=j+1; end while;
    polraw := Basis(EliminationIdeal(Ptboth,{R.i,R.j}))[1]; 
  end if;
  U := PolynomialRing(Q); T := U.1;
  pol := hom< R -> U | 1,1,1,1,1,T>(polraw);

  if IsIrreducible(pol) and Degree(pol) eq 2 then
  // pair is defined over an extension.
  // compute a rational point by Sheppard-Barrons parametrization method
    D:=Discriminant(pol);
    E<alpha> := ext< Q | T^2-D >;
    Pt1 := Coordinates(RationalPoints(Scheme(P5,Ptboth),E)[1]);
    evl := hom< R -> E | Pt1 >;
    JMe := [[ evl(JacobianMatrix(Eqs)[i,j]) : j in [1..6] ] : i in [1..5]];
    Ve6 := VectorSpace(E,6);
    Tangents := Nullspace(Transpose(Matrix(JMe)));
    Tpar := ExtendBasis([Ve6!Pt1],Tangents);

    B1 := [ Eltseq(Pt1[i])[1] : i in [1..6] ];
    B2 := [ Eltseq(Pt1[i])[2] : i in [1..6] ];
    B3 := [ Eltseq(Eltseq(Tpar[2])[i])[1] : i in [1..6] ];
    B4 := [ Eltseq(Eltseq(Tpar[2])[i])[2] : i in [1..6] ];

    A<y1,y2,y3,y4> := PolynomialRing(Q,4);
    plan := hom< R -> A | [y1*B1[i]+y2*B2[i]+y3*B3[i]+y4*B4[i] : i in [1..6] ]>;
    tosolve := Ideal([ plan(Eqs[i]) : i in [1..5] ]);
    irrev := Ideal([ plan(Basis(Ptboth)[i]) : i in [1..5] ]);
    irrev := Ideal(GroebnerBasis(irrev));
    res:= Saturation(tosolve,irrev);
    ptg := Coordinates(RationalPoints(Scheme(ProjectiveSpace(A),res))[1]);
    ptpar:= Eltseq(ptg[1]*V6!B1+ptg[2]*V6!B2+ptg[3]*V6!B3+ptg[4]*V6!B4);

  else
  // take the first of the two points.
    ptpar := Coordinates(RationalPoints(Scheme(P5,Ptboth))[1]);
  end if;

  // projection from the tangent plane
  evl := hom< R -> Q | ptpar >;         
  JMe := [[ evl(JacobianMatrix(Eqs)[i,j]) : j in [1..6] ] : i in [1..5]];
  if Rank(Matrix(JMe)) lt 3 then
  // hit singular point by chance!
    pr := Projection(X,X!ptpar);    
    Y := pr(X);
    chk, half := ParametrizeScroll(Y,P2);
    if not chk then 
    // this should not be possible
      error "points disappeared by projection";
    end if;
    _,hinv := IsInvertible(half);
    pinv := pr * hinv;
    chk, par := IsInvertible(pinv);
    if not chk then
    // this should not be possible either
      error "projection from singular point not birational";
    end if;
    return par;
  end if;
  Tangents := Nullspace(Transpose(Matrix(JMe)));
  Tpar := ExtendBasis([V6!ptpar],Tangents);
  new := ExtendBasis(Tpar,V6);
  _,back := IsInvertible(Matrix(new));
  parai := [ &+([ back[j,i]*P5.j : j in [1..6]]) : i in [4..6] ];

  // we could use IsInvertible now, but the following is faster
  FF<p,q> := FunctionField(Q,2);
  FFi<p,q> := PolynomialRing(Q,2);
  Ve6 := VectorSpace(FF,6);
  B1 := Eltseq(Ve6!Tpar[1]);
  B2 := Eltseq(Ve6!Tpar[2]);
  B3 := Eltseq(Ve6!Tpar[3]);
  B4 := Eltseq(p*Ve6!new[4]+q*Ve6!new[5]+1*Ve6!new[6]);
  A<y1,y2,y3,y4> := PolynomialRing(FF,4);
  plan := hom< R -> A | [y1*B1[i]+y2*B2[i]+y3*B3[i]+y4*B4[i]:i in [1..6]]>;
  tosolve := Ideal([ plan(Eqs[i]) : i in [1..5] ]);
  irrev := Ideal([y2,y3,y4]);
  res:= Saturation(tosolve,irrev);
  if ( Dimension(res) gt 1 or Degree(res) gt 1 ) then
  // additional base points. 
  // Only happens for small examples, so we can afford an expensive method
    pinv := map< X -> P2 | parai>;
    chk, par := IsInvertible(pinv);
    if chk then
      return par;
    else
    // this should not be possible
      error "projection from tangent plane is not birational.";
    end if;
  end if;
  ptg := Coordinates(RationalPoints(Scheme(ProjectiveSpace(A),res))[1]);
  ptpar := Eltseq(ptg[1]*Ve6!B1+ptg[2]*Ve6!B2+ptg[3]*Ve6!B3+ptg[4]*Ve6!B4);
  Deno := Denominator(ptpar[1]);
  for i in [2..6] do
    Deno := LeastCommonMultiple(Denominator(ptpar[i]),Deno);
  end for;
  ptpar := [ FFi!Numerator(ptpar[i]*Deno) : i in [1..6] ];
  rename := hom< FFi -> Par | s,t >;
  homog := map < FFi -> Par | f :-> 
    &+([rename(HomogeneousComponents(f+p^6)[i])*u^(6-i):i in [1..6]])
  >;
  para := [ homog(ptpar[i]): i in [1..6]];
  phi := map<P2 -> X | para, parai : Check:=false, CheckInverse:=false>;

  return phi;

end intrinsic;
