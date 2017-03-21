freeze;

import "../../Commut/RngMPol/sheaf.m": QuotientIdealBasis;

intrinsic IneffectiveDivisorToSheaf(X::Sch,I::RngMPol,J::RngMPol: GetMax := true) -> ShfCoh
{Returns the invertible sheaf <-> the (locally principal) effective divisor on X defined by ideal I. If GetMax is true (the default), the module computed is the maximal separated one, the associated divisor map is computed and stored and a basis for the Riemann-Roch space is computed and stored at the same time in a slightly more efficient way than for the direct sheaf computation.}
    R := CoordinateRing(Ambient(X));
    Saturate(~X);
    require Generic(I) eq R:
	"I doesn't lie in the coordinate ring of X";
    Saturate(~X);
    IX := Ideal(X);
    ID := Saturation(I + IX);

    // IDEA: let r be the smallest s.t. ID_r != IX_r.
    //  Let Fr in ID_r\IX_r and IE=(<Fr>+IX:ID). Then
    //  IE is the ideal defining an effective divisor of X with D+E=rH where
    //  H is the hyperplane section and L(D)=L(rH-E) which is represented by
    //  the module (IE/IX)(r).
    //  Note also that (IE/IX)(r) will be saturated in degrees >= 0 if
    //  R_i = (R/I)_i [ith graded pieces] for i >= r

    dX := Degree(HilbertPolynomial(IX)); dD := Degree(HilbertPolynomial(ID));
    require dX eq dD+1:
	"I doesn't define a codimension 1 subscheme of X";
    hD := HilbertSeries(ID);
    hX := HilbertSeries(IX);
    hXD := hX-hD;
    r := Valuation(Numerator(hXD));

    // find an Fr
    BX := GroebnerBasis(IX); BD := GroebnerBasis(ID);
    Reverse(~BX); Reverse(~BD);
      // assumed here that R has a degree ordering
    i := 1; while LeadingTotalDegree(BD[i]) lt r do i +:=1; end while;
    if LeadingTotalDegree(BX[#BX]) ge r then
      j := 1; while LeadingTotalDegree(BX[j]) lt r do j +:=1; end while;
      while (j le #BX) and (BD[i] eq BX[j]) do
	j +:=1; i +:=1;
      end while;
    end if;
    Fr := BD[i];
    // NB : really need to check that Fr not an IX zero-divisor here.
    //  If IX is equidimensional then STP that Dim(<Fr,IX>)=Dim(IX)+1

    r1 := r;
    if GetMax then
	n := Rank(R);
	OXres := MinimalFreeResolution(QuotientModule(IX));
	if #Terms(OXres) ge n+2 then
	    assert  #Terms(OXres) eq n+2; //as IX is saturated
	    h1 := Term(OXres,n-1);
	    // Ext^(n-1)(R/I,R) is a quotient of the dual of h1.
	    // This is dual to sum_r H^1(P^(n-1),I(r)) with the
	    // r graded piece <-> the (-n-r)th graded piece of
	    // the Ext module. We want the max r >= 0 s.t.
	    // this rth graded piece is non-zero which is the
	    // max r s.t. R_r -> (R/I)_r ISN't onto (if r exists)
	    r1 := Max(ColumnWeights(h1))-n+1;
	    r1 := Max(r,r1);
	end if;
    end if;
    if r1 gt r then
	//as IX saturated, x^(r1-r)Fr not in IX for some variable x
	i := 1; while (R.i)^(r1-r)*Fr in IX do i +:=1; end while;
	Fr := Fr * (R.i)^(r1-r);
    end if;

    // Get IE
    IXF := Saturation(IX+(ideal<R|Fr> * J));
    IE := ColonIdeal(IXF,ID); // IE is automatically saturated

    // Get (IE/IX)(r1)
    M0 := QuotientModule(IX);
    M0 := Twist(M0,r1);
    M := sub<M0|[M0![b] : b in Basis(IE)]>;
    M := quo<M|>; // temp fix for minimisation!

    S := HackobjCreateRaw(ShfCoh);
    S`M := M; S`X := X; S`Isupp := IX; S`Iann := IX;
    if GetMax then
	S`Mfull := M;
	//get basis for divisor map
	B := QuotientIdealBasis(IE,IX,r1);
	S`rr_space := <B,Fr>;
if #B ne 0 then	// THINK: handle this carefully
	S`div_map := map<X->ProjectiveSpace(BaseRing(X),#B-1)|B>;
end if;
	M0 := sub<M0|[M0![b] : b in B]>;
	M0 := quo<M0|>; // temp fix for minimisation!
	S`M0 := M0;
    end if;

    return S;

end intrinsic;

intrinsic IneffectiveRiemannRochBasis(X::Sch,I::RngMPol,J::RngMPol) -> SeqEnum, RngMPolElt, ShfCoh
{Returns a basis for the Riemann-Roch space of the (locally principal) effective divisor D on variety X defined by ideal I. Returned as a sequence [F1,..,Fn] of numerators and a denominator G such that rational functions Fi/G on X give a basis for L(D).  An invertible sheaf representing the divisor class of D is also returned.}
	S := IneffectiveDivisorToSheaf(X,I,J : GetMax := true);
    rr_sp := S`rr_space;
    return rr_sp[1], rr_sp[2], S;

end intrinsic;

