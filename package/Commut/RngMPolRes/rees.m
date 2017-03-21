freeze;

/************************************************************************

Functions to compute the Rees algebra R(I) of an ideal I of an
                  affine algebra R.

   Allan Steel - 07/09 - with some minor adaptations by mch - 10/09

************************************************************************/

intrinsic ReesIdeal(R::RngMPolRes, I::RngMPol : a := 1) -> RngMPol, Map
{ For R=P/I1 an affine algebra and I an ideal of P considered as an ideal
  of R, returns the Rees ideal J s.t. Generic(J)/J is isomorphic to the
  graded Rees algebra over R,  R(I)/<a-torsion>. a is an element of P which
  gives a non-zero divisor in R and its default value is 1. Also returns
  the corresponding homomorphism P -> Generic(J) inducing the 
  R-algebra structure of R(I). }

    n := Rank(R);
    I1 := DivisorIdeal(R);
    P := Generic(I1);
    k := BaseRing(P);

    require Generic(I) cmpeq P:
	"Argument 2 must be an ideal of the polynomial ring cover of argument 1";

    boo,nzd := IsCoercible(P,a);
    require boo:
	"Parameter must be an element of the polynomial ring cover of argument 1"; 

    M:=sub<EModule(R, 1) | [[f]: f in Basis(I)]>;
    SB := MinimalBasis(MinimalSyzygyModule(M));

    r := #Basis(I);
    PZ := PolynomialRing(k, n + r, "grevlex");
    AssignNames(
	~PZ, [Sprint(P.i): i in [1..n]] cat [Sprintf("z%o", i): i in [1..r]]
    );
    f := hom<P -> PZ | [PZ.i: i in [1 .. n]]>;
    IZ := Ideal(f(Basis(I1)));
    phiz := Matrix([[f(v[j]): j in [1..Ncols(v)]]: v in SB]);
    zmat := Matrix([[PZ.(n + j)]: j in [1..r]]);
    mat := phiz*zmat;
    J := IZ + Ideal(Eltseq(mat));

    if nzd ne P!1 then
      g := f(nzd);
      return Saturation(J, g), f;
    else
      return J,f;
    end if;

end intrinsic;

intrinsic ReesIdeal(P::RngMPol, J::RngMPol, I::RngMPol : a := 1) -> RngMPol, Map
{ If R=P/J - an affine algebra - and I an ideal of P considered as an ideal
  of R, returns the Rees ideal K s.t. Generic(K)/K is isomorphic to the
  graded Rees algebra over R, R(I)/<a-torsion>. a is an element of P which
  gives a non-zero divisor in R and its default value is 1. Also returns
  the corresponding homomorphism P -> Generic(K) inducing the 
  R-algebra structure of R(I). }

    require Generic(J) cmpeq P:
	"Argument 2 must be an ideal of argument 1";

    require Generic(I) cmpeq P:
	"Argument 3 must be an ideal of argument 1";

    require IsCoercible(P,a):
	"Parameter must be an element of argument 1";

    return ReesIdeal(P/J, I : a := a);

end intrinsic;

intrinsic ReesIdeal(P::RngMPol, I::RngMPol) -> RngMPol, Map
{ I is an ideal of P. Returns the Rees ideal J s.t. Generic(J)/J is 
  isomorphic to the graded Rees algebra over P, R(I). Also returns
  the corresponding homomorphism P -> Generic(J) inducing the 
  P-algebra structure of R(I). }

    require Generic(I) cmpeq P:
	"Argument 2 must be an ideal of argument 1";

    return ReesIdeal(P/ideal<P|>, I);

end intrinsic;
 
