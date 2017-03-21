freeze;

//Generalized Srivastava Code			Lancelot Pecquet, 1996

// q is a power of a prime number
// m is ge 1
// F is a finite field of cardinality q^m
// alpha is a sequence of n distincts elements of F
// w is a sequence of s distincts elements of F
// The elements of alpha and w are distincts
// z is a sequence of n non-zero elements of F
// t is a non-negative integer

intrinsic GeneralizedSrivastavaCode(alpha::[FldFinElt], W::[FldFinElt],
	Z::[FldFinElt], t::RngIntElt, S::FldFin) -> Code
{Given sequences alpha = [a_1, ..., a_n], W = [w_1, ..., w_s], and
Z = [z_1, ... z_k] of elements from the extension field K of the finite field
S, such that the elements of alpha and Z are non-zero and the n + s elements of
alpha and W are distinct, together with an integer t > 0,
construct the generalized Srivastava code of parameters alpha, W, Z,
t, over S}

	requirege t, 1;

	n := #alpha;
    	require n ge 1: "Argument 1 should have at least one element";

	s := #W;
    	require s ge 1: "Argument 2 should have at least one element";
	require #Z eq n: "Arguments 1 and 3 must have the same length";

	F := Parent(alpha[1]);
	require S subset F:
	    "Elements of argument 1 should be in a superfield of argument 5";

	require Parent(W[1]) cmpeq Parent(alpha[1]):
	    "Elements of argument 1 and 2 should be in the same field";

	require Parent(Z[1]) cmpeq Parent(alpha[1]):
	    "Elements of argument 1 and 3 should be in the same field";

	require 0 notin Z: "Argument 3 should consist of nonzero elements";

	require #(SequenceToSet(alpha cat W)) eq n + s:
	    "Arguments 1 and 2 should together consist of distinct elements";

	V := RSpace(F, n);
	H := RMatrixSpace(F,t*s,n)! &cat &cat [[[Z[j]/(alpha[j]-W[l])^i 
		:j in [1 .. n]]
		:i in [1 .. t]] :l in [1 .. s]];
	return SubfieldSubcode(Dual(LinearCode(sub<V | RowSpace(H)>)),S);
end intrinsic;


//Srivastava Code                       Lancelot Pecquet, 1996

// q is a power of a prime number
// m is ge 1 
// F is a finite field of cardinality q^m
// alpha is a sequence of n distincts, nonzero elements of F
// w is a sequence of s distintcts elements of F
// The elements of alpha and w are distincts
// mu is an elt of Z

intrinsic SrivastavaCode(alpha::[FldFinElt], W::[FldFinElt],mu::RngIntElt,
			S::FldFin) -> Code
{Given sequences alpha = [a_1, ..., a_n] and W = [w_1, ..., w_s] of elements
from the extension field K of the finite field S, such that the elements of
alpha are non-zero and the n + s elements of alpha and W are distinct,
together with an integer mu, construct a Srivastava code of parameters
alpha, W, mu, over S}

	n := #alpha;
    	require n ge 1: "Argument 1 should have at least one element";

	s := #W;
    	require s ge 1: "Argument 2 should have at least one element";

	require S subset Parent(alpha[1]):
	    "Elements of argument 1 should be in a superfield of argument 4";

	require Parent(W[1]) cmpeq Parent(alpha[1]):
	    "Elements of argument 1 and 2 should be in the same field";

	require 0 notin alpha:
	    "Argument 1 should consist of nonzero elements";

	require #(SequenceToSet(alpha cat W)) eq n + s:
	    "Arguments 1 and 2 should together consist of distinct elements";

        Z := [alpha[i]^mu : i in [1 .. #alpha]];
        return GeneralizedSrivastavaCode(alpha,W,Z,1,S);
end intrinsic;

intrinsic GabidulinCode(alpha::[FldFinElt], w::[FldFinElt],z::[FldFinElt],
        t::RngIntElt) -> Code
{Given alpha = [a_1,...a_n], and w = [w_1,...w_s] a sequence of n+s distincts 
elements of GF(q),  z, a sequence of n nonzero elements of GF(q), and t > 0, 
construct the Gabidulin MDS code of parameters alpha, w, z, t over GF(q)}
        requirege t,1;
        n := #alpha;
        require n ge 1: "Argument 1 should have at least one element";
        s := #w;
        require s ge 1: "Argument 2 should have at least one element";
        require #z eq n: "Argument 1 and 3 must have the same length";
        F := Parent(alpha[1]);
        q := #F;
        require #F eq #Parent(w[1]):
        "Elements of argument 1 and 2 should be in the same field";
        require #F eq #Parent(z[1]):    
        "Elements of argument 1 and 3 should be in the same field";
        require not (0 in z):"Argument 3 should consist of nonzero elements";
        require #(SequenceToSet(alpha cat w)) eq n + s:
        "Argument 1 and 2 should consist of ",n," + ",s," distincts elements";
        V := RSpace(F,n);
        H := RMatrixSpace(F,t*s,n)! &cat &cat [[[z[j]/(alpha[j]-w[l])^i 
                :j in [1 .. n]]
                :i in [1 .. t]] :l in [1 .. s]];
        C := SubfieldSubcode(Dual(LinearCode(sub<V | RowSpace(H)>)),F);
        AssertAttribute(C,"MinimumWeight",Length(C)-Dimension(C)+1);
        return C;
end intrinsic;

//Chien-Choy Generalized BCH codes		Lancelot Pecquet, 1996

// n is relatively prime to q
// F = GF(q^m) is the splitting field of X^n - 1 over GF(q).
// P is a polynomial in F[X], deg(P) le n-1, P relatively prime to X^n-1
// G is a polynomial in F[X], r=deg(G) le n-1, G relatively prime to X^n-1

intrinsic ChienChoyCode(P::RngUPolElt,G::RngUPolElt,n::RngIntElt,S::FldFin)
			-> Code
{Given polynomials P and G over a finite field F, an integer n > 1, together
with a subfield S of F, such that n is coprime to the cardinality of S, F
is the splitting field of x^n - 1 over S, P and G are coprime to x^n - 1
and both have degree less than n, construct the Chien-Choy generalised BCH code
with parameters P, G, n over S}

	requirege n, 2;
	require Degree(P) lt n:
	    "Degree of argument 1 (", Degree(P),
	    ") should be < argument 3 (", n, ")";
	require Degree(G) lt n:
	    "Degree of argument 2 (", Degree(G),
	    ") should be < argument 3 (", n, ")";

	F := CoefficientRing(Parent(P));
	require Type(F) eq FldFin and S subset F:
	    "Argument 1 should be a polynomial over an extension ",
	    "field of argument 4";
	require F cmpeq CoefficientRing(Parent(G)):
	    "Argument 1 and 2 should be polynomials over the same field";

	r := Degree(G);
	FX := PolynomialRing(F); X := FX.1;
	require Degree(GCD(P, X^n-1)) eq 0:
	    "Argument 1 should be relatively prime to x ^", n, " - 1";
	require Degree(GCD(G, X^n-1)) eq 0:
	    "Argument 2 should be relatively prime to x ^", n, " - 1";
	require n mod #PrimeField(F) ne 0:
	    "Argument 3 (", n, ") should be coprime to size of argument 4 (",
	    #S, ")";

	alpha := RootOfUnity(n, F);
	require Parent(alpha) cmpeq F:
	    "Arguments 1 and 2 should be in a splitting field of x ^",
	    n, " - 1 over argument 4";

	p := InverseMattsonSolomonTransform(P, n);
	g := InverseMattsonSolomonTransform(G, n);	
	V := RSpace(F, n);
	H := RMatrixSpace(F, r, n)! 
		&cat [[Coefficient(p, j)*alpha^(i*j)/Coefficient(g, j) 
		:j in [0 .. n-1]]
		:i in [1 .. r]];
	return SubfieldSubcode(Dual(LinearCode(sub<V | RowSpace(H)>)), S);
end intrinsic;
