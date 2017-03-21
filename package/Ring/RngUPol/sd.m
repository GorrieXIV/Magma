freeze;

intrinsic SwinnertonDyerPolynomial(n::RngIntElt) -> RngUPol
{The n-th SwinnertonDyer polynomial of degree 2^n}
    requirege n, 1;

    Z := IntegerRing();
    P := [2];
    for i := 2 to n do
        Append(~P, NextPrime(P[#P]));
    end for;
    A := AlgebraicClosure();
    S := [Sqrt(A ! p): p in P];
    P := PolynomialRing(A); z := P.1;
    f := &*[z + &+[t[i]*S[i]: i in [1..n]]: t in CartesianPower({-1, 1}, n)];
    return PolynomialRing(Z) ! f;
end intrinsic;
