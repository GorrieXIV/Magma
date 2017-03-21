freeze;

intrinsic BrandtModuleDimension(D::RngIntElt) -> RngIntElt
    {The dimension of the Brandt module of level D.}
    return BrandtModuleDimension(D,1);
end intrinsic;

intrinsic BrandtModuleDimension(D::RngIntElt,N::RngIntElt) -> RngIntElt
    {The dimension of the Brandt module of level (D,N).}
    require GCD(D,N) eq 1 : "Arguments must be coprime.";
    Dprms := PrimeDivisors(D);
    Nprms := PrimeDivisors(N);
    require D eq &*Dprms and #Dprms mod 2 eq 1 :
       "Argument 1 must be the product of an odd number of primes.";
    return 1 + &+[ &*[ Integers() | 1 + Valuation(M,p) : p in Nprms ] * 
        DimensionNewCuspFormsGamma0(D*(N div M),2) : M in Divisors(N) ];
end intrinsic;
