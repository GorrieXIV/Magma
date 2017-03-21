freeze;

// Simplex codes		Lancelot Pecquet, 1996

intrinsic SimplexCode(r::RngIntElt) -> Code
{Return the [2^r-1,r,2^(r-1)] binary simplex code}
	requirege r,1;
	C := Dual(HammingCode(GF(2),r));
	AssertAttribute(C,"MinimumWeight",2^(r-1));
	return C; 
end intrinsic;
