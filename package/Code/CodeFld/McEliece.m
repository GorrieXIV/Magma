freeze;

//these functions choose the right combinations for McElice attacks


intrinsic McEliecesAttack(C::Code, v::ModTupFldElt, e::RngIntElt
		    : MaxTime := 0, DirectEnumeration := false) -> ModTupFldElt
{Using McEliece's original attack on the McEliece cryptosystem, attempt
to enumerate a vector of weight e from the error coset v + C. };

    return DecodingAttack(C, v, e : MatrixSequence := "Random",
				    Enumeration := "Standard",
				    p := 0,
				    DirectEnumeration := DirectEnumeration,
				    MaxTime := MaxTime); 
end intrinsic;

intrinsic LeeBrickellsAttack(C::Code, v::ModTupFldElt, e::RngIntElt,
		    p::RngIntElt
		    : MaxTime := 0, DirectEnumeration := false) -> ModTupFldElt
{Using Lee and Bickell's attack on the McEliece cryptosystem, attempt
to enumerate a vector of weight e from the error coset v + C. };

    return DecodingAttack(C, v, e : MatrixSequence := "Random",
				    Enumeration := "Standard",
				    p := p,
				    DirectEnumeration := DirectEnumeration,
				    MaxTime := MaxTime); 
end intrinsic;

intrinsic LeonsAttack(C::Code, v::ModTupFldElt, e::RngIntElt, 
		    p::RngIntElt, l::RngIntElt
		    : MaxTime := 0, DirectEnumeration := false) -> ModTupFldElt
{Using Leon's attack on the McEliece cryptosystem, attempt
to enumerate a vector of weight e from the error coset v + C. };

    return DecodingAttack(C, v, e : MatrixSequence := "Random",
				    Enumeration := "Leon",
				    p := p,
				    l := l,
				    DirectEnumeration := DirectEnumeration,
				    MaxTime := MaxTime); 
end intrinsic;



intrinsic SternsAttack(C::Code, v::ModTupFldElt, e::RngIntElt, 
		    p::RngIntElt, l::RngIntElt 
		    : MaxTime := 0, DirectEnumeration := false) -> ModTupFldElt
{Using Stern's attack on the McEliece cryptosystem, attempt
to enumerate a vector of weight e from the error coset v + C. };

    return DecodingAttack(C, v, e : MatrixSequence := "Random",
				    Enumeration := "HashTable",
				    p := p,
				    l := l,
				    DirectEnumeration := DirectEnumeration,
				    MaxTime := MaxTime); 
end intrinsic;


intrinsic CanteautChabaudsAttack(C::Code, v::ModTupFldElt, e::RngIntElt, 
		    p::RngIntElt, l::RngIntElt 
		    : MaxTime := 0, DirectEnumeration := false) -> ModTupFldElt
{Using Canteaut and Chabaud's attack on the McEliece cryptosystem, attempt
to enumerate a vector of weight e from the error coset v + C. };

    return DecodingAttack(C, v, e : MatrixSequence := "Stepped",
				    NumSteps := 1,
				    Enumeration := "Leon",
				    p := p,
				    l := l,
				    DirectEnumeration := DirectEnumeration,
				    MaxTime := MaxTime); 
end intrinsic;
