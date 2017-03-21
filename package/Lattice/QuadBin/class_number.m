////////////////////////////////////////////////////////////////////
//                                                                //
//                         CLASS NUMBERS                          //
//                    OF BINARY QUADRATIC FORMS                   //
//                          David Kohel                           //
//                    Last modified April 2000                    //
//                                                                //
////////////////////////////////////////////////////////////////////

freeze;

// Intrinsics: BinaryQuadraticForms, ClassNumber,
// Conductor, ElementToSequence. 

forward NFCofactor, NUnits, ProjOrderMod;
 
function FundDiscCond(D)
    // Require: D mod 4 in {0,1}; 
    DK := FundamentalDiscriminant(D);
    return DK, Isqrt(D div DK);
end function;

////////////////////////////////////////////////////////////////////
//                                                                //
//                 Nonfundamental Class Number                    //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic ClassNumber(D::RngIntElt : FactorBasisBound := 0.1,
    ProofBound := 6.0, ExtraRelations := 1, Al := "Automatic") -> RngIntElt
    {The class number of the binary quadratic forms of discriminant D.}  

    if D eq 1 then
      return 1;
    end if;

    require D mod 4 in {0,1} :
       "Argument must be congruent to 0 or 1 mod 4.";
    require ISA(Type(FactorBasisBound), FldReElt) : 
				"FactorBasisBound must be a FldReElt";
    require ISA(Type(ProofBound), FldReElt) : 
				"ProofBound must be a FldReElt";
    require ISA(Type(ExtraRelations), RngIntElt) : 
				"ExtraRelations must be a RngIntElt";

    require Al in {"Automatic", "ReducedForms", "Relations", "Shanks", "Sieve", "NoSieve"}: 
        "Al must be one of Automatic, ReducedForms, Relations, Shanks, Sieve or NoSieve";

    DK, m := FundDiscCond(D);
    if DK lt 0 and -10^6 lt DK then
	return NFCofactor(DK,m) * #ReducedForms(DK);
    end if;
    return NFCofactor(DK,m)*
        FundamentalClassNumber(QuadraticForms(DK) :
            FactorBasisBound := FactorBasisBound,
	    ProofBound := ProofBound,
	    ExtraRelations := ExtraRelations, Al := Al);
end intrinsic;

intrinsic ClassNumber(Q::QuadBin : FactorBasisBound := 0.1,
    ProofBound := 6.0, ExtraRelations := 1, Al := "Automatic") -> RngIntElt
    {The number of the binary quadratic form classes in Q.}  
    require ISA(Type(FactorBasisBound), FldReElt) : 
	"FactorBasisBound must be a FldReElt";
    require ISA(Type(ProofBound), FldReElt) : 
	"ProofBound must be a FldReElt";
    require ISA(Type(ExtraRelations), RngIntElt) : 
	"ExtraRelations must be a RngIntElt";
    require Al in {"Automatic", "ReducedForms", "Relations", "Shanks", "Sieve", "NoSieve"}: 
        "Al must be one of Automatic, ReducedForms, Relations, Shanks, Sieve or NoSieve";

    DK, m := FundDiscCond(Discriminant(Q));
    if DK lt 0 and -10^6 lt DK then
	return NFCofactor(DK,m) * #ReducedForms(DK);
    end if;
    return NFCofactor(DK,m)*
        FundamentalClassNumber(QuadraticForms(DK) :
            FactorBasisBound := FactorBasisBound,
            ProofBound := ProofBound,
            ExtraRelations := ExtraRelations, Al := Al);
end intrinsic;

intrinsic PicardNumber(R::RngQuad : FactorBasisBound := 0.1,
    ProofBound := 6.0, ExtraRelations := 1, Al := "Automatic") -> RngIntElt
    {The ideal class number of R.}  
    require ISA(Type(FactorBasisBound), FldReElt) : 
				"FactorBasisBound must be a FldReElt";
    require ISA(Type(ProofBound), FldReElt) : 
				"ProofBound must be a FldReElt";
    require ISA(Type(ExtraRelations), RngIntElt) : 
				"ExtraRelations must be a RngIntElt";
    require Al in {"Automatic", "ReducedForms", "Relations", "Shanks", "Sieve", "NoSieve"}: 
        "Al must be one of Automatic, ReducedForms, Relations, Shanks, Sieve or NoSieve";
    DK, m := FundDiscCond(Discriminant(R));
    if DK lt 0 and -10^6 lt DK then
	return NFCofactor(DK,m) * #ReducedForms(DK);
    end if;
    return NFCofactor(DK,m)*
        FundamentalClassNumber(QuadraticForms(DK) :
	    FactorBasisBound := FactorBasisBound,
	    ProofBound := ProofBound,
	    ExtraRelations := ExtraRelations, Al := Al);
end intrinsic;

function NFCofactor(DK,m)
    error if (DK mod 4) notin {0,1},
       "Error: Argument 1 not congruent to 0 or 1 mod 4."; 
    if m eq 1 then return 1; end if;
    if DK lt 0 then 
        eR := NUnits(DK) div NUnits(m^2*DK);  
    else 
        R := MaximalOrder(QuadraticField(DK));
        e := FundamentalUnit(R);
        w := Basis(R)[2];
        M := MatrixAlgebra(Integers(),2)!&cat[Eltseq(e),Eltseq(e*w)];
        eR := ProjOrderMod(M,m); 
    end if; 
    cf := &*[ p[1]^p[2] - KroneckerSymbol(DK,p[1])*p[1]^(p[2]-1)  
   	     : p in Factorization(m) ]; 
    return cf div eR;
end function;
 
function NUnits(D)
    case D: 
	when -3: return 6;
	when -4: return 4;
        else return 2;
    end case;
end function;

function ProjOrderMod(M,m)
    ppow, p, r := IsPrimePower(m); 
    if ppow then 
	S := ResidueClassRing(m);
	m0 := ProjectiveOrder(MatrixAlgebra(GF(p),2)!M);
	M0 := (MatrixAlgebra(S,2)!M)^m0;
	if p eq 2 and (M0[1,2] ne 0 or M0[2,1] ne 0) then
	    m0 := p*m0; 
	    M0 := M0^p; 
	end if; 
	if M0[1,2] eq 0 and M0[2,1] eq 0 then       
	    return m0; 
	else 
	    k := Min([ Valuation(Integers()!x,p) 
		   : x in [ M0[1,2], M0[2,1] ] | x ne 0 ]);   
        end if;
	M1 := (MatrixAlgebra(S,2)!M)^((m0*p^(r-k)) div p);
	assert M1[2,1] ne 0 or M1[1,2] ne 0;
	return m0*p^(r-k);
    end if; 
    Q := Factorization(m); 
    return LCM([ ProjOrderMod(M,p[1]^p[2]) : p in Q ]); 
end function;

