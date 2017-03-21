freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../derlie.m":ExtendHInDerL;
import "../stsa.m":DR_IsSTSA;

/*
Tries to identify L, H:
- L is assumed to be the simple constituent of the Lie algebra of a simple alg. gp
- H is assumed to be a split maximal toral subalgebra

In this file we only handle those cases where the full Lie algebra of the simple 
  alg. gp is *non-simple*; in all other cases we can use identify_liealgebra_of_simple_group.
Therefore, the field is assumed to be finite.
*/

extend_and_identify := function(L,H,d,R : Twist := false)
	/* 
	 - ExtendHInDerL is called on L and H, yielding LL,
	 - Attempt to add "d" dimensions (d will often be 1)
	 - Extend the MTSA H into the new, bigger Lie algebra
	 - Attempt to identify L', H' as R.
	
	return false on failure; otherwise:
	 - R   : The root datum it has been identified as
	 - CBD : The ChevBasData object that is the proof
	 - LL  : The bigger Lie algebra
	 - LLL : The Lie algebra of type R inside LL (possibly equal to LL)
	 - HHH : MTSA of LLL
	 - maps: The record of maps sending L to LL and vice versa
	*/
	
	local dimL, LL, maps, HinLL, HH, LLL, HHH, CBD, e,
		LLLFF, HHHFF, Rt;

	vprintf ChevBas, 2: "[E&I] Started with Dim(H) = %o, Dim(L) = %o, d = %o, R = %o, twist = %o\n", Dimension(H), Dimension(L), d, R, Twist;
	
	dimL := Dimension(L);
	if not DR_IsSTSA(L,H) then 
		error "extend_and_identify: H is not a MTSA of L";
	end if;
	
	//Extend the Lie algebra
	LL,maps := ExtendHInDerL(L,H);
	vprintf ChevBas, 2: "[E&I] Dim(LL) = %o\n", Dimension(LL);
	if Dimension(LL) lt dimL+d then
		vprintf ChevBas, 2: "[E&I] FAIL: Was hoping for %o extra.\n", d;
		return false, _, _, _, _, _;
	end if;

	//Try to extend MTSA, in several ways.
	HinLL := sub<LL | [ (maps`mp_L_to_LL)(L!b) : b in Basis(H) ]>;
	HH := Centraliser(LL, HinLL);
	vprintf ChevBas, 2: "[E&I] Dim(H) = %o, d = %o, Dim(HH) = %o\n", Dimension(H), d, Dimension(HH);
	if Twist cmpne false then
		//Twisted case
		if Dimension(LL) ne Dimension(L) + d then
			vprintf ChevBas, 2: "[E&I] Twist = %o, Dimension(LL) = %o, Dimension(L) = %o, d = %o, this won't work.\n", Twist, Dimension(LL), Dimension(L), d;
		end if;
		vprintf ChevBas, 2: "[E&I] Twist = %o, happy so far, extending HH as far as we can.\n", Twist;
		try
			HH := SplitToralSubalgebra(LL : H0 := HinLL);
		catch err
			HH := HinLL;
		end try;
		vprintf ChevBas, 2: "[E&I] -> Dim(HH) = %o. Continuing.\n", Dimension(HH);
	elif Dimension(HH) eq Dimension(H) + d then
		//We are quite happy, but...
		if not DR_IsSTSA(LL, HH) then
			vprintf ChevBas, 2: "[E&I] FAIL: not IsSTSA(LL, HH)\n";
			return false, _, _, _, _, _;
		end if;
	else
		//We have to go through more elaborate stuff to extend SCSA
		vprintf ChevBas, 2: "[E&I] Calling findMTSAChar2...\n";
		HH := SplitToralSubalgebra(LL : H0 := HinLL);
		vprintf ChevBas, 2: "[E&I] -> Dim(HH) = %o\n", Dimension(HH);

		if Dimension(HH) ne Dimension(H) + d then
			vprintf ChevBas, 2: "[E&I] FAIL: Was hoping for %o + %o\n", Dimension(H), d;
			return false, _, _, _, _, _;
		end if;
	end if;

	if Dimension(LL) ne Dimension(L) + d then
		LLL := sub<LL | [ (maps`mp_L_to_LL)(L!b) : b in Basis(L) ], HH>;
		HHH := LLL meet HH;
		vprintf ChevBas, 2: "[E&I] OK: Dim(LLL) = %o (of Dim(LL) = %o), Dim(HHH) = %o (of Dim(LL) = %o)\n", Dimension(LLL), Dimension(LL), Dimension(HHH), Dimension(HH);
	else
		LLL := LL;
		HHH := HH;
		vprintf ChevBas, 2: "[E&I] OK: LLL = LL (%o-dim), HHH = HH (%o-dim)\n", Dimension(LLL), Dimension(HHH);
	end if;
	assert DR_IsSTSA(LLL, HHH);
	
	//Great! Now try and do the identification...
	try
		if Twist cmpeq false then
			_,_,_,CBD := ChevalleyBasis(LLL, HHH, R);
			vprintf ChevBas, 2: "[E&I] OK: chevbasis succeeded!\n";
			vprintf ChevBas, 2: "[E&I] DONE: L is the simple part of a Lie algebra of type %o.\n", CartanName(R) ;
		
			retformat := recformat< R:RootDtm, LL:AlgLie, LLL:AlgLie, HHH:AlgLie, ChevBasData:Rec, maps:Rec>;
			return CBD`R, rec<retformat| R := CBD`R, ChevBasData := CBD, LL := LL, LLL := LLL, HHH := HHH, maps := maps>;
		else
			Rt := TwistedRootDatum(R : Twist := Twist);
			LLLFF, phiLLLFF, CBD, Fhave := TwistedBasis(LLL, HHH, Rt);
			vprintf ChevBas, 2: "[E&I] OK: TwistedBasis succeeded!\n";
			vprintf ChevBas, 2: "[E&I] DONE: L is the simple part of a twisted Lie algebra of type %o%o.\n", Twist, CartanName(R);

			retformat := recformat< R:RootDtm, LL:AlgLie, LLL:AlgLie, HHH:AlgLie, LLLFF:AlgLie, phiLLLFF:Map, ChevBasData:Rec, maps:Rec, Fhave:AlgMatElt>;
			return Rt, rec<retformat| R := Rt, LL := LL, LLL := LLL, HHH := HHH, LLLFF := LLLFF, phiLLLFF := phiLLLFF, ChevBasData := CBD, maps := maps, Fhave := Fhave>;
		end if;
	catch e
		vprintf ChevBas, 2: "[E&I] FAIL: Identification failed.\n";
		print e;
		return false, _, _, _, _, _;
	end try;
end function;
	
function identify_simple_liealg(L, H : Select := "All", hintR := false) //-> SeqEnum, FldReElt
/* Identify a simple Lie algebra; but here only those cases where the full Lie algebra of the simple 
  alg. gp is non-simple are handled. In all other cases we can use identify_liealgebra_of_simple_group.

Select can be "All" (returns all hits), "CartanType" (return only one hit for each Cartan type), 
  or "First" (return as soon as the first hit is found).

 Returns a sequence Q of hits, each element q of Q is a record:
 - q`R    : The corresponding root datum
 - q`str  : A string describing the hit
 - in q`extra:
    - CBD  : The ChevBasData object that is the proof
    - LL   : The bigger Lie algebra
    - LLL  : The Lie algebra of type R inside LL (possibly equal to LL)
    - HHH  : MTSA of LLL
    - maps : The record of maps sending L to LL and vice versa
 - in q`extra, if R is twisted, additionally:
    - LLLFF: LLL over a field extension
    - HHHFF: HHH over a field extension

Second return value is Cputime of first hit.

if hintR is given and simply a split or twisted root datum, we return immediately (since that
means L is of type R and that case is not for us)
*/
	local b, p, d, r, rr, eicands, e, t,
		R, CBD, LL, LLL, HHH, maps,
		ret, RF, tfirst,
		twist, str, ROK, err, stop;

	vprintf ChevBas, 2: "[ISL] Started. L = %o-dim, H = %o-dim.\n", Dimension(L), Dimension(H);
	if not IsFinite(BaseRing(L)) then
		vprintf ChevBas, 2: "[ISL] L not over finite field.\n";
		return [], Cputime();
	end if;
	if (hintR cmpne false) and (ISA(Type(hintR), RootDtm)) then
		vprintf ChevBas, 2: "[ISL] hintR != false.\n";
		return [], Cputime();
	end if;		
	assert DR_IsSTSA(L,H);
	
	p := Characteristic(BaseRing(L));
	d := Dimension(L);
	r := Dimension(H);
	ret := [];
	tfirst := false;
	
	//Candidates for the E&I algorithm
	eicands := [* *];
	if (d eq (r+2)^2-2) and ((r+2) mod p) eq 0 and (r ge 1) then
		//A_n, with p|n+1
		Append(~eicands, <1, RootDatum(Sprintf("A%o", r+1))>);
	end if;
	if (p eq 3) and (r eq 5) and (d eq 77) then
		//E_6, char. 3
		Append(~eicands, <1, RootDatum("E6")>);
	end if;
	if (p eq 2) and (r+2 ge 4) and (r mod 2 eq 0) and (d eq 2*(r+2)^2 - (r+2) - 2) then
		//D_n, char. 2, n even
		Append(~eicands, <2, RootDatum(Sprintf("D%o", r+2))>);
	end if;
	if (p eq 2) and (r+1 ge 4) and (r mod 2 eq 0) and (d eq 2*(r+1)^2 - (r+1) - 1) then
		//D_n, char. 2, n odd
		Append(~eicands, <1, RootDatum(Sprintf("D%o", r+1))>);
	end if;
	if (p eq 2) and (r eq 6) and (d eq 132) then
		//E_7, char. 2
		Append(~eicands, <1, RootDatum("E7")>);
	end if;
	
	//Additional, twisted, candidates.	
	b,rr := IsSquare(d+2);
	if b and (rr mod p) eq 0 then
		//2A_n, with p|n+1
		Append(~eicands, <1, RootDatum(Sprintf("A%o", rr-1)), 2>);
	end if;
	if (p eq 3) and (r eq 4) and (d eq 77) then
		//E_6, char. 3
		Append(~eicands, <1, RootDatum("E6"), 2>);
	end if;
	
	//Run the E&I algorithm; in char. 2 we run it a few times because bad luck may occur wrt the torus
	RF := recformat< str : MonStgElt, R : RootDtm, L:AlgLie, H:AlgLie, extra : Rec >;
	for e in eicands do
		d := e[1]; R := e[2]; twist := (#e le 2) select false else e[3];
		vprintf ChevBas, 2: "[ISL] Guessing %o%o...\n", (twist cmpeq false) select "" else twist, CartanName(R);
		for t in [1..(p eq 2 select 5 else 1)] do
			stop := false;
			try
				ROK, extra := extend_and_identify(L, H, d, R : Twist := twist);
				if ROK cmpne false then
					//Success!
					str := Sprintf("The %o-dim simple constituent of a %oLie algebra of type %o%o", 
						Dimension(L),
						(twist cmpeq false select "" else "twisted "),
						(twist cmpeq false select "" else twist),
						CartanName(ROK)
					);
					Append(~ret, rec< RF | 
						str := str,
						L := L, H := H,
						R := ROK,
						extra := extra>);
					if tfirst cmpeq false then tfirst := Cputime(); end if;
					if Select eq "First" then return ret, tfirst; end if;
					stop := true;
				end if;
			catch err
				ROK := false;
				vprintf ChevBas, 2: "[ISL] Error in extend_and_identify ?\n%o\n", err;
			end try;
			
			if stop then break t; end if;
		end for;
	end for;
	
	return ret, tfirst;
end function;
