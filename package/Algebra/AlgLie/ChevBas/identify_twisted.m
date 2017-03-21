freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "identify_liealg_of_simp_grp.m": all_isogs;
import "identify.m":nice_fullname_irred_rootdtm;

function identify_twisted(L, H  : Select := "All", hintR := false) //-> SeqEnum, FldReElt
/* Tries to identify L as a twisted Lie algebra. 
  H should be a split toral subalgebra of L.
  Select may be either "First" or "All".

  Returns a sequence of matches, second is Cputime of first hit.
*/
	local b, k, ret, tfirst,
		dimH, dimL, opts, o,
		isogs, i,
		LFF, HFF, CBD, Frob, Rnm, R;

	if not IsFinite(BaseRing(L)) then
		vprintf ChevBas, 2: "[IDTw] L not over finite field.\n";
		return [], Cputime();
	end if;
	if (hintR cmpne false) and (not IsTwisted(hintR)) then 
		vprintf ChevBas, 2: "[ILSG] hintR is not twisted. Returning.\n";
		return [], _; 
	end if;
	
	tfirst := false;
	dimL := Dimension(L);
	dimH := Dimension(H);
	vprintf ChevBas, 2: "[IDTw] dimL = %o, dimH = %o\n", dimL, dimH;
	
	//We do slightly sloppy things here since SplittingCartanSubalgebra 
	//  occasionally returns something that is not quite right, dimension wise.
	//These are the options marked "SCSA bug"
	if (hintR cmpne false) and ISA(Type(hintR), RootDtm) and IsTwisted(hintR) then
		assert IsIrreducible(hintR);
		CN := CartanName(hintR);
		assert CN[#CN] ne " ";
		opts := [<CartanName(hintR), TwistingDegree(hintR)>];
	else
		opts := [];
	
		//An
		b,k := IsSquare(dimL+1);
		if b then Append(~opts, <Sprintf("A%o", k-1), 2>); end if;

		//Dn
		k := 1;
		while dimL gt 2*k^2 - k do k +:= 1; end while;
		if dimL eq 2*k^2 - k then Append(~opts, <Sprintf("D%o", k), 2>); end if;

		//3D4, OK & SCSA bug
		if dimL eq 28 then Append(~opts, <"D4", 3>); end if;
	
		//2E6, OK & SCSA bug
		if dimL eq 78 then Append(~opts, <"E6", 2>); end if;
	end if;
	
	vprintf ChevBas, 2: "[IDTw] opts = %o\n", opts;

	ret := [];
	retformat := recformat< str:MonStgElt, R : RootDtm, twist : RngIntElt, LFF: AlgLie, phi:Map, ChevBasData:Rec, Frob:AlgMatElt>;
	for o in opts do
		isogs := all_isogs(o[1]);
		for R in isogs do
			Rnm := nice_fullname_irred_rootdtm(R);
			vprintf ChevBas, 2: "[IDtw] Trying %o%o ...\n", o[2], Rnm;
			try
				Rt := TwistedRootDatum(R : Twist := o[2]);
				LFF, phi, CBD, Frob := TwistedBasis(L, H, Rt);
				vprintf ChevBas, 2: "[IDtw] %o%o matches!\n", o[2], Rnm;
				Append(~ret, rec<retformat | 
					str := Sprintf("Twisted Lie algebra of type %o%o", o[2], Rnm),
					R := Rt,
					twist := o[2],
					LFF := LFF,
					phi := phi,
					ChevBasData := CBD,
					Frob := Frob
				>);
				if #ret eq 1 then tfirst := Cputime(); end if;
				if Select eq "First" then return ret, tfirst; end if;
			catch e
				vprintf ChevBas, 2: "[IDtw] %o%o does not match.\n", o[2], Rnm;
			end try;
		end for;
	end for;

	//Done :)
	return ret, tfirst;
end function;	
