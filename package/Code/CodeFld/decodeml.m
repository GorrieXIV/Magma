freeze;

// Decoder for binary code by majority logic 
// 				Lanclelot Pecquet, 1996


intrinsic MaxOrthPCheck(C::CodeLinFld) -> []
{Return a maximal set of equations orthogonal for each position}
	F := Alphabet(C);
	n := Length(C);
	W := RSpace(F,n);
	k := Dimension(C);
	Hoj := [];
	Z := IntegerRing();
	V := RSpace(Z,n);
	C0 := Dual(C);
	for j in [1 .. n] do                    // For each position:
		SCr := {{V!c} : c in C0 | c[j] eq 1};
		if (#SCr gt 0) then
			SCrp1 := {};
			Cr := SetToSequence(SCr);
			Crp1 := [];
			tseq := [1 .. j-1] cat [j+1 .. n];
			for l in [2 .. n-k] do          // For all nb of eq:
				for s in [1 .. #Cr] do
					for t in [s+1 .. #Cr] do
						S := Cr[s] join Cr[t];
						if (#S eq l) then
							v := &+[c : c in S];
							rep := true;
							for t in tseq do
								if (v[t] gt 1) then
									rep := false;
									break;
								end if;
							end for;
							if (rep eq true) then
								SCrp1 join:= {S};
								end if;
							end if;
						end for;
					end for;
					if (#SCrp1 eq 0) then
						break;
					else
						SCr := SCrp1;
						Cr := SetToSequence(SCr);
						SCrp1 := {};
					end if;
				end for;
				M := ChangeUniverse(SetToSequence(Random(Cr)),W);
				Append(~Hoj,M);
			else
				Append(~Hoj,[W!0]);
			end if;
		end for;
		return Hoj;
end intrinsic;


intrinsic DecodeML(C::CodeLinFld,S::[ModTupFldElt]) -> [],[]
{Decoder for binary codes. Given a list of received vectors, return a two 
sequences. The second contains the corrected vectors, the first, boolean values
saying if the decoder could retrieve the original codeword}
	F := Alphabet(C);
	require (#F eq 2):"Argument 1 should be binary";
	N := #S;
	require N ge 1: "Argument 2 should contain at least one codeword";
	n := Length(C);
	k := Dimension(C);
	d := MinimumWeight(C);
	dm1o2 := (d-1) div 2;
	nmk := n-k;

	L := MaxOrthPCheck(C);

	V := RSpace(F,n);
	Correct := [];
	CHECK := [];

	for i in [1 .. N] do
		v := S[i];
		e := V!0;
		for j in [1 .. n] do
			Lj := L[j];
			NbOfEq := #Lj;
			LL := [ElementToSequence(Lj[i]) 
			: i in [1 .. NbOfEq]];
			Hoj := RMatrixSpace(F,NbOfEq,n)!&cat(LL);
			E := v*Transpose(Hoj);
			// Test for majority:
			if (Weight(E) gt NbOfEq div 2) then // error
				e[j] := F!1;
			end if;
		end for;
		c := v+e; 
		Append(~Correct,c);
		if ((Weight(e) le dm1o2) and (c in C)) then
			CHECK[i] := true;
		else
			CHECK[i] := false;
		end if;
	end for;
	return CHECK,Correct;
end intrinsic;


