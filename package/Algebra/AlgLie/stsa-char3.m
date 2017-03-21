freeze;

/* 
 * Dan Roozemond, 2010. 
 * Update June, 2011
 */

import "quo_with_pullback.m":quo_with_pullback;
import "stsa.m":DR_IsSTSA;

pullback_to_L := function(L, pbs, Ms, x)
	local i, r;
	assert #Ms eq #pbs + 1;
	r := sub<Ms[#Ms]|x>;
	for i in [#pbs..1 by -1] do
		r := sub<Ms[i] | [ (pbs[i])(Ms[i+1]!b) : b in Basis(r) ]>;
	end for;
	return r;
end function;

findSTSACharNot2_actual := function(L : StartH := false)
	local F, M, pbs, Ms, Hs, 
		HinL, done, c, h, adh, ev, t,
		S1, S2, HinM;
	
	F := BaseRing(L);
	assert Characteristic(F) ne 2; //Not for characteristic 2.
	assert IsFinite(F);

	M := L;
	pbs := [ ];
	Ms := [ L ];
	Hs := [];
	
	if StartH cmpne false then
		//We start with this split toral subalgebra
		if not DR_IsSTSA(M, StartH) then
			error "findSTSAChar3: StartH is not a split toral subalgebra of L";
		end if;
		
		Append(~Hs, StartH);
		CMH := Centraliser(M, StartH);
		if Dimension(CMH) ne 0 then
			M,_,_,pb := quo_with_pullback(CMH, StartH);
			Append(~Ms, M);
			Append(~pbs, pb);
		end if;	
	end if;
	
	c := 0;
	while Dimension(M) gt 0 do
	
		vprintf STSA, 1: "[STSAc3] M = %o\n", M;
		adM := AdjointRepresentation(M : ComputePreImage := false);
	
		if Dimension(M*M) eq 0 then
			HinL := pullback_to_L(L, pbs, Ms, M);
			if DR_IsSTSA(L, HinL) then
				vprintf STSA, 2:  "[STSAc3]   [M,M] = 0 and M is split in L\n";
				//Found a split thing.
				Append(~Hs, HinL);
				break;
			end if;	
		end if;	
	
		done := false;
		while not done do
			//Anti-inf. loop
			c +:= 1; if c gt 100 then 
				vprintf STSA, 1 : "[STSAc3] STOP -- Infinite loop. Returning as far as I got.\n"; 
				return sub<L | Hs>;
			end if;
		
			h := Random(M);
			adh := Matrix(adM(h));
	
			ev := { i[1] : i in Eigenvalues(adh) };
			for t in ev do
				if -t notin ev then continue; end if;
		
				S1 := sub<M | [ M!b : b in Basis(Eigenspace(adh, t)) ]>;
				S2 := sub<M | [ M!b : b in Basis(Eigenspace(adh, -t)) ]>;
				HinM := sub<M | Random(S1)*Random(S2)>;
				vprintf STSA, 2:  "  dim(HinM) = %o\n", Dimension(HinM);
				if Dimension(HinM) eq 0 then continue; end if;
			
				if DR_IsSTSA(M, HinM) then 
					vprintf STSA, 3:  "[STSAc3]   split in M\n";
				else
					vprintf STSA, 3:  "[STSAc3]   not split in M\n";
					continue;
				end if;
		
				HinL := pullback_to_L(L, pbs, Ms, HinM);
				if DR_IsSTSA(L, HinL) then
					vprintf STSA, 3:  "[STSAc3]   split in L\n";
				else
					vprintf STSA, 3:  "[STSAc3]   not split in L\n";
					continue;
				end if;			

				done := true;
				break t;
			end for;
		end while;
	
		//Found a split thing -- continue somewhere else
		Append(~Hs, HinL);
		CMH := Centraliser(M, HinM);
		if Dimension(CMH) eq 0 then
			vprintf STSA, 1:  "[STSAc3] Dimension(Centraliser(M, HinM)) = 0\n";
			break;
		else
			M,_,_,pb := quo_with_pullback(CMH, HinM);
			Append(~Ms, M);
			Append(~pbs, pb);
		end if;
	end while;
	
	return sub<L | Hs>;
end function;


findSTSACharNot2 := function(L : StartH := false, MaxTries := 10, TryMaximal := true)
	//We try to find a split toral subalgebra of the reductive rank; if 
	//  we don't succeed after MaxTries attempts we just return the 
	//  biggest we've found.
	assert Characteristic(BaseRing(L)) notin {0,2}; //Not for characteristic 2.

	if Type(TryMaximal) eq RngIntElt then
		error if TryMaximal le 0, "TryMaximal as integer should be positive.";
		aim := TryMaximal;
	elif TryMaximal cmpeq true then
		vprintf STSA, 2:  "[STSAc3] Computing reductive rank...\n";
		aim := ReductiveRank(L : Check := false);
	else
		aim := 1;
	end if;
	mx := -1; fndH := false;
	
	for i in [1..MaxTries] do
		H := findSTSACharNot2_actual(L : StartH := StartH);
		dimH := Dimension(H);
		if dimH ge aim then return H; end if;
		if dimH gt mx then fndH := H; end if;
	end for;
	
	return fndH;

end function;