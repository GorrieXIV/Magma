freeze;

import "RootDatumDan.m": myComponents;

function AlternatingDominant_Simple( lrd ) //-> LieRepDec
/* Alternating Dominant (from LiE; see page 68 of the LiE Manual), 
   R is simple */
    R := RootDatum(lrd);
	s := Rank(R);

	wts, mps := Explode(lrd`WtsMps);
	rtact := RootAction(CoxeterGroup(R));
	reflprms := ReflectionPermutations(R);

	for j in [1..#wts] do
		i := 1; n := 0;
		while (true) do
			//find negative entry
			while (i le s) do
				if (wts[j][i] lt 0) then break; end if;
				i +:= 1;
			end while;

			if (i le s) then
				//negative entry found
				if (wts[j][i] eq -1) then
					mps[j] := 0; 
					break; 
				end if;

				wts[j][i] +:= 1;

				//reflect, count, and shift back
				wts[j] := rtact(wts[j], reflprms[i]);
				wts[j][i] -:= 1;
				n +:= 1; 

				//go back to the first entry that might be negative
				if (i le 2) then i := 1; else i -:= 2; end if;
			else
				//no negative entry found
				break;
			end if;

		end while;

		if (IsOdd(n)) then mps[j] *:= -1; end if;
	end for;

    return LieRepresentationDecomposition(R, wts, mps);
end function;


intrinsic AlternatingDominant( R::RootDtm, wt::ModTupRngElt ) -> LieRepDec
{ Alternating Dominant (from LiE; see page 68 of the LiE Manual) }
	return AlternatingDominant( LieRepresentationDecomposition(R, wt) );
end intrinsic;

intrinsic AlternatingDominant( R::RootDtm, wt::SeqEnum ) -> LieRepDec
{ " }
	return AlternatingDominant( LieRepresentationDecomposition(R, wt) );
end intrinsic;

intrinsic AlternatingDominant( D::LieRepDec ) -> LieRepDec
{ Alternating Dominant (from LiE; see page 68 of the LiE Manual) }
    R := RootDatum(D);
	comps, pi := myComponents(R);
	if (#comps) eq 1 then
		return AlternatingDominant_Simple( D );
	end if;

	for comp in comps do
	    Dsub := SubWeights(D, comp[2], comps[1]);
		if (comp[1] cmpeq "T") then
			Dtmp := Dsub;
		else
			Dtmp := AlternatingDominant_Simple( Dsub );
		end if;
		
		if assigned DRet then
		    DRet := DRet*Dtmp;
		else
		    DRet := Dtmp;
		end if;
	end for;

	return PermuteWeights(DRet, pi^-1, R);
end intrinsic;







procedure AlternatingDominant_Loop( ~n, ~c_pos, ~m_pos, ~c, ~m, ~k
		  : PosCoeffs := [CartesianProduct(Integers(), Integers()) | ] )
/* This should implement: 
	#define loop(body)  while (n-->0) 
	\{ if (b= *(c++),(d= *(v=(*(m++))+k)+1)<0) \{ b->size= -b->size; body; *v= -1-d; \}\}

	With the additional assumption that body is of the form:
		v[PosCoeffs[1][1]]+=PosCoeffs[1][2]*d; 
		v[PosCoeffs[2][1]]+=PosCoeffs[2][2]*d;
		...
		(see altdom.c in LiE)
*/
														// c-equiv
	while (n gt 0) do									//
		n -:= 1;										// while (n-->0)
		d := m[m_pos + 1][k+1] + 1;						// d = *(v=(*(m++))+k)+1
		if (d lt 0) then								// if (b= *(c++),(d= *(v=(*(m++))+k)+1)<0)
			c[c_pos + 1] *:= -1;						// b->size = -b->size
			for pc in PosCoeffs do						// 
				m[m_pos + 1][k+1+pc[1]] +:= (pc[2])*d;	//   BODY
			end for;									// 
			m[m_pos + 1][k+1] := -1 - d;				// *v = -1-d
		end if;
		c_pos +:= 1;									// c++
		m_pos +:= 1;									// m++
	end while;
end procedure;

function AlternatingReflections_Simple( R, D, offset, i ) //-> LieRepDec
	LieType := CartanName(R)[1];
	r := Rank(R);
	m, c := Explode(D`WtsMps);
	m_pos := 0; c_pos := 0;
	k := offset + i;

	n := #m;
	to_remove := [ j : j in [n..1 by -1] | m[j][k+1] eq -1 ];
	for j in to_remove do Remove(~m, j); Remove(~c, j); end for;
	n -:= #to_remove;	

	case LieType:
		when "A":
			if   (i gt 0 and i lt r-1)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1> , <1, 1> ]);
			elif (i eq 0 and r eq 1)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ ]);
			elif (i eq 0 and r ne 1)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <1,1> ]);
			else						AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1,1> ]);
			end if;
		when "B":
			if	 (i gt 0 and i lt r-2)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1> , <1, 1> ]);
			elif (i eq 0 and r eq 2)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <1, 2> ]);
			elif (i eq 0 and r ne 2)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <1, 1> ]);
			elif (i eq r-1)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1> ]);
			else						AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1>, <1, 2> ]);
			end if;
		when "C":
			if   (i gt 0 and i lt r-1)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1> , <1, 1> ]);
			elif (i eq 0)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <1, 1> ]);
			else						AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 2> ]);
			end if;
		when "D":
			if   (i gt 0 and i lt r-3)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1> , <1, 1> ]);
			elif (i eq 0 and r eq 3)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <1, 1>, <2, 1> ]);
			elif (i eq 0 and r ne 3)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <1, 1> ]);
			elif (i eq r-3)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1> , <1, 1>, <2, 1> ]);
			else						AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <r-3-i, 1> ]);
			end if;
		when "E":
			if   (i gt 3 and i lt r-1)	then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1>, <1, 1> ]);
			elif (i eq r-1)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1, 1> ]);
			elif (i lt 2)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <2, 1> ]);
			elif (i eq 2)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-2,1>, <1,1> ]);
			else				AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-2,1>, <-1,1>, <1,1> ]);
			end if;
		when "F":
			if   (i eq 0)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <1,1>]);
			elif (i eq 1)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1,1>,<1,2>]);
			elif (i eq 2)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1,1>,<1,1> ]);
			else						AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1,1> ]);
			end if;
		when "G":
			if   (i eq 0)			then		AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <1,1>]);
			else						AlternatingDominant_Loop(~n, ~c_pos, ~m_pos, ~c, ~m, ~k : PosCoeffs := [ <-1,3> ]);
			end if;
		else:
			error "Unknown LieType: " cat LieType;
	end case;

	return LieRepresentationDecomposition(RootDatum(D), m, c);
end function;

function AlternatingReflections( D, nr ) //-> LieRepDec
    R := RootDatum(D);
	comps := myComponents(R);
	offset := 0;
	for comp in comps do
		poss := [ i - 1 : i in comp[2] ];
		if nr in poss then
			if (#poss ne Maximum(poss) - Minimum(poss) + 1) then 
				error "Cannot find a suitable decomposition for application of AlternatingReflections.";
			end if;
			out := AlternatingReflections_Simple( comp[1], D, poss[1], nr - poss[1] );
			return out;
		end if;
	end for;

	error "Invalid nr: ", nr;
end function;

intrinsic AlternatingDominant( D::LieRepDec, word::GrpPermElt ) -> LieRepDec
{ Alternating Dominant (from LiE; see page 68 of the LiE Manual) }
    R := RootDatum(D);
    W := CoxeterGroup(R);
	fp, h := CoxeterGroup(GrpFPCox, W);
	for w in Eltseq(h(word)) do
		if w ne 0 then 
			D := AlternatingReflections( D, w-1 ); 
		end if;
	end for;

	return D;
end intrinsic;

intrinsic AlternatingDominant( R::RootDtm, wt::SeqEnum, w::GrpPermElt ) -> LieRepDec
{ Alternating Dominant (from LiE; see page 68 of the LiE Manual) }
	return AlternatingDominant( LieRepresentationDecomposition(R, wt), w );
end intrinsic;

intrinsic AlternatingDominant( R::RootDtm, wt::ModTupRngElt, w::GrpPermElt ) -> LieRepDec
{ " }
	return AlternatingDominant( LieRepresentationDecomposition(R, wt), w );
end intrinsic;
