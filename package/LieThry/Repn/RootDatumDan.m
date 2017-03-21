freeze;

/* By Dan */
import "../Root/RootDtm.m": toType;

intrinsic LiERootDatum( Name::MonStgElt ) -> RootDtm
{ Create RootDatum with potentially non-zero-dimensional torus }
	return RootDatum( Name : Isogeny := "SC" );
end intrinsic;

function myComponents( R : IncludeToralPart := true, Use := "Both" )
/* Decomposes RootDatum R into a list of root data, toral and simple, 
   for the functionality from LiE.

   This means that the Roots and Coroots must have a very specific, easily
   decomposable form. This function errors if that is not the case.

   Returns a list L consisting of tuples t:
   * t[1] irreducible rootdatum or "T"
   * t[2] the indices in the original roots corresponding to this rootdatum
     (useful for splitting weights into the irreducible components)
   and a permutation pi. Pi is chosen in such a way that 
   PermuteSequence(wt, pi) gives a weight wt', such that the order of the 
   entries of wt' corresponds to the order of the simple (and toral) 
   components in L.
*/
	if IsIrreducible(R) then
	  n := Rank(R);
	  return [* <R,[1..n]> *], Sym(n)!1;
	end if;

	dim := Dimension(R);
	rts := SimpleRoots(R);
	corts := SimpleCoroots(R);
	if (Use notin { "Roots", "Coroots", "Both" } ) then error "Invalid parameter: Use = ", Use; end if;
	ret := [* *];

	totalnonzero := { };

	for t in toType(R) do
		lietype := t[1];
		lierank := #(t[2]);

		/* find out where this component is */
		nonzero := {};
		for r in t[2] do
			if Use eq "Roots"     then nonzero join:= { i : i in [1..dim] | rts[r][i] ne 0 }; 
			elif Use eq "Coroots" then nonzero join:= { i : i in [1..dim] | corts[r][i] ne 0 }; 
			elif Use eq "Both"    then nonzero join:= { i : i in [1..dim] | rts[r][i] ne 0 or corts[r][i] ne 0 }; 
			end if;
		end for;
		
		/* check if this component is still 'easy' (as above) */
		if #nonzero ne lierank then error "Could not decompose ", R; end if;
		if #(nonzero meet totalnonzero) ne 0 then error "Could not decompose ", R; end if;
		totalnonzero join:= nonzero;

		/* construct component */
		nonzero := Setseq(nonzero);
		subrts := Matrix([ Eltseq(rts[r])[nonzero] : r in t[2] ]);
		subcorts := Matrix([ Eltseq(corts[r])[nonzero] : r in t[2] ]);
		
		/* insert into result */
		Append(~ret, <RootDatum(subrts, subcorts), nonzero>);
	end for;

	/* get toral part, if needed */
	if (#totalnonzero lt dim) then
		toral := Setseq( Seqset([1..dim]) diff totalnonzero);
		if IncludeToralPart then
			Append(~ret, <"T",  toral>);
		end if;
	else
		toral := false;
	end if;

	/* construct pi */
	l := [];
	for t in ret do l cat:= t[2]; end for;
	if toral cmpne false and not IncludeToralPart then l cat:= toral; end if;
	pi := Sym(#l)!l;

	/* and we're done. */
	return ret, pi;
end function;



function Exponents_Simple( LieType, LieRank ) //->SeqEnum
	case LieType:
		when "A":				return [i : i in [1..LieRank] ];
		when "B", "C":			return [2*(i-1) + 1 : i in [1..LieRank] ];
		when "D":			
			t := [ 2*(i-1) + 1 : i in [1..(LieRank - 1)] ];
			case IsOdd(LieRank):
				when true:		Insert(~t, (LieRank+1) div 2, LieRank-1);
				when false:		Insert(~t, LieRank div 2, LieRank-1);
			end case;
			return t;
		when "E":
			case LieRank:
				when 6:			return [1,4,5,7,8,11];
				when 7:			return [1,5,7,9,11,13,17];
				when 8:			return [1,7,11,13,17,19,23,29];
			end case;
		when "F":				return [1,5,7,11];
		when "G":				return [1,5];
		when "T":				return [ 0 : i in [1..LieRank] ];
	end case;
end function;


intrinsic Exponents( R::RootDtm ) -> SeqEnum
{ The exponents of the given rootdatum, as in LiE. See also page 62 of the LiE manual. }
	ret := [];
	comps, pi := myComponents(R);
	for comp in comps do
		tp := (Type(comp[1]) eq MonStgElt) select comp[1] else CartanName(comp[1])[1];
		rnk := #(comp[2]);
		ret cat:= Exponents_Simple(tp, rnk);
	end for;

	ret := PermuteSequence(ret, pi^-1);
	return ret;
end intrinsic;





function Adjoint_Simple( G ) //->ModTupFldElt
	return HighestRoot(G : Basis := "Weight");
end function;


intrinsic AdjointRepresentationDecomposition( R::RootDtm ) -> LieRepDec
{ The decomposition polynomial of the adjoint representation of the Lie group of the root datum R }

	dimR := Dimension(R); trR := dimR-Rank(R);

    out := LieRepresentationDecomposition(R);

	comps := myComponents(R);
	
	pos := 0;
	for comp in comps do
		if (comp[1] cmpeq "T") then 
		    AddRepresentation( ~out, [ 0 : i in [1..dimR] ], #(comp[2]) ); 
		else
			rnk := Rank(comp[1]);

			x := Adjoint_Simple( comp[1] );
			w := Vector([ 0 : i in [1..dimR] ]);
			for p in [1..rnk] do w[comp[2][p]] := x[p]; end for;
		
		    out +:= w;
		end if;
	end for;

	return out;
end intrinsic;

/* Convenient */
intrinsic Weights( D::LieRepDec ) -> SeqEnum, SeqEnum
{The weights and multiplicities in D }
    return Explode(D`WtsMps);
end intrinsic;

intrinsic WeightsAndMultiplicities( D::LieRepDec ) -> SeqEnum, SeqEnum
{The weights and multiplicities in D }
    return Explode(D`WtsMps);
end intrinsic;

intrinsic Multiplicity( D::LieRepDec, v::ModTupRngElt ) -> RngIntElt
{ The multiplicity of the weight v in D }
	wts, mps := WeightsAndMultiplicities(D);
	p := Position(wts, v);
	if p eq 0 then return 0; else return mps[p]; end if;
end intrinsic;
intrinsic Multiplicity( D::LieRepDec, v::SeqEnum ) -> RngIntElt
{ The multiplicity of the weight v in D }
	return Multiplicity(D, Vector(v));
end intrinsic;


intrinsic Multiset( D::LieRepDec ) -> SetMulti
{The weights and multiplicities in D as a multiset }
    wts, mps := WeightsAndMultiplicities(D);
	assert #wts eq #mps;
	return {* wts[i]^^mps[i]:  i in [1..#wts] *};
end intrinsic;


/* Conversion, just because it may be practical */
intrinsic ToLiE( D::LieRepDec ) -> MonStgElt
{ Prints D in LiE format }
    out := "";
    wts, mps := Explode(D`WtsMps);
    for i in [1..#wts] do
        if (mps[i] gt 0 and i gt 1) then
            out cat:= "+";
        end if;
        out cat:= IntegerToString(mps[i]);
        out cat:= "X";
        out cat:= &cat[ t : t in Eltseq(Sprint(Eltseq(wts[i]))) | t ne " "];
    end for;
    return out;
end intrinsic;

intrinsic FromLiE( R::RootDtm, p::MonStgElt ) -> LieRepDec
{ Returns a LieRepDec object }
    univwts := RSpace(Rationals(), Dimension(R)); 
    univmps := Integers();
    wts := [ univwts | ]; mps := [ univmps | ];
    
    t := "";
    st := "mp";
    for c in Eltseq(p) do
        if c eq "X" then
            if st ne "mp" then error "Incorrect format"; end if;
            u := eval(t);
            if not IsCoercible(univmps, u) then error "'" cat t cat "' is not a multiplicity"; end if;
            Append(~mps, u);
            t := ""; st := "wt";
        elif c eq "]" then
            if st ne "wt" then error "Incorrect format"; end if;
            t cat:= c;
            u := eval(t);
            if not IsCoercible(univwts, u) then error "'" cat t cat "' is not a valid weight"; end if;
            Append(~wts, u);
            t := ""; st := "mp";
        else
            t cat:= c;
        end if;
    end for;
    
    if t ne "" then error "Input should end with a ']' character"; end if;
    
    return LieRepresentationDecomposition(R, wts, mps);
end intrinsic;


/*
 *
 * Functions below by Bruce Westbury 
 *
 */

NCasimir := function( R, w )
	local l, M;
	// The value of the quadratic Casimir on the highest weight module 
	// with highest weight w.

    l := Rank( R );
    M := CoxeterForm( R : Basis:= "Root" );
    return &+[ w[i]*(w[i]+2)*M[i][i] : i in [1..l] ] ;
end function;

intrinsic CasimirValue(R::RootDtm, w::SeqEnum[RngIntElt]) -> FldRatElt
{ The value of the quadratic Casimir on the highest weight module 
  with highest weight w normalised to take the value 2 on the
  highest weight of the adjoint representation. }

    return CasimirValue(R, Vector(w));
end intrinsic;

intrinsic CasimirValue(R::RootDtm, w::ModTupRngElt) -> FldRatElt
{ The value of the quadratic Casimir on the highest weight module 
  with highest weight w normalised to take the value 2 on the
  highest weight of the adjoint representation. }

	require IsCrystallographic( R ) : "This function only works for crystallographic root data";
	require NumberOfColumns(w) eq Dimension(R) : "The weight is not of the correct length";
	require &and[ IsIntegral( w[i] ) and w[i] ge 0 : i in [1..Dimension(R)] ] : "The weight must be dominant integral";

    return 2*NCasimir(R,HighestRoot(R : Basis := "Weight"))/NCasimir(R,w);
end intrinsic;


/* This function is taken from
/usr/local/pkg/magma-2.10/package/Algebra/AlgLie/freudenthal.m
and modified to produce the quantum dimension. 

The output is two Multisets of positive integers. This should be
read as follows. Take the product of the integers in Num and divide
by the product of the integers in Den to get the ordinary dimension.
If you replace each integer by the quantum integer this will give
the quantum dimension.

This means that the output should really be converted to a
Laurent polynomial in q. However it is more useful to me in this
format.

Bruce Westbury
October 2003 */

intrinsic QuantumDimension(R::RootDtm, w::SeqEnum[RngIntElt]) -> SetMulti, SetMulti
{ Two Multisets of positive integers, Num and Den. This should be
    read as follows. Take the product of the integers in Num and divide
    by the product of the integers in Den to get the ordinary dimension.
    If you replace each integer by the quantum integer this will give
    the quantum dimension.}
    
    return QuantumDimension(R, Vector(w));
end intrinsic;

intrinsic QuantumDimension(R::RootDtm, w::ModTupRngElt) -> SetMulti, SetMulti
{ Two Multisets of positive integers, Num and Den. This should be
    read as follows. Take the product of the integers in Num and divide
    by the product of the integers in Den to get the ordinary dimension.
    If you replace each integer by the quantum integer this will give
    the quantum dimension.}

    local l, M, posR, Den, Num, n, m;
    
	require IsCrystallographic( R ) : "This function only works for crystallographic root data";
	require NumberOfColumns(w) eq Dimension(R) : "The weight is not of the correct length";
	require &and[ IsIntegral( w[i] ) and w[i] ge 0 : i in [1..Dimension(R)] ] : "The weight must be dominant integral";

    l := Rank( R );
    
    posR := PositiveRoots( R : Basis:= "Root" );
    M := CoxeterForm( R : Basis:= "Root" );
    Den := {* Integers() | *};
    Num := {* Integers() | *};
    
    for r in posR do
        Include( ~Num , &+[ r[i]*(w[i]+1)*M[i][i] : i in [1..l] ] );
        Include( ~Den , &+[ r[i]*M[i][i] : i in [1..l] ] );
    end for;
    
    for n in MultisetToSet(Den) do
        m := Min(Multiplicity(Den,n),Multiplicity(Num,n));
        Exclude(~Num,n^^m);
        Exclude(~Den,n^^m);
    end for;
    
    return Num, Den;
end intrinsic;


/*
 * For the "Decreasing Height Ordering "
 */
function levelVecSimp(R)
    CM := ChangeRing(CartanMatrix(R), Rationals());
    InvCM := ChangeRing( (CM/Determinant(CM))^-1, Integers());
    return Vector([1 : i in [1..Dimension(R)]])*Transpose(InvCM);
end function;

intrinsic InternalLevelVec(R::RootDtm) -> ModTupRngElt
{ internal, for decreasing height ordering }
    if (Dimension(R) eq 0) then return Vector([Integers()|]); end if;
    
    comps, pi := myComponents(R);
    v := [* c[1] cmpeq "T" select
               Vector([0 : i in [1..#(c[2])] ])
           else
               levelVecSimp(c[1]) 
           : c in comps *];
    return Vector(PermuteSequence(&cat[ Eltseq(e) : e in v ], pi));
end intrinsic;
