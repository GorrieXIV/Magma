/******************************************************************************
 *
 *    util.m    Useful Magma intrinsics
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm, Eamonn O'Brien and Mark Stather
 *    Dev start : 2005-04-30
 *
 *    Version   : $Revision:: 2244                                           $:
 *    Date      : $Date:: 2011-03-25 13:08:05 +1100 (Fri, 25 Mar 2011)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: util.m 2244 2011-03-25 02:08:05Z eobr007                       $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "closure.m": RandomSubProduct;

forward structFrobeniusTwist, elementFrobeniusTwist;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic GeneratingTranspositions(n :: RngIntElt) -> []
    { Construct generating set for S_n used in the Coxeter presentation.
    This is the n transpositions of the form (i, i + 1). }
    local seq, gens, G, newSeq;
    
    // Construct every transposition
    return  [Sym(n) ! (i, i + 1) : i in [1 .. n - 1]];
end intrinsic;

intrinsic AllTranspositions(n :: RngIntElt) -> []
    { Construct generating set for S_n used in the Coxeter presentation.
    This is the n transpositions of the form (i, i + 1). }
    local seq, gens, G, newSeq;
    
    // Construct every transposition
    return  [Sym(n) ! (i, j) : i in [1 .. n - 1], j in [1 .. n] | i lt j];
end intrinsic;

intrinsic GeneratingTransvections(d :: RngIntElt, p :: RngIntElt) -> []
    { Construct the generating set for SL(d, p) consisting of all matrices
    I + E_ij where E_ij has a 1 in the (i,j)-th position and 0 elsewhere.
    p must be a prime, since the generators will only generate SL(d, p)
    over the prime field. }

    require IsPrime(p) : "p must be a prime number";
    
    G := GL(d, p);
    MA := MatrixAlgebra(GF(p), d);

    return [G ! (One(MA) + MatrixUnit(MA, i, j)) : i in [1 .. d],
	j in [1 .. d] | i ne j];
end intrinsic;

intrinsic Normalise(seq :: SeqEnum) -> SeqEnum
    { Normalise each matrix in seq. }
    return [Normalise(g) : g in seq];
end intrinsic;

/* 
intrinsic IsNormalSeries(series :: SeqEnum) -> BoolElt
{test if the series of subgroups is a normal series}

    topDown := Reverse(series);
    RandomSchreier(topDown[1]);
    Verify(topDown[1]);

    for i in [1 .. #topDown - 1] do
	if not topDown[i + 1] subset topDown[i] then
	    str := Sprintf("%o not subgroup of %o",
		topDown[i + 1], topDown[i]);
	    return false;
	end if;
	
	if not IsNormal(topDown[i], topDown[i + 1]) then
	    str := Sprintf("%o not normal in %o",
		topDown[i + 1], topDown[i]);
	    return false;
	end if;
    end for;

    return true;
end intrinsic;

*/

function getLatexMatrixRow(row)
    rowStr := "";

    for i in [1 .. #row - 1] do
	rowStr cat:= Sprintf("%o & ", row[i]);
    end for;

    return Sprintf("%o%o", rowStr, row[#row]);
end function;

function GetLaTeXMatrix(M)
    rows := RowSequence(M);

    str := &cat[Sprintf("%o \\\\\n", getLatexMatrixRow(rows[j])) :
	j in [1 .. #rows - 1]];
    
    return str cat getLatexMatrixRow(rows[#rows]);
end function;

