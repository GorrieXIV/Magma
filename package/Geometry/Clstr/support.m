freeze;

/*
David Kohel: 2002/06
 --Deprecation of function name Support in preference for 
   general function RationalPoints and Points for schemes.  
 --All code in the file should be considered deprecated and 
   to be removed at some future date, and is provided for 
   backward compatibility.
 --Expanded functionality for testing of irreducibile and 
   reduced schemes, decompositions, degree of schemes, and 
   point enumeration, and cluster creation is provided in 
   the separate files cluster.m, degree.m, ratpoints.m,
   and splitting.m.
*/

/////////////////////////////////////////////////////////////////
// Formerly: cluster.m
//	Code for zero-dimensional schemes:
//		support over various fields
// GDB 13/11/00
/////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
//			Support
///////////////////////////////////////////////////////////////////////

tuple2seq := func< t | [ t[i] : i in [1..#t] ] >;

intrinsic Support(Z::Clstr,K::Rng) -> SetEnum
{Sequence of points of Z defined over K or the base field of Z}
    if IsAffine(Z) then
	return { Z(K) | Z(K) ! p : p in var }
	    where var is [ tuple2seq(p) : p in Variety(DefiningIdeal(Z),K)];
    elif IsOrdinaryProjective(Z) then
	Ztemp := Z;
	A := Ambient(Z);
	d := Dimension(A);
	pts := { Z(K) | };
	for i in [1..d+1] do
	    // Note the coercion from an affine point to a projective one
	    // takes care of where to put the 1s in the coordinates.
	    pts join:=  { Z(K) ! p : p in Support(Zi,K) }
			where Zi is AffinePatch(Ztemp,i);
	    // cut Ztemp down a bit so as not to repeat points.
	    Ztemp := Scheme(A, DefiningPolynomials(Ztemp) cat [A.(d+2-i)] );
	    // Point is that Ztemp could be empty and the 'Cluster' creation
	    // function doesn't allow that. It's not a problem since we already
	    // know that the support is a finite number of points.
	end for;
	return pts;
    else
	gr := Gradings(Z);
	A := Ambient(Z);
	d := Dimension(A);
	require #gr eq 2 and d eq 2:
	    "Argument must lie in affine space, projective space or a "*
			"surface scroll";	// THINK: extra cases to do.
	pts := { Z(K) |  };
	Ztemp := Z;
	for i in [1..d+#gr] do
	    pts join:=  { Z(K) ! p : p in Support(Zi,K) }
			where Zi is AffinePatch(Ztemp,i);
	    // THINK: the next line is trickier in this case; it will speed big
	    // calculations up once it's right.
	    // Ztemp := Scheme(A, DefiningPolynomials(Ztemp) cat [A.(d+3-i)] );
	end for;
	return pts;
    end if;
end intrinsic;

intrinsic Support(Z::Clstr) -> SetEnum
{"} // "
    require IsAffine(Z) or IsOrdinaryProjective(Z) or 
		(Dimension(Ambient(Z)) eq 2 and #Gradings(Z) eq 2) : 
	    "Argument must lie in affine space, projective space or a "*
			"surface scroll";	// THINK: extra cases to do.
    return Support(Z,BaseField(Z));
end intrinsic;

intrinsic SupportOverSplittingField(Z::Clstr) -> SetEnum,Fld
{Sequence of points of Z defined over a splitting field}
    // AKS explained the VarietySizeOverAlgebraicClosure intrinsic.
    K := BaseRing(Z);
    if Type(K) cmpeq FldAC then
	return Support(Z);
    elif K cmpeq RationalField() then
	return Support(Z,AlgebraicClosure());
    elif Type(K) eq FldFin then
	if IsAffine(Z) then
	    r := RadicalDecomposition(DefiningIdeal(Z));
	    d := LCM([VarietySizeOverAlgebraicClosure(J): J in r]);
	    L := ext<K | d>;
	    return Support(Z,L);
	else
	    ext_degs := [];
	    for i in [1..NumberOfAffinePatches(Z)] do
		Zi := AffinePatch(Z,i);
		ri := RadicalDecomposition(DefiningIdeal(Zi));
		di := LCM([VarietySizeOverAlgebraicClosure(J): J in ri]);
		Append(~ext_degs,di);
	    end for;
	    d := LCM(ext_degs);
	    L := ext<K | d>;
	    return Support(Z,L);
	end if;
    else
	require false: "Cannot compute over the given base field";
    end if;
end intrinsic;

intrinsic Support(S::Sch,K::Rng) -> SetEnum
{Sequence of points of the zero-dimensional scheme S defined over K or the base field of S}
    if IsEmpty(S) then		// too much dim checking?
	return { S(K) | };
    end  if;
    b,Z := IsCluster(S);
    require b:
	"Scheme is not zero dimensional";
    require IsAffine(Z) or IsOrdinaryProjective(Z) or (Dimension(Ambient(Z)) eq 2 and #Gradings(Z) eq 2) : 
	    "Argument must lie in affine space, projective space or a "*
			"surface scroll";	// THINK: extra cases to do.
    return Support(Z,K);
end intrinsic;

intrinsic Support(S::Sch) -> SetEnum
{"} // "
    if IsEmpty(S) then		// too much dim checking?
	return { S(BaseField(S)) | };
    end  if;
    b,Z := IsCluster(S);
    require b:
	"Scheme is not zero dimensional";
    require IsAffine(Z) or IsOrdinaryProjective(Z) or 
		(Dimension(Ambient(Z)) eq 2 and #Gradings(Z) eq 2) : 
	    "Argument must lie in affine space, projective space or a "*
			"surface scroll";	// THINK: extra cases to do.
    return Support(Z);
end intrinsic;

intrinsic SupportOverSplittingField(S::Sch) -> SetEnum,Fld
{Sequence of points of the zero-dimensional scheme S  defined over a
splitting field; the splitting field is returned as second value}
    b,Z := IsCluster(S);
    require b:
	"Scheme is not zero dimensional";
    return SupportOverSplittingField(Z);
end intrinsic;


