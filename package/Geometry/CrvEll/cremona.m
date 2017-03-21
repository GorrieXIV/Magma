freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//              STRING LOOKUPS FOR CREMONA DATABASE               //
//                   OF MODULAR ELLIPTIC CURVES                   //
//                         David Kohel                            //
//                   Last modified July 2001                      //
//                                                                //
////////////////////////////////////////////////////////////////////

function CremonaIndexToString(Q)
    error if (#Q eq 0), "Invalid empty sequence for Cremona index.";
    if #Q eq 1 then
        return IntegerToString(Q[1]);
    end if;
    alphabet := "abcdefghijklmnopqrstuvwxyz";
    // We force length at least 1 to handle 0 properly
    L := alphabet[[x+1: x in Reverse(Intseq(Q[2]-1, 26, 1))]];
    if #Q eq 2 then
        return IntegerToString(Q[1]) cat L;
    elif #Q eq 3 then
        return IntegerToString(Q[1]) cat L cat
               IntegerToString(Q[3]);
    end if;
    error "Invalid sequence for Cremona index";
end function;

function CremonaLabelToIndex(L)
    alphabet := "abcdefghijklmnopqrstuvwxyz";
    if Index(alphabet, L[1]) ne 0 then		// new style
	indices := [ Index(alphabet, letter) - 1 : letter in Eltseq(L) ];
	error if -1 in indices, "Bad Cremona label format";
	return 1 + Seqint(Reverse(indices), 26);
    end if;
    alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    x := Index(alphabet, L[1]);
    if x eq 0 or L[1]^#L ne L then
	error "Bad Cremona label format";
    end if;
    return x + 26*(#L - 1);
end function;

function CremonaStringToIndex(L)
    ok, match, seq := Regexp("([0-9]+)([A-Za-z]*)([0-9]*)", L);
    if not ok or match ne L then
	error "Bad Cremona reference string format";
    end if;
    S := [ StringToInteger(seq[1]) ];					// N
    if seq[2] ne "" then
	S cat:= [ CremonaLabelToIndex(seq[2]) ];			// I
	if seq[3] ne "" then
	    S cat:= [ StringToInteger(seq[3]) ];			// C
	end if;
    end if;
    return S;
end function;

intrinsic CremonaReference(D::DB, E::CrvEll) -> MonStgElt
    {The Cremona database reference for E.}

    error if Type(BaseRing(E)) ne FldRat,
         "Curve must be defined over Q";

    N,i,j := CremonaReferenceData(D, E);
    return CremonaIndexToString([N, i, j]);
end intrinsic;

intrinsic CremonaReference(E::CrvEll) -> MonStgElt
    {The Cremona database reference for E.}
    return CremonaReference(CremonaDatabase(), E);
end intrinsic;

intrinsic EllipticCurves(D::DB, S::MonStgElt) -> SeqEnum
    {The sequence of elliptic curves with label S (e.g. "101A")
    in the elliptic curve database D.}

    ind := CremonaStringToIndex(S);
    N := ind[1];
    if #ind eq 1 then
        return EllipticCurves(D, N);
    elif #ind eq 2 then
        I := ind[2];
        return EllipticCurves(D, N, I);
    end if;
    error "Invalid index to specify isogeny class of curves.";
end intrinsic;

intrinsic EllipticCurves(D::DB, N::RngIntElt, S::MonStgElt) -> SeqEnum
    {The sequence of elliptic curves of conductor N and label S
    (e.g. "A") in the elliptic curve database D.}

    k := CremonaLabelToIndex(S);
    require k le NumberOfIsogenyClasses(D, N) :
        "Conductor", N, "does not have", k, "isogeny classes.";
    return EllipticCurves(D, N, k);
end intrinsic;

intrinsic EllipticCurve(S::MonStgElt) -> SeqEnum
    {An elliptic curve with label S (e.g. "101A" or "101A1")
     in the Cremona database.}
     return EllipticCurve(CremonaDatabase(), S);
end intrinsic;

intrinsic EllipticCurve(D::DB, S::MonStgElt) -> SeqEnum
    {An elliptic curve with label S (e.g. "101A" or "101A1")
    in the elliptic curve database D.}

    ind := CremonaStringToIndex(S);
    N := ind[1];
    if #ind eq 1 then
        return EllipticCurve(D, N, 1, 1);
    end if;
    I := ind[2];
    require NumberOfIsogenyClasses(D, N) ge I :
        "Conductor does not have", I, "isogeny classes.";
    if #ind eq 2 then
        return EllipticCurve(D, N, I, 1);
    elif #ind eq 3 then
        J := ind[3];
        require NumberOfCurves(D, N, I) ge J :
            "Isogeny class does not have", J, "elements.";
        return EllipticCurve(D, N, I, J);
    end if;
end intrinsic;

intrinsic EllipticCurve(D::DB, N::RngIntElt, S::MonStgElt, J::RngIntElt)
    -> SeqEnum
    {The J-th elliptic curve of conductor N and label S (e.g. "A")
    in the elliptic curve database D.}

    I := CremonaLabelToIndex(S);
    require NumberOfIsogenyClasses(D, N) ge I :
        "Conductor does not have", I, "isogeny classes.";
    require NumberOfCurves(D, N, I) ge J :
        "Isogeny class does not have", J, "elements.";
    return EllipticCurve(D, N, I, J);
end intrinsic;

intrinsic NumberOfCurves(D::DB, S::MonStgElt) -> RngIntElt
    {The number of curves isogeny class defined by S (e.g. "101A").}

    ind := CremonaStringToIndex(S);
    error if #ind gt 2,
        "Invalid string for isogeny class";
    N := ind[1];
    if #ind eq 1 then
        return NumberOfCurves(D, N);
    end if;
    I := ind[2];
    require NumberOfIsogenyClasses(D, N) ge I :
        "Conductor does not have", I, "isogeny classes.";
    return NumberOfCurves(D, N, I);
end intrinsic;

intrinsic NumberOfCurves(D::DB, N::RngIntElt, S::MonStgElt) -> RngIntElt
    {The number of curves of conductor N and isogeny class
    S (e.g. "A").}

    I := CremonaLabelToIndex(S);
    require NumberOfIsogenyClasses(D, N) ge I :
        "Conductor does not have", I, "isogeny classes.";
    return NumberOfCurves(D, N, I);
end intrinsic;
