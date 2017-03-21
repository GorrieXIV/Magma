freeze;
 
/////////////////////////////////////////////////////////////////////
//		Translation to and from records
/////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////
//		Singularities and baskets
// The records created for baskets are not very efficient.
// If you want to manage large lists, you should record the
// basket information more precisely and optimally.
/////////////////////////////////////////////////////////////////////

intrinsic GRPtSToRec(X::GRPtS) -> Rec
{A record whose fields are a minimal collection of the attributes of X}
    GRPtSRec := recformat< r,n : RngIntElt, P : SeqEnum >;
    Xrec := rec< GRPtSRec | >;
    Xrec`r := X`r;
    Xrec`n := X`n;
    Xrec`P := X`P;
    return Xrec;
end intrinsic;

intrinsic RecToGRPtS(X::Rec) -> GRPtS
{A graded ring object made from the data of the record X}
    Y := HackobjCreateRaw(GRPtS);
    Y`r := X`r;
    Y`n := X`n;
    Y`P := X`P;
    return Y;
end intrinsic;

intrinsic GRCrvSToRec(X::GRCrvS) -> Rec
{A record whose fields are a minimal collection of the attributes of X}
    GRCrvSRec := recformat< d : FldRatElt, N,t : RngIntElt, p : Rec >;
    Xrec := rec< GRCrvSRec | >;
    Xrec`d := X`d;
    Xrec`N := X`N;
    Xrec`t := X`t;
    Xrec`p := GRPtSToRec(X`p);
    return Xrec;
end intrinsic;

intrinsic RecToGRCrvS(X::Rec) -> GRCrvS
{A graded ring object made from the data of the record X}
    Y := HackobjCreateRaw(GRCrvS);
    Y`d := X`d;
    Y`N := X`N;
    Y`t := X`t;
    Y`p := RecToGRPtS(X`p);
    return Y;
end intrinsic;

intrinsic GRBsktToRec(X::GRBskt) -> Rec
{A record whose fields are a minimal collection of the attributes of X}
    GRBsktRec := recformat< points,curves : SeqEnum >;
    Xrec := rec< GRBsktRec | >;
    Xrec`points := [ GRPtSToRec(p) : p in Points(X) ];
    Xrec`curves := [ GRCrvSToRec(C) : C in Curves(X) ];
    return Xrec;
end intrinsic;

intrinsic RecToGRBskt(X::Rec) -> GRBskt
{A graded ring object made from the data of the record X}
    Y := HackobjCreateRaw(GRBskt);
    Y`points := [ RecToGRPtS(p) : p in X`points ];
    Y`curves := [ RecToGRCrvS(C) : C in X`curves ];
    return Y;
end intrinsic;


/////////////////////////////////////////////////////////////////////
//		Generic graded ring objects
/////////////////////////////////////////////////////////////////////

intrinsic GRSchToRec(X::GRSch) -> Rec
{A record whose fields are a minimal collection of the attributes of X}
    GRSchRec := recformat<
			dim : RngIntElt,
			basket : Rec,
			weights : SeqEnum,
			num : RngUPolElt,
			degree, Ac : FldRatElt >;
    Xrec := rec< GRSchRec | >;
    if assigned X`dim then
	Xrec`dim := X`dim;
    end if;
    if assigned X`basket then
	Xrec`basket := GRBsktToRec(X`basket);
    end if;
    if assigned X`weights then
	Xrec`weights := X`weights;
    end if;
    if assigned X`num then
	Xrec`num := X`num;
    end if;
    if assigned X`degree then
	Xrec`degree := X`degree;
    end if;
    if assigned X`Ac then
	Xrec`Ac := X`Ac;
    end if;
    return Xrec;
end intrinsic;

intrinsic RecToGRSch(X::Rec) -> GRSch
{A graded ring object made from the data of the record X}
// This assumes that the fields of X are those of GRSchRec above
    Y := HackobjCreateRaw(GRSch);
    if assigned X`dim then
	Y`dim := X`dim;
    end if;
    if assigned X`basket then
	Y`basket := RecToGRBskt(X`basket);
    end if;
    if assigned X`weights then
	Y`weights := X`weights;
    end if;
    if assigned X`num then
	Y`num := X`num;
    end if;
    if assigned X`degree then
	Y`degree := X`degree;
    end if;
    if assigned X`Ac then
	Y`Ac := X`Ac;
    end if;
    return Y;
end intrinsic;

