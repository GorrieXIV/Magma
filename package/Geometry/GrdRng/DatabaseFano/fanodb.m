freeze;
 
///////////////////////////////////////////////////////////////////////
//			Fano database
// GB Oct 2003
///////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////
//		Cosmetic wrapper for the database
/////////////////////////////////////////////////////////////////////

intrinsic FanoDatabase() -> DB
{The database of Fano 3-folds}
    return GenericDatabase(:Name:="Fano");
end intrinsic;


/////////////////////////////////////////////////////////////////////
//		Getting elements out of the database
/////////////////////////////////////////////////////////////////////

forward tup_to_fano;
intrinsic Fano(D::DB,i::RngIntElt) -> GRFano
{}
    require i in [1..#D]: "Second argument i must be >= 1 and <= ",#D;
    x := Element(D,i);
    return tup_to_fano(x);
end intrinsic;

intrinsic Fano(D::DB,f::RngIntElt,i::RngIntElt) -> GRFano
{}
    require NumberOfElements(D,[f]) ge i:
	"Third argument too large; maximum value",NumberOfElements(D,[f]);
    x := Element(D,[f],i);
    return tup_to_fano(x);
end intrinsic;

intrinsic Fano(D::DB,f::RngIntElt,Q::SeqEnum,i::RngIntElt) -> GRFano
{The i-th Fano 3-fold in the Fano database D (among those having Fano
genus f >= 1, or plurigenera Q = [p_1,p_2,...] if given)}
    require #Q le 4:
	"The third argument Q can contain at most the first four genera";
    require NumberOfElements(D,[f] cat Q) ge i:
	"Third argument too large; maximum value",NumberOfElements(D,[f] cat Q);
    x := Element(D,[f] cat Q,i);
    return tup_to_fano(x);
end intrinsic;


/////////////////////////////////////////////////////////////////////
//			Searching
/////////////////////////////////////////////////////////////////////


intrinsic Fano(D::DB,W::SeqEnum) -> GRFano
{}
    Sort(~W);
    for x in D do
	if x[6] eq W then
	    return Fano(x);
	end if;
    end for;
    require false: "No Fano with weights",W;
end intrinsic;

intrinsic Fano(D::DB,f::RngIntElt,B::GRBskt) -> GRFano
{}
    return Fano(D,f,RawBasket(B));
end intrinsic;

forward sameB;
intrinsic Fano(D::DB,f::RngIntElt,B::SeqEnum) -> GRFano
{The Fano 3-fold in the Fano database D either with weights W, or with
Fano index f >= 1 and basket of singularities B (as a basket type or in raw 
sequence format)}
    Sort(~B);
    for x in D do
	if x[2] eq f and sameB(x[7],B) then
	    return Fano(x);
	end if;
    end for;
    require false: "No Fano with given index and basket";
end intrinsic;

function sameB(A,B)
    if #A ne #B then
	return false;
    end if;
    Sort(~A);
    Sort(~B);
    return &and[ A[i] eq B[i] : i in [1..#A] ];
end function;


/////////////////////////////////////////////////////////////////////
//			The raw versions
/////////////////////////////////////////////////////////////////////

intrinsic Fano(x::Tup) -> GRFano
{}
    return tup_to_fano(x);
end intrinsic;

function tup_to_fano(x)
// x is a tuple of data as returned by the GenericDatabase() object.
    X := HackobjCreateRaw(GRFano);
    X`dim := 3;
    X`fanoindex := x[2];
    X`fanogenus := x[3];
    X`fanobasegenus := x[4];
    X`indexes := x[5];
    X`weights := x[6];
    X`rawbasket := x[7];
    X`numinfo := x[8];
    X`noetherw := x[9];
    X`noethernseq := x[10];
    return X;
end function;

