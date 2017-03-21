freeze;
 
/////////////////////////////////////////////////////////////////////
//	Intrinsics that prepare Fano data for the Fano database
//
// It is assumed that you have got a sequence Q that contains all
// the Fano 3-folds that you want to be in the database IN THE RIGHT ORDER.
// For the eventual creation of .dat and .sig files (using other
// functions) it is also fine to split the files of records AS LONG
// AS THE ORDER IS PRESERVED.
//
/////////////////////////////////////////////////////////////////////

/*
An example of the translation Fano -> record.

Given Fano X:
Fano 3-fold X,A of Fano index 8 in codimension 4 with data
  Weights: [ 1, 2, 2, 3, 5, 8, 9, 11 ]
  Basket: 1/11(2,9,8)
  Degrees: A^3 = 1/11,  (1/12)Ac_2(X) = 3/22    (Bogomolov unstable)
  Numerator: t^33 - ... + t^14 - t^10 - t^9 - t^8 - t^6 + 1

with

> NoetherWeights(X);
[ 1, 2, 2, 11 ]
> NoetherNumerator(X);
t^8 + t^5 + t^3 + 1

we get the record

rec<recformat<identifier, fanoindex, fanogenus, fanobasegenus: RngIntElt, 
indexes, weights, basket, numinfo, noether, numerator: SeqEnum> | 
    fanoindex := 8,
    fanogenus := 0,
    fanobasegenus := 0,
    indexes := [ 1, 3, 4, 7, 10 ],
    weights := [ 1, 2, 2, 3, 5, 8, 9, 11 ],
    basket := [
        [ 11, 2, 9, 8 ]
    ],
    numinfo := [
        [ 6, 1, 8, 1, 9, 1, 10, 1 ],
        [ 14, 1, 15, 1, 16, 1, 17, 1, 18, 1, 19, 1 ],
        [ 33, 3 ]
    ],
    noether := [ 1, 2, 2, 11 ],
    numerator := [ 1, 0, 0, 1, 0, 1, 0, 0, 1 ]
    >
*/

/////////////////////////////////////////////////////////////////////
//		Translating between Fanos and records
/////////////////////////////////////////////////////////////////////

intrinsic FanoToRecord(X::GRFano) -> Rec
{A record whose fields are a minimal collection of the attributes of
the Fano X}
    Fano := recformat<
	identifier,fanoindex,fanogenus,fanobasegenus : RngIntElt,
	indexes,weights,basket,numinfo,noether,numerator : SeqEnum >;
    Xrec := rec< Fano | >;
    Xrec`identifier := Integers() ! 0;
    Xrec`indexes := [ Integers() | FanoIndex(X) ] cat HilbertCoefficients(X,4);
    Xrec`fanoindex := Integers() ! X`fanoindex;
    Xrec`fanogenus := Integers() ! FanoGenus(X);
    Xrec`fanobasegenus := Integers() ! FanoBaseGenus(X);
    Xrec`weights := [ Integers() | w : w in Weights(X) ];
    Xrec`basket := RawBasket(X);
    Xrec`numinfo := NumeratorData(X);
    Xrec`noether := [ Integers() | w : w in NoetherWeights(X) ];
    coeffs := Coefficients(NoetherNumerator(X));
    ChangeUniverse(~coeffs, Integers());
    Xrec`numerator := coeffs;
    return Xrec;
end intrinsic;

intrinsic Fano(x::Rec) -> GRFano
{Return a Fano 3-fold with data from the database-style tuple or
record of data x}
    Y := HackobjCreateRaw(GRFano);
    Y`dim := 3;
    Y`indexes := x`indexes;
    Y`fanoindex := x`fanoindex;
    Y`fanogenus := x`fanogenus;
    Y`fanobasegenus := x`fanobasegenus;
    Y`weights := x`weights;
    Y`basket := MakeBasket(x`basket);
    Y`noetherw := x`noether;
    Y`noethern := x`numerator;
    Y`numinfo := x`numinfo;
    return Y;
end intrinsic;


///////////////////////////////////////////////////////////////////////	
//	Writing a sequence of Fanos to a text file
//
// This code is copied from ~bruce/databases/qmdb/write_info_file.m .
//
// To write a new data file in a magma session:
//		> WriteFanoData(Q,"newfilename");
// where Q is a sequence of Fanos.
///////////////////////////////////////////////////////////////////////

forward ConstructData;
intrinsic WriteFanoData(Q::SeqEnum,F::MonStgElt)
{Write the Fano 3-folds in the sequence Q of Fano 3-folds to the file named F,
encoding each member as a record}
    Krec := [ FanoToRecord(X) : X in Q ];
    ConstructData(F,Krec);
end intrinsic;


/////////////////////////////////////////////////////////////////////
//			Write records to a file
/////////////////////////////////////////////////////////////////////

WriteHead := procedure(F)
    fprintf F, "T := PolynomialRing(Rationals()); t := T.1;\n";
    fprintf F, "GRFano := recformat<\n";
    fprintf F, "identifier,fanoindex,fanogenus,fanobasegenus : RngIntElt,\n";
    fprintf F, "indexes,weights,basket,numinfo : SeqEnum,\n";
    fprintf F, "noether,numerator : SeqEnum >;\n";
    fprintf F, "data := [ Parent(rec< GRFano | >) | ];\n";
end procedure;

// data is a sequence of records
ConstructData := procedure(F,data)
    WriteHead(F);
    for X in data do
	fprintf F, "r := rec< GRFano | >;\n";
	if assigned X`identifier then
	    fprintf F, "r`identifier := %o;\n", X`identifier;
	end if;
	if assigned X`fanoindex then
	    fprintf F, "r`fanoindex := %o;\n", X`fanoindex;
	end if;
	if assigned X`fanogenus then
	    fprintf F, "r`fanogenus := %o;\n", X`fanogenus;
	end if;
	if assigned X`fanobasegenus then
	    fprintf F, "r`fanobasegenus := %o;\n", X`fanobasegenus;
	end if;
	if assigned X`indexes then
	    fprintf F, "r`indexes := %o%o;\n", "\\", X`indexes;
	end if;
	if assigned X`weights then
	    fprintf F, "r`weights := %o%o;\n", "\\", X`weights;
	end if;
	if assigned X`basket then
	    fprintf F, "r`basket := %o;\n", X`basket;
	end if;
	if assigned X`numinfo then
	    fprintf F, "r`numinfo := %o;\n", X`numinfo;
	end if;
	if assigned X`noether then
	    fprintf F, "r`noether := %o%o;\n", "\\", X`noether;
	end if;
	if assigned X`numerator then
	    fprintf F, "r`numerator := %o%o;\n", "\\", X`numerator;
	end if;
	fprintf F, "Append(~data, r);\n";
    end for;
end procedure;

