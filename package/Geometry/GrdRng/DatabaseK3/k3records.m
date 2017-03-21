freeze;
 
/////////////////////////////////////////////////////////////////////
//	Intrinsics that prepare K3 data for the K3 database
//
// It is assumed that you have got a sequence Q that contains all
// the K3 surfaces of the database IN THE RIGHT ORDER.
// For the eventual creation of .dat and .sig files (using other
// functions) it is also fine to split the files of records AS LONG
// AS THE ORDER IS PRESERVED.
//
// Contents:
//	-- an example K3 surface with its corresponding record
//	-- intrinsics to translate K3 surfaces to and from records
//	-- intrinsic to write a seq of K3 surfaces (as records) to a file
//
/////////////////////////////////////////////////////////////////////

/*
An example of the translation K3 surface -> record.

Given K3 surface X:

> X;
K3 surface, genus -1, number 1234, in codimension 12 with data
  Weights: [ 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 7, 12 ]
  Basket: 2 x 1/2(1,1), 2 x 1/3(1,2), 1/5(1,4), 1/7(2,5)
  Degree: 59/105                Singular rank: 16
  Numerator: t^72 - ... + 11*t^22 - 7*t^10 - 16*t^9 - 14*t^8 - 5*t^7 - t^6 - 1
  Projection to codim 9 K3 no.940 -- type II_2 from 1/3(1,2)
  Projection to codim 3 K3 number 202 -- type IV from 1/2(1,1)
  Projection to codim 10 K3 no.1211 -- type II_1 from 1/5(1,4)
  Unproj'n from codim 14 K3 no.1238 -- type II_1 from 1/6(1,5)
  Unproj'n from codim 13 K3 no.1258 -- type I from 1/5(2,3)
  Unproj'n from codim 14 K3 no.1327 -- type II_1 from 1/4(1,3)
  Unproj'n from codim 15 K3 no.1483 -- type II_2 from 1/3(1,2)
  Unproj'n from codim 15 K3 no.2308 -- type IV from 1/2(1,1)

we write the record

> K3SurfaceToRecord(X);		// THINK: old version

rec<recformat<identifier: RngIntElt, genus1to5, weights, basket, numinfo, 
projinds, projdata, noether: SeqEnum, numerator: RngUPolElt> | 
    identifier := 1234,
    genus1to5 := [ 0, 1, 3, 5, 7 ],
    weights := [ 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 7, 12 ],
    basket := [
        [ 2, 1 ],
        [ 2, 1 ],
        [ 3, 1 ],
        [ 3, 1 ],
        [ 5, 1 ],
        [ 7, 2 ]
    ],
    numinfo := [
        [ 6, 1, 7, 5, 8, 14, 9, 16, 10, 7 ],
        [ 11, 22, 12, 58, 13, 90, 14, 78, 15, 7 ],
        [ 72, 13 ]
    ],
    projinds := [ 940, 202, 1211, 1238, 1258, 1327, 1483, 2308 ],
    projdata := [
        [ 9, 3, 1, 2, 2 ],
        [ 3, 2, 1, 4, 0 ],
        [ 10, 5, 1, 2, 1 ],
        [ 14, 6, 1, 2, 1 ],
        [ 13, 5, 2, 1, 0 ],
        [ 14, 4, 1, 2, 1 ],
        [ 15, 3, 1, 2, 2 ],
        [ 15, 2, 1, 4, 0 ]
    ],
    noether := [ 5, 6, 7 ],
    numerator := t^18 + t^16 + 3*t^15 + 5*t^14 + 6*t^13 + 10*t^12 + 12*t^11 + 
        14*t^10 + 14*t^9 + 14*t^8 + 12*t^7 + 10*t^6 + 6*t^5 + 5*t^4 + 3*t^3 + 
        t^2 + 1
    >

What do the fields mean?
Recall that the data is split up into large blocks, each containing
data for many K3 surfaces.  The blocks are indexed first by the GENUS,
which is an integer g >= -1.
For a fixed genus g, the K3 surfaces with that genus are listed
in order 1,2,3,...  according to their identifier i.
Smaller subdivisions of the data are made according to higher genuses,
in particular TWOGENUS and THREEGENUS.  The field 'genus1to5' holds all
genuses that we might use: [ genus, 2-genus, 3-genus, 4-genus, 5-genus ].

Fields 'weights', 'basket', 'noether', 'numerator' are unloaded
directly onto the K3 surface as they are.

'numinfo' contains coded information about a (usually large) polynomial.

The two remaining fields 'projinds', 'projdata' contain coded
information about both projections and unprojections.
The pair
    projinds[j], projdata[j]
together describe completely a projection or unprojection:
    projinds[j] is the identifier of a K3 surface Y of the same genus as X,
		which is a positive medium integer;
    projdata[j] is a sequence 4 small positive (or 0) integers
	[	codimension Y,
		index of the centre of projection in the basket of X,
		type of projection,
		subtype of projection	].
(It is easy to tell whether the j-th item is a projection or an
unprojection, since projections are ALWAYS to a surface Y having SMALLER
identifier.)
*/


/////////////////////////////////////////////////////////////////////
//		Translating between K3 surfaces and records
/////////////////////////////////////////////////////////////////////

intrinsic K3SurfaceToRecord(X::GRK3) -> Rec
{A record whose fields are a minimal collection of the attributes of
the K3 surface X}
    K3 := recformat<
	identifier : RngIntElt, genus1to5,weights,basket,numinfo,
	projinds,projdata,noether,numerator : SeqEnum >;
    Xrec := rec< K3 | >;
    Xrec`identifier := X`number;		// MedPosInt (in range 1..7000)
    Xrec`genus1to5 := InitialCoefficients(X)[2..6];	// [ MedPosInt ]
    Xrec`weights := Weights(X);			// [ SmallPosInt ]
    Xrec`basket := RawBasket(X);		// [ [SmallPosInt] ]
    Xrec`numinfo := NumeratorData(X);		// [ [MedPosInt] ]
    Xrec`noether := NoetherWeights(X);		// [ [SmallPosInt] ]
    Xrec`numerator := Eltseq(NoetherNumerator(X));	// THINK;
					// RngUPolElt (MedPosInt coeffs)
    // translate projection/unprojection data
    projinds := [Integers() | ];		// [ MedPosInt ]
    projdata := [ Parent([Integers()|]) | ];	// [ [ SmallPosInt ] ]
    for pr in Projections(X) cat Unprojections(X) do
        Append(~projinds,pr[1]);
	cod := pr[2];
        r := Index(pr[3]);
        a := Polarisation(pr[3])[1];
        type := pr[4];
	subtype := pr[5];
        Append(~projdata,[cod,r,a,type,subtype]);
    end for;
    Xrec`projinds  := projinds;
    Xrec`projdata  := projdata;
    return Xrec;
end intrinsic;

intrinsic K3Surface(X::Rec) -> GRK3
{A K3 surface made from the data of the record X}
    Y := HackobjCreateRaw(GRK3);
    Y`dim := 2;
    Y`number := X`identifier;
    Y`weights := X`weights;
    Y`rawbasket := X`basket;
    Y`noetherw := X`noether;
    Y`noethernseq := X`numerator;
    Y`numinfo := X`numinfo;
    // make projections and unprojections from coded data
    projinds := X`projinds;
    projdata := X`projdata;
    projs := [];
    for i in [1..#projinds] do
	pr := projdata[i];
        p := Point(r,[a,r-a]) where r is pr[2] where a is pr[3];
        Append(~projs, <projinds[i],pr[1],p,pr[4],pr[5]>);
    end for;
    PI := [ i : i in [1..#projinds] | projinds[i] lt X`identifier ];
    Y`proj := [ projs[i] : i in PI ];
    Y`unproj := [ projs[i] : i in [1..#projinds] | i notin PI ];
    return Y;
end intrinsic;


///////////////////////////////////////////////////////////////////////	
//	Writing a sequence of K3 surfaces to a text file
//
// This code is copied from ~bruce/databases/qmdb/write_info_file.m .
// To write a new data file in a magma session:
//		> WriteK3Data(Q,"newfilename");
// where Q is a sequence of K3 surfaces.
///////////////////////////////////////////////////////////////////////

forward ConstructData;
intrinsic WriteK3Data(Q::SeqEnum,F::MonStgElt)
{Write the K3 surfaces in the sequence Q of K3 surfaces to the file named F,
encoding each member as a record}
    Krec := [ K3SurfaceToRecord(X) : X in Q ];
    ConstructData(F,Krec);
end intrinsic;


/////////////////////////////////////////////////////////////////////
//			Write records to a file
/////////////////////////////////////////////////////////////////////

WriteHead := procedure(F)
    fprintf F, "T<t> := PolynomialRing(Rationals());\n";
    fprintf F, "GRK3 := recformat<\n";
    fprintf F, "identifier : RngIntElt,\n";
    fprintf F, "genus1to5,weights,basket,numinfo : SeqEnum,\n";
    fprintf F, "projinds,projdata,noether,numerator : SeqEnum >;\n";
    fprintf F, "data := [ Parent(rec< GRK3 | >) | ];\n";
end procedure;

// data is a sequence of records
ConstructData := procedure(F,data)
    WriteHead(F);
    for X in data do
	fprintf F, "r := rec< GRK3 | >;\n";
	if assigned X`identifier then
	    fprintf F, "r`identifier := %o;\n", X`identifier;
	end if;
	if assigned X`genus1to5 then
	    fprintf F, "r`genus1to5 := %o%o;\n", "\\", X`genus1to5;
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
	if assigned X`projinds then
	    fprintf F, "r`projinds := %o%o;\n", "\\", X`projinds;
	end if;
	if assigned X`projdata then
	    fprintf F, "r`projdata := %o;\n", X`projdata;
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

