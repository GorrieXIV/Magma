freeze;

import "BKLCdb4Q.m":GF4QIndex;
import "BKLCdb4Q.m":GF4QConstructionEnum;
import "BKLCdb4Q.m":GF4QMAXN;


forward QECCRecurse;
forward ReadEntry;
forward ReadObject;

forward ConcatenatedQuantumCode;

declare verbose BestCode,2;

is_export_version := IsExport();


/* compatibility with older versions */

words:=function(c,w:NumWords:=0,StoreWords:=true);
  a,b:=GetVersion();
  if b lt 12 then
    return Words(c,w:Cutoff:=NumWords);
  else
    return Words(c,w:NumWords:=NumWords);
  end if;
end function;

//////////////////////////// Assign MAXN /////////////////////////////////

function AssignMAXN(F)
    if is_export_version then
	sizes := {4};
    else
	sizes := {4};
    end if;

    q := #F;
    if q notin sizes then
	return 0, false;
    end if;

    case q:
	when 4:
	    MAXN := GF4QMAXN;
	else
	    error "Internal Error";
    end case;

    return MAXN, true;
end function;


///////////////////////////////////////////////////////////////////////////
///////////////////////////Cache functions////////////////////////////////
//////////////////////////////////////////////////////////////////////////

AddAttribute(SetEnum, "Codes");
AddAttribute(SetEnum, "Code_params");
AddAttribute(SetEnum, "Code_descs");
Code_cache := {Integers()|};
//Codes is a list of created codes
Code_cache`Codes := [* *];
//Code_params locates the created codes in the database's 3D array
Code_cache`Code_params := [ Parent(<1,2,3>) | ];
//Code_descs are strings describing the construction
Code_cache`Code_descs := [ Parent("") | ];

/* just for development
intrinsic ret_Code() -> .
{}
return Code_cache;
end intrinsic;
*/

///////////////////////////////////////

Display_Cache := procedure();
//for debugging, print the cache

    Codes := Code_cache`Codes;
    params := Code_cache`Code_params;
    descs := Code_cache`Code_descs;

    if #Codes ne #params or #params ne #descs then
        "Cache seq's have different lengths!!! ERROR!!!";
        "Codes",#Codes,Codes;
        "params",#params,params;
        "descs",#descs,descs;
        return;
    end if;

    "Codes",Codes:Minimal;
    "params",params;
    "descs",descs;

    for i in [1..#Codes] do
        "[" cat Sprint(i) cat "]: ";
        params[i], descs[i];  Codes[i]:Minimal;
    end for; 

end procedure;

///////////////////////////////

empty_Cache := procedure()
//empty the cache

    empty_Cache_sub := procedure(Code_cache);
        Code_cache`Code_params := [ Parent(<1,2,3>) | ];
        Code_cache`Codes := [* *];
        Code_cache`Code_descs := [* *];
    end procedure;

    empty_Cache_sub(Code_cache);

end procedure;

///////////////////////////////

get_Code_Index := function(C_params)
//return an index for the code to be used in the verbose printing
//give it a new one if none exists already

    add_Params_sub := procedure(Code_cache, C_params);

        CC := Code_cache`Codes;
        CC[#CC+1] := 0;      //this is a dummy value to signify uncreated
        Code_cache`Codes := CC;

        CP := Code_cache`Code_params;
        CP[#CP+1] := C_params;
        Code_cache`Code_params := CP;

        CD := Code_cache`Code_descs;
        CD[#CD+1] := "";
        Code_cache`Code_descs := CD;

    end procedure;

    num := Index(Code_cache`Code_params, C_params);
    if num ne 0 then
        return num;
    end if;

    add_Params_sub(Code_cache, C_params);

    return Index(Code_cache`Code_params, C_params);

end function;

////////////////////////////////////

add_Code := procedure(C_params,Code)
 //add a Code(or really any other object for that matter) to the cache
 //its parameters MUST already have been given an verbose list index

    add_Code_sub := procedure(Code_cache, Code, num)

        CC := Code_cache`Codes;
        CC[num] :=  Code;
        Code_cache`Codes := CC;

    end procedure;

    num := get_Code_Index(C_params);

        //Check that the code entry is not there yet
    if Type(Code_cache`Codes[num]) ne RngIntElt then
        error "INTERNAL ERROR: code being created twice";
    end if;

    add_Code_sub(Code_cache, Code, num);

end procedure;

////////////////////////////////////

check_Code := function(C_params)
//check if the code has already been created, 
//must already of been given an index

    num := get_Code_Index(C_params);

    if Type(Code_cache`Codes[num]) eq RngIntElt then
        return false, _;
    else
        return true, Code_cache`Codes[num];
    end if;

end function;

/////////////////////////////////////

ad := procedure(C_params, desc)

    add_desc_sub := procedure(Code_cache, desc, num);

        CD := Code_cache`Code_descs;
        CD[num] := desc;
        Code_cache`Code_descs := CD;

    end procedure;

    num := get_Code_Index(C_params);

    add_desc_sub(Code_cache, desc, num);

end procedure;

///////////////////////////////////////

//these functions are for convenient printing

/*
ad := procedure(C_params, descs)
//add a description as a list of objects to be printed

    //all integers are given a single space before them
    add_desc( C_params, &cat 
        [(Type(x) ne MonStgElt select " " else "") cat Sprint(x) : x in descs]);

end procedure;
*/

//////////////////////////////////////

/* this a a dodgy patch!!! fix up soon */

si := function(C_params)
//return the string of the code in index form: " [i]"

    return C_params;
    //return " [" cat Sprint(get_Code_Index(C_params)) cat "]";

end function;

si1 := function(C_params, num_descs)
//return the string of the code in index form: " [i]"

    return " [" cat Sprint(num_descs - get_Code_Index(C_params) + 1) cat "]";

end function;


print_verbose := procedure(Code_cache);

    Codes := Code_cache`Codes;
    descs := Code_cache`Code_descs;

    old_indent := GetIndent();
    SetIndent(8);

    for i in [#descs..1 by -1] do
        res := Codes[i];
        num := #descs - i + 1;
        str := "[" cat Sprint(num) cat "]:";
        if num lt 10 then
            str cat:= " "; //this is just so everything is aligned
        end if;
        if ISA(Type(res),Code) then
           str,res:Minimal;
        elif Type(res) eq ModMatFldElt then
           str,"Matrix of Dimensions",Nrows(res),"x",Ncols(res);
        elif Type(res) eq RngMPolElt then
            P := Parent(res);
            P1<[x]> := PolynomialRing( BaseRing(P) , Rank(P) );
            str,"Polynomial over",BaseRing(P),":",P1!res;
        elif Type(res) eq Crv then
            str,"Curve";
        else
            params := Code_cache`Code_params[i];
            str, "[" cat Sprint(params[1]) cat ", " cat
                            Sprint(params[2]) cat "] Code";
        end if;

        IndentPush();
    &cat [(Type(y) ne MonStgElt select " " else "") cat Sprint(y)
            where y := (Type(descs[i][j]) eq Tup and #descs[i][j] eq 3) 
                            select si1(descs[i][j], #descs) else descs[i][j] 
                                    : j in [1..#descs[i]]];

        IndentPop();
    end for;

    SetIndent(old_indent);

end procedure;


//---------------CodeEntry is a debugging function for the DB-------------//

intrinsic CodeEntryQECC(F::FldFin, n::RngIntElt,k::RngIntElt,i::RngIntElt) -> Code
{Returns the ith entry of length n and dimension k, which are
non-negative integers}

empty_Cache(); 


return QECCRecurse(F,< n,k,i >,0);
end intrinsic; 



///////////////////////////////////////////////////////////////////////////
////////////////// Quantum codes //////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

intrinsic BestKnownQuantumCode(F::FldFin,n::RngIntElt,k::RngIntElt) -> Code, BoolElt
{Returns the Best Known Quantum Code (of Maximal MinimumDistance)
of Length n and Dimension k over the finite field F.
The second return value
signals whether or not the desired code exists in the database.
If the code is not available then the second return value is false and
an irrelevant ZeroCode will be returned.

Note that binary quantum codes are accessed using the field GF(4),
since that is the alphabet under which they are represented};

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange k,0,n;

    return QECC(F, n, k);
end intrinsic;

intrinsic BKQC(F::FldFin,n::RngIntElt,k::RngIntElt) -> Code, BoolElt
{Returns the Best Known Quantum Code (of Maximal MinimumDistance)
of Length n and Dimension k over the finite field F.
The second return value
signals whether or not the desired code exists in the database.
If the code is not available then the second return value is false and
an irrelevant ZeroCode will be returned.

Note that binary quantum codes are accessed using the field GF(4),
since that is the alphabet under which they are represented};

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange k,0,n;

    return QECC(F, n, k);
end intrinsic;


intrinsic QECC(F::FldFin,n::RngIntElt,k::RngIntElt) -> Code, BoolElt
{Returns the Best Known Quantum Code (of Maximal MinimumDistance)
of Length n and Dimension k over the finite field F.
The second return value
signals whether or not the desired code exists in the database.
If the code is not available then the second return value is false and
an irrelevant ZeroCode will be returned.

Note that binary quantum codes are accessed using the field GF(4),
since that is the alphabet under which they are represented};

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange k,0,n;

    entry := ReadEntry(F,n,k);

    empty_Cache(); //need to empty before for saftey(possible interruptions etc)

    vprint BestCode: "Construction of a [[",n,",",k,",",entry[1],"]] Quantum Code:";

    res := QECCRecurse(F,<n,k, entry[3] >,0: Entry := entry);
                // the 3rd entry is the index of the best code

    //Display_Cache();  // this is for debugging

    if GetVerbose("BestCode") ge 1 then
        print_verbose(Code_cache);
    end if;

    empty_Cache(); //need to empty afterward so user can delete code

    if ISA(Type(res), Code) then
        return res, true;
    else
        return ZeroCode(F,n), false;
    end if;

end intrinsic;

//--------------------QECCLowerBound QECCUpperBound ----------------------//

intrinsic QECCLowerBound(F::FldFin,n::RngIntElt,k::RngIntElt) -> RngIntElt
{Returns the best known lower bound on the Maximal MinimumDistance of a 
Quantum Code of Length n and Dimension k over the finite field F.

Note that binary quantum codes are accessed using the field GF(4),
since that is the alphabet under which they are represented};

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;
    
    requirerange n,1,MAXN;
    requirerange k,0,n;

    entry := ReadEntry(F,n,k);

    return entry[1];
		// the 1st entry is the lb
end intrinsic;


intrinsic QECCUpperBound(F::FldFin,n::RngIntElt,k::RngIntElt) -> RngIntElt
{Returns the best known upper bound on the Maximal MinimumDistance of a 
Quantum Code of Length n and Dimension k over the finite field F.

Note that binary quantum codes are accessed using the field GF(4),
since that is the alphabet under which they are represented};

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange k,0,n;


    entry := ReadEntry(F,n,k);

    return entry[2];
		// the 2nd entry is the ub
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
/////////////////////////now for internals
////////////////////////////////////////////////////////////////////////////

QECCRecurse := function(F,C_params, ind: Entry := 0)
//Return the code in the [n][k][i]th position of the QECC table for F2

    n := C_params[1]; 
    k := C_params[2];  
    i := C_params[3];

    ind := 1;
    sp := "";

    C1 := 0; C2 := 0; C3 := 0; C4 := 0; C5 := 0;

                //check for trivial constructions first
 
    found,res := check_Code(C_params);
    if found then
        return res;
    end if;

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    case #F:            //now look in the table
        when 4:
            ConstructionEnum := GF4QConstructionEnum;
        else
            error "Database does not exist for GF(",#F,") currently";
    end case;

    F2:=GF(Isqrt(#F));

    if Type(Entry) eq RngIntElt then
        if n le MAXN then
            code := ReadEntry(F,n,k)[5][i];
        else
            code := ReadEntry(F,MAXN+1,0)[5][i];
        end if;
    else
        code := Entry[5][i];
    end if;

    params := code[6];
    ConstrNum := code[5];
    d := code[3];

    if ConstrNum eq 0 then
        //print code[4],n,k;   // this is the reference intitials
        //print code[4];
        ad(C_params, [* "Failed Construction" *] );
//        return code[4] cat " " cat IntegerToString(n) cat " " 
//                        cat IntegerToString(k) cat " " cat IntegerToString(d);
        return Sprintf("%3o %3o %3o %3o",code[4],n,k,d);
    end if;

    Construction := ConstructionEnum[ code[5] ];

    res := 0;

    case Construction:
        when "trivial":
            if k eq n then
                ad(C_params, [* "UniverseCode of length",n *]);
                res := QuantumCode(AdditiveZeroCode(F,F2,n));
            else
                print "Error for trivial";
            end if;

        when "shorten":
            if #params eq 2 then
                pos := params[2];
            else
                pos := { n+1 .. params[1][1] };
            end if;

            ad(C_params, [* "Shortening of",si(params[1])," at",pos *]);

            C1 := QECCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := ShortenCode( C1 , pos );
            end if;

        when "shorten_stabilizer":
            if #params eq 2 then
                pos := params[2];
            else
                pos := { n+1 .. params[1][1] };
            end if;

            ad(C_params, [* "Shortening of the stabilizer code of ",si(params[1])," at",pos *]);

            C1 := QECCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := QuantumCode(ShortenCode( StabilizerCode(C1), pos ));
            end if;

        when "puncture":
            if #params eq 2 then
                pos := params[2];
            else
                pos := { n+1 .. params[1][1] };
            end if;

            ad(C_params, [* "Puncturing of",si(params[1])," at",pos *]);

            C1 := QECCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := PunctureCode( C1, pos );
            end if;


        when "subcode":
            if #params eq 1 then
                ad(C_params, [* "Subcode of", si(params[1]) *]);
            elif #params eq 2 then
                ad(C_params, [* "Subcode of", si(params[1]),
                                " with ",params[2] *]);
            else
                error "subcode wrong params";
            end if;

            C1 := QECCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                if #params eq 1 then
                    res := Subcode( C1 , k );
                elif #params eq 2 then
                    res := Subcode( C1 , params[2] );
                else
                    error "subcode wrong params";
                end if;
            end if;

        when "extend":
            ad(C_params, [* "ExtendCode", si(params[1]),
                                        " by", n - params[1][1] *]);

            C1 := QECCRecurse(F, params[1],ind+1);

            if ISA(Type(C1),Code) then
                res := ExtendCode( C1 , n - Length(C1) );
            end if;

        when "standard_lengthening":
            ad(C_params, [* "standard lengthening of ", si(params[1]) *]);

            C1 := QECCRecurse(F, params[1],ind+1);

            if ISA(Type(C1),Code) then
                res := StandardLengthening( C1 );
            end if;

        when "gen":
            if Type(params[1]) cmpeq MonStgElt then
              ad(C_params,[* params[1] cat 
                             "\nConstruction from a stored generator matrix"*]);
              L := params[2];
            else
              ad(C_params,[* "Construction from a stored generator matrix"*]);
              L := params[1];
            end if;
            K := Universe(L);
            if Type(K) cmpne FldFin then
              K:=F;
            end if;
            G := Matrix(K,#L div n,n,L);
            c := AdditiveCode(F,G);
            res := QuantumCode( AdditiveCode(F2,G) );

        when "gen_field":
            ad(C_params,[* "Construction from a stored generator matrix"*]);
            K := GF(params[1]);
            if k gt n div 2 then
                G := KMatrixSpace(K,n-k,n) ! params[2];
                res := Dual( LinearCode(G) );
            else
                G := KMatrixSpace(K,k,n) ! params[2];
                res := LinearCode(G);
            end if;

        when "cyclic":
            K    := Universe(params[1]);
            if Type(K) cmpne FldFin then
              P := PolynomialRing(F); x := P.1;
              p := [P!x:x in params[1]];
              ad(C_params,[*"CyclicCode of length",n,
                                    " with generating polynomials",p *]);
            else
              P := PolynomialRing(K); x := P.1;
              p := P!params[1];
              ad(C_params,[*"CyclicCode of length",n,
                                    " with generating polynomial",p *]);
            end if;
            res := QuantumCode(AdditiveCyclicCode(F2,n,p));

        when "constacyclic":
            a :=params[1];
            Remove(~params,1);

            K    := Universe(params[1]);
            if Type(K) cmpne FldFin then
              P := PolynomialRing(F); x := P.1;
              p := [P!x:x in params[1]];
              ad(C_params,[*"ConstaCyclicCode generated by",
                   p, " with shift constant", a *]);
            else
              P := PolynomialRing(K); x := P.1;
              p := P!params[1];
              ad(C_params,[*"ConstaCyclicCode generated by",
                   p, " with shift constant", a *]);
            end if;
            res := QuantumCode(AdditiveConstaCyclicCode(F2,n,p,a));


        when "quasicyclic":
            P := PolynomialRing(Universe(params[1])); x := P.1;
            ad(C_params,[*"QuasiCyclicCode of length",n,
                            " with generating polynomials:"*] cat
                     Prune( &cat[ [* P!y, ", "*] : y in params ]) );

            res := QuantumCode(AdditiveQuasiCyclicCode(n, [P!y : y in params ] ));

        when "quasicyclic_field":
            P := PolynomialRing(Universe(params[1])); x := P.1;
            ad(C_params,[*"QuasiCyclicCode of length",n,
                            " with generating polynomials:"*] cat
                     Prune( &cat[ [* P!y, ", "*] : y in params ]) );

            res := QuasiCyclicCode(n, [P!y : y in params ] );

        when "quasicyclic_stack","quasicylic_stack":
            h := params[1];
            Remove(~params,1);
            P := PolynomialRing(Universe(params[1])); x := P.1;
            polys := [P!y : y in params ];
            ad(C_params,[*"QuasiCyclicCode of length",n,
                " stacked to height",h," with generating polynomials:"*] cat
                    Prune( &cat[ [* P!y, ", "*] : y in params ]) );

            res := QuantumCode(AdditiveQuasiCyclicCode(n,polys,h));

        when "quasitwistedcyclic":
            a := params[1];
            Remove(~params,1);
            V:=KSpace(GF(#F^2),#params[1]);
            ad(C_params,[*"QuasiTwistedCyclicCode of length",n,
                                " and constant",a," with generators:"*] cat
                    Prune( &cat[ [* V!v, ", "*] : v in params ]) );

            res := QuantumCode(AdditiveQuasiTwistedCyclicCode(F2,[V!v:v in params],a));

        when "quantumtwisted":
            A := params[1];
            kappa := params[2];
            ad(C_params,[*"Quantum Twisted Code of length",n,
                                " with interval",A," and parameter kappa",kappa*] );

            res := QuantumTwistedCode(F,n,A,kappa);

         when "concat":
            ad(C_params,[*"Concatenation of",si(params[1])," and",
                            si(params[2]) *]);;

            C1 := QECCRecurse(F,params[1],ind+1);
            C2 := QECCRecurse(F,params[2],ind+1);
            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
               res := ConcatenatedQuantumCode(C1,C2);
            end if;


         when "mat":
            res := KMatrixSpace(Universe(params[1]),k,n) ! params[1];
            ad(C_params,[* "Stored Matrix:" ,res *]);
            

            
/////////////////////////////////////////////////////////////////////////////
        else
            error "Unknown Construction",Construction;
    end case;


    if ISA(Type(res),Code) then
        if d ne 0 then
            if assigned res`MinimumWeight and res`MinimumWeight ne d then
                print "Incorrect MinimumWeight Error:",[n,k,res`MinimumWeight];
                print "Possibly caused by an incorrect user defined MinimumWeight Attribute";
            elif res`MinimumWeightLowerBound gt d then
                print "Incorrect MinimumWeightLowerBound Error:",[n,k,res`MinimumWeightLowerBound];
                print "Possibly caused by an incorrect user defined MinimumWeight Attribute";
            elif res`MinimumWeightUpperBound lt d then
                print "Incorrect MinimumWeightUpperBound Error:",[n,k,res`MinimumWeightUpperBound];
                print "Possibly caused by an incorrect user defined MinimumWeight Attribute";
            else
                res`MinimumWeight := d;
            end if;
        end if;

        add_Code(C_params,res);

    elif ISA(Type(res), ModMatFldElt) then
        add_Code(C_params,res);
    elif ISA(Type(res), RngMPolElt) then
        add_Code(C_params,res);
    elif ISA(Type(res), Crv) then
        add_Code(C_params,res);
    

    elif Type(res) ne RngIntElt then
            //if its not one of the above catered for types then it should
            //still be the res := 0 it was initialised with
        error "UNCHECKED TYPE RETURNED!!! ::",Type(res);
    else
            //this is a bit dodgy
        if Type(C1) eq MonStgElt then
            res := C1;
        elif Type(C2) eq MonStgElt then
            res := C2;
        elif Type(C3) eq MonStgElt then
            res := C3;
        elif Type(C4) eq MonStgElt then
            res := C4;
        elif Type(C5) eq MonStgElt then
            res := C5;
        end if;
    end if;


    return res;
end function;
 
intrinsic ReadEntryQECC(F::FldFin, n::RngIntElt,k::RngIntElt) -> Any
{read the data from the n,k -th entry in the code database}
  return ReadEntry(F,n,k);
end intrinsic;

ReadEntry := function(F,n,k)
//read the n,k entry from the binary file

        //change this flag if using the internal package version

    use_lib := is_export_version;
    DATA := "/home/grassl/BKLC/export/";
    Open := LibFileOpen;

    if use_lib then
	BinFilePath := GetLibraryRoot() cat "/data/BKLC/";
    else
	BinFilePath := DATA;
    end if;

    BinFilePath cat:= "BKLCbi" cat IntegerToString(#F) cat "Q.dat";
    BinFile := Open(BinFilePath, "rb");

    case #F:
	when 4: Index := GF4QIndex;
    else
	error "Internal Error";
    end case;

    Seek(BinFile,Index[n][k+1], 0 );

    len := Seqint( ReadBytes(BinFile,2) ,256);

    Bytes := ReadBytes(BinFile,len);

    Offset := 1;

    res:=0;
    ReadObject(~Bytes,~Offset,~res);

    return res;
    
end function;



ReadObject := procedure(~Bytes,~Offset,~res)
//Read in the object contained at Offset in Bytes

    set := false;
 
    case Bytes[Offset]:
 
        when 1:
 
            sign := Bytes[Offset+1];
            len := Seqint(Bytes[Offset+2..Offset+3],256);
 
            Offset +:= 4;
            res:= Seqint(
                    [Bytes[i]:i in [Offset..Offset+len-1]]
                        ,256);
 
            Offset +:= len;
            if sign eq 0 then
                res *:= -1;
            end if;
 
            return;
 
        when 2:
 
            len := Seqint(Bytes[Offset+1..Offset+2],256);
 
            Offset +:= 3;
            res:=&cat[CodeToString(Bytes[i]):i in [Offset..Offset+len-1]];
            if Type(res) eq SeqEnum then
                res := "";
            end if;

            Offset +:= len;
 
            return;
 
        when 3:
            res := [];
            set := true;
 
        when 4:
            res := [];
 
        when 5:
            res := <>;
 
        when 6:
            res := [**];

        when 7:
            p := Bytes[Offset+1];
            k := Bytes[Offset+2];
            K := GF(p,k);
            res := [ K |];

// bug fix M. Grassl, 08.01.2003:
// problem: the defining polynomial of a finite field is not fix
// solution: use the root of the ConwayPolynomial as base for the dLog

            w := Roots(ConwayPolynomial(p,k),GF(p,k))[1,1];

//          w := K.1;

            len := Seqint(Bytes[Offset+3..Offset+4],256);

            Offset +:= 5;

            if p ne 2 then
               blen := Ceiling(1+Log(256,p^k));
                     // number of bytes used for the exponent

                     //read in the exponents of length k
                for i in [1..len] do
                    exp := Seqint( Bytes[Offset+blen*(i-1)..Offset+blen*i-1] , 256 );
                    if exp eq 0 then
                	res[i] := 0;
                    else
                	res[i] := w^(exp-1);
                    end if;
                end for;

                Offset +:= len * blen;

            else
                ByteLen := len*k;
                if (ByteLen mod 8) ne 0 then
                    ByteLen +:= 8-(ByteLen mod 8);
                end if;
	        
                ByteLen div:= 8;
	        
                    //transfer the bytes back into bits
                Bits := [];
                for i in [0..ByteLen-1] do
                    Bits cat:= Intseq(Bytes[Offset+i],2,8);
                end for;
	        
                Offset +:= ByteLen;
	        
                    //read in the exponents of length k
                for i in [1..len] do
                    exp := Seqint( Bits[k*(i-1)+1..k*i] , 2 );
                    if exp eq 0 then
                	res[i] := 0;
                    else
                	res[i] := w^(exp-1);
                    end if;
                end for;
            end if;
            return;

        when 8:

            p := Bytes[Offset+1];
            k := Bytes[Offset+2];

            K := GF(p,k);
            len := Bytes[Offset+3]; 
            Offset +:= 4;
            exp:= Seqint(
                    [Bytes[i]:i in [Offset..Offset+len-1]]
                        ,256);
 
            Offset +:= len;
// bug fix M. Grassl, 08.01.2003:
// problem: the defining polynomial of a finite field is not fix
// solution: use the root of the ConwayPolynomial as base for the dLog

            w := Roots(ConwayPolynomial(p,k),K)[1,1];
//          res := (K.1)^(exp-1);
            res := w^(exp-1);
 
            return;

        else
            print "ERROR, Unknown datatype:",Bytes[Offset];

    end case;
 
    len := Seqint(Bytes[Offset+1..Offset+2],256);
 
    Offset +:= 3;
    tempres := 0;
    for i in [1..len] do
        ReadObject(~Bytes,~Offset,~tempres);
        Append(~res, tempres );
    end for;
 
    if set eq true then
        res := SequenceToSet(res);
    end if;
 
    return;
 
end procedure;


ConcatenatedQuantumCode:=function(C1,C2);
  if not Dimension(C2) eq 1 then
    error "only implemented for codes C2 of dimension 1";
  end if;
  s2:=StabilizerCode(C2);
  n2:=NormalizerCode(C2);
  ops2:=GeneratorMatrix(CodeComplement(n2,s2));
  g0:=DirectSum([s2:i in [1..Length(C1)]]);
  g1:=Matrix([&cat[Eltseq(Vector(Eltseq(x))*ops2):x in Eltseq(g)]:g in Generators(StabilizerCode(C1))]);
  g:=g0+AdditiveCode(g1);

  return QuantumCode(g);

end function;
