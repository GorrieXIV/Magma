freeze;

import "BKLCdb2.m":GF2Index;
import "BKLCdb2.m":GF2ConstructionEnum;
import "BKLCdb2.m":GF2MAXN;

import "BKLCdb3.m":GF3Index;
import "BKLCdb3.m":GF3ConstructionEnum;
import "BKLCdb3.m":GF3MAXN;

import "BKLCdb4.m":GF4Index;
import "BKLCdb4.m":GF4ConstructionEnum;
import "BKLCdb4.m":GF4MAXN;

import "BKLCdb5.m":GF5Index;
import "BKLCdb5.m":GF5ConstructionEnum;
import "BKLCdb5.m":GF5MAXN;

import "BKLCdb7.m":GF7Index;
import "BKLCdb7.m":GF7ConstructionEnum;
import "BKLCdb7.m":GF7MAXN;

import "BKLCdb8.m":GF8Index;
import "BKLCdb8.m":GF8ConstructionEnum;
import "BKLCdb8.m":GF8MAXN;

import "BKLCdb9.m":GF9Index;
import "BKLCdb9.m":GF9ConstructionEnum;
import "BKLCdb9.m":GF9MAXN;


forward BKLCRecurse;
forward ReadEntry;
forward ReadEntryFlag;
forward ReadObject;

forward ConstructionB2Code;
forward ConstructionB2Code1;
forward OctalStringToPoly;
forward OctalChenCode;
forward SugiyamaCode;
forward SugiyamaCodeQ;
forward PGCode;
forward PGCode1;
forward MarutaCode;
forward MarutaCode1;
forward MarutaCode2;

declare verbose BestCode,2;

S2L := SequenceToList;

is_export_version := IsExport();


/* compatibility with older versions */

words:=function(c,w:NumWords:=0,StoreWords:=true);
  a,b:=GetVersion();
  if b lt 12 then
    return Words(c,w:Cutoff:=NumWords);
  else
//c:Minimal;
//printf "searching for a word of weight %o\n",w;
//set a fixed seed value fater storing the actual value
    s1,s2:=GetSeed();
    SetSeed(1);
    www:=Words(c,w:NumWords:=NumWords,Method:="Zimmermann");
//printf "support: %o\n",Support(Rep(www));
    SetSeed(s1,s2);
    return www;
  end if;
end function;

//////////////////////////// Assign MAXN /////////////////////////////////

function AssignMAXN(F)
    if is_export_version then
	sizes := {2,3,4,5,7,8,9};
    else
	sizes := {2,3,4,5,7,8,9};
    end if;

    q := #F;
    if q notin sizes then
	return 0, false;
    end if;

    case q:
	when 2:
	    MAXN := GF2MAXN;
	when 3:
	    MAXN := GF3MAXN;
	when 4:
	    MAXN := GF4MAXN;
	when 5:
	    MAXN := GF5MAXN;
	when 7:
	    MAXN := GF7MAXN;
	when 8:
	    MAXN := GF8MAXN;
	when 9:
	    MAXN := GF9MAXN;
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

//these functions are for convinient printing

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
        elif ISA(Type(res),Crv) then
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

intrinsic CodeEntry(F::FldFin, n::RngIntElt,k::RngIntElt,i::RngIntElt) -> Code
{Returns the ith entry of length n and dimension k, which are
non-negative integers}

empty_Cache(); 

if k eq 0 then
    return ZeroCode(F,n);
end if;
    //this is a little bit dodgy, but easier than adding a zero row
    //into the database

return BKLCRecurse(F,< n,k,i >,0);
end intrinsic; 



//--------------------BKLCLowerBound BKLCUpperBound ----------------------//

intrinsic BKLCLowerBound(F::FldFin,n::RngIntElt,k::RngIntElt) -> RngIntElt
{Returns the best known lower bound on the Maximal MinimumDistance of a 
Linear Code 
of Length n and Dimension k over the finite field F}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;
    
    requirerange n,1,MAXN;
    requirerange k,0,n;

    if k eq 0 then
	return n;
    end if;
	//this is a little bit dodgy, but easier than adding a zero row
	//into the database

    entry := ReadEntry(F,n,k);

    return entry[1];
		// the 1st entry is the lb
end intrinsic;


intrinsic BKLCUpperBound(F::FldFin,n::RngIntElt,k::RngIntElt) -> RngIntElt
{Returns the upper bound on the MinimumDistance of a Linear Code   
of Length n and Dimension k over the finite field F}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange k,0,n;


    if k eq 0 then
	return n;
    end if;
	//this is a little bit dodgy, but easier than adding a zero row
	//into the database

    entry := ReadEntry(F,n,k);

    return entry[2];
		// the 2nd entry is the ub
end intrinsic;

//---------------BLLCUpperBound BLLCLowerBound -----------------//
//--------------Bounds on the minimum length for given k,d ----------------//

intrinsic BLLCUpperBound(F::FldFin,k::RngIntElt,d::RngIntElt) -> RngIntElt
{Returns the best known upper bound on the minimum possible Length for 
which a Linear Code 
of Dimension k over the finite field F has MinimumDistance >= d. If the 
length required is > 256, then it is not available, and the value 0 
will be returned }

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange k,0,MAXN;
    requirerange d,1,MAXN;

    for n in [Max(1,k)..MAXN] do
	entry := ReadEntry(F,n,k);
	    //entry[1] is the LowerBound
	if entry[1] ge d then
	    return n;
	end if;
    end for;

    return 0;

end intrinsic;

intrinsic BLLCLowerBound(F::FldFin,k::RngIntElt,d::RngIntElt) -> RngIntElt
{Returns the lower bound on the Length for which a Linear Code
of Dimension k over the finite field F has MinimumDistance >= d. If the
length required is > 256, then it is not available, and the value 0
will be returned }

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange k,0,MAXN;
    requirerange d,1,MAXN;

    for n in [Max(1,k)..MAXN] do
	entry := ReadEntry(F,n,k);
	    //entry[2] is the UpperBound
	if entry[2] ge d then
	    return n;
	end if;
    end for;

    return 0;

end intrinsic;

//----------------- BestLengthLinearCode BLLC ------------------------//
//------- Known/available code of minimal length for given k,d--------// 

intrinsic BestLengthLinearCode(F::FldFin,k::RngIntElt,d::RngIntElt)
                                                    -> Code, BoolElt
{Returns a Code of Dimenson k and MinimumDistance >=d over the finite field F
with the minimum known possible Length. If the required code has Length >=
256 then it is not available and the Boolean value will return false (along
with an irrelevant ZeroCode),
otherwise the boolean return value will be true}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange k,1,MAXN;
    requirerange d,1,MAXN;

    return BLLC(F,k,d);
end intrinsic;

intrinsic BLLC(F::FldFin,k::RngIntElt,d::RngIntElt) -> Code,BoolElt
{Returns a Code of Dimenson k and MinimumDistance >=d over the finite field F
with the minimum known possible Length. If the required code has Length >=
256 then it is not available and the Boolean value will return false (along
with an irrelevant ZeroCode),
otherwise the boolean return value will be true}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange k,1,MAXN;
    requirerange d,1,MAXN;

    if k eq 0 then
	return ZeroCode(F, d), true;
    end if;

    for n in [Max(1,k)..MAXN] do
	entry := ReadEntry(F,n,k);
	    //entry[1] is the LowerBound
	if entry[1] ge d then
//	    C, is_code := BKLC(F,n,k);
	    C := BKLC(F,n,k);
            is_code:=ISA(Type(C),Code);
	    if is_code then
		return C,true;
	    else
		break;
	    end if;
	end if;
    end for;

    return ZeroCode(F,257),false;

end intrinsic;

//--------------- BDLCLowerBound BDLCUpperBound ---------//
//--------------Bounds on the maximum possible dimension for a given n,d---//

intrinsic BDLCLowerBound(F::FldFin,n::RngIntElt,d::RngIntElt) 
                                                            -> RngIntElt
{Returns the best known lower bound on the maximum possible Dimension 
for which
a Linear Code of Length n over the finite field F 
has MinimumDistance >= d}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,0,MAXN;
    requirerange d,1,n;

    for k in [n..1 by -1] do
	entry := ReadEntry(F,n,k);
	    //entry[1] is the LowerBound
	if entry[1] ge d then
	    return k;
	end if;
    end for;

    print "Internal Error";
    return 0;

end intrinsic;

intrinsic BDLCUpperBound(F::FldFin,n::RngIntElt,d::RngIntElt)
                                                            -> RngIntElt
{Returns the best known upper bound on the Dimension for which
a Linear Code of Length n over the finite field F
has MinimumDistance >= d}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,0,MAXN;
    requirerange d,1,n;

    for k in [n..1 by -1] do
	entry := ReadEntry(F,n,k);
	    //entry[2] is the UpperBound
	if entry[2] ge d then
	    return k;
	end if;
    end for;

    print "Internal Error";
    return 0;

end intrinsic;

//----------------------BestDimensionLinearCode BDLC---------------------//

intrinsic BestDimensionLinearCode(F::FldFin,n::RngIntElt,d::RngIntElt)
                                                        -> Code, BoolElt
{Returns a Code of Length n and MinimumDistance >=d over the finite field F
with the largest known possible Dimension. The second return value
signals whether or not the desired code exists in the database.
If the code is not available then the second return value is false and
an irrelevant ZeroCode will be returned.}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange d,1,n;

    return BDLC(F,n,d);
end intrinsic;

intrinsic BDLC(F::FldFin,n::RngIntElt,d::RngIntElt)  -> Code, BoolElt
{Returns a Code of Length n and MinimumDistance >=d over the finite field F
with the largest known possible Dimension. The second return value
signals whether or not the desired code exists in the database.
If the code is not available then the second return value is false and
an irrelevant ZeroCode will be returned.}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange d,1,n;

    for k in [n..1 by -1] do
	entry := ReadEntry(F,n,k);
	    //entry[1] is the LowerBound
	if entry[1] ge d then
//	    C, is_code := BKLC(F,n,k);
	    C := BKLC(F,n,k);
            is_code:=ISA(Type(C),Code);
	    if is_code then
		return C, true;
	    else
              if is_export_version then
          	return ZeroCode(F,n),false;
              else
          	return ZeroCode(F,n),false,Sprintf("%3o %3o %3o %3o",C,n,k,d);
              end if;
	    end if;
	end if;
    end for;

    print "Internal Error"; //This should never be reached, as k = 1
			    //has d = n
    return ZeroCode(F,n), false;

end intrinsic;

//---------------------BestKnownLinearCode BKLC ---------------------//

intrinsic BestKnownLinearCode(F::FldFin,n::RngIntElt,k::RngIntElt) 
							-> Code, BoolElt
{Returns the Best Known Linear Code (of Maximal MinimumDistance)
of Length n and Dimension k over the finite field F.
The second return value
signals whether or not the desired code exists in the database.
If the code is not available then the second return value is false and
an irrelevant ZeroCode will be returned.}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange k,0,n;

    return BKLC(F,n,k);
end intrinsic;

intrinsic BKLC(F::FldFin,n::RngIntElt,k::RngIntElt) -> Code, BoolElt
{Returns the Best Known Linear Code (of Maximal MinimumDistance)
of Length n and Dimension k over the finite field F.
The second return value
signals whether or not the desired code exists in the database.
If the code is not available then the second return value is false and
an irrelevant ZeroCode will be returned.}

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    requirerange n,1,MAXN;
    requirerange k,0,n;

    if k eq 0 then
        vprint BestCode: "ZeroCode of length",n;
        return ZeroCode(F,n), true;
    end if;
        //this is a little bit dodgy, but easier than adding a zero row
        //into the database

    entry := ReadEntry(F,n,k);

    empty_Cache(); //need to empty before for saftey(possible interruptions etc)

    vprint BestCode: "Construction of a [",n,",",k,",",entry[1],"] Code:";

    res := BKLCRecurse(F,<n,k, entry[3] >,0: Entry := entry);
                // the 3rd entry is the index of the best code

    //Display_Cache();  // this is for debugging

    if GetVerbose("BestCode") ge 1 then
        print_verbose(Code_cache);
    end if;

    empty_Cache(); //need to empty afterward so user can delete code

    if ISA(Type(res), Code) then
        return res, true;
    else
      if is_export_version then
  	return ZeroCode(F,n),false;
      else
//  	return Sprintf("%3o %3o %3o %3o",res,n,k,BKLCLowerBound(F,n,k));
  	return ZeroCode(F,n),false,res;
      end if;
    end if;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////
/////////////////////////now for internals
////////////////////////////////////////////////////////////////////////////

BKLCRecurse := function(F,C_params, ind: Entry := 0)
//Return the code in the [n][k][i]th position of the BKLC table for F

    n := C_params[1]; 
    k := C_params[2];  
    i := C_params[3];

    ind := 1;
    sp := "";

    C1 := 0; C2 := 0; C3 := 0; C4 := 0; C5 := 0;

                //check for trivial constructions first
                //Zerocode is only possible code for k eq 0
    if k eq 0 then
        ad(C_params, [* "ZeroCode of length",n *]);
        return ZeroCode(F,n);
    end if;

    found,res := check_Code(C_params);
    if found then
        return res;
    end if;

    MAXN, is_valid := AssignMAXN(F);
    if not is_valid then
        error "Database does not exist for GF(",#F,") currently";
    end if;

    case #F:            //now look in the table
        when 2:
            ConstructionEnum := GF2ConstructionEnum;
        when 3:
            ConstructionEnum := GF3ConstructionEnum;
        when 4:
            ConstructionEnum := GF4ConstructionEnum;
        when 5:
            ConstructionEnum := GF5ConstructionEnum;
        when 7:
            ConstructionEnum := GF7ConstructionEnum;
        when 8:
            ConstructionEnum := GF8ConstructionEnum;
        when 9:
            ConstructionEnum := GF9ConstructionEnum;
        else
            error "Database does not exist for GF(",#F,") currently";
    end case;


    if Type(Entry) eq RngIntElt then
        if n le MAXN then
            code := ReadEntry(F,n,k)[5][i];
        else
            code := ReadEntry(F,MAXN+1,1)[5][i];
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
            if k eq 1 then
                ad(C_params, [* "RepetitionCode of length",n *]);
                res := RepetitionCode(F,n);             
            elif k eq n then
                ad(C_params, [* "UniverseCode of length",n *]);
                res := UniverseCode(F,n);
            else
                print "Error for trivial";
            end if;

        when "Universe_field":
            ad(C_params, [* "UniverseCode of length",n,
                            " over GF(",params[1],")" *]);
            res := UniverseCode(GF(params[1]),n);

        when "dual-all-1":
            ad(C_params, [* "Dual of the RepetitionCode of length",n *] );
            res := Dual(RepetitionCode(F,n));           

        when "shorten":
            if #params eq 2 then
                pos := params[2];
            else
                pos := { n+1 .. params[1][1] };
            end if;

            ad(C_params, [* "Shortening of",si(params[1])," at",pos *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := ShortenCode( C1 , pos );
            end if;

        when "puncture":
            if #params eq 2 then
                pos := params[2];
            else
                pos := { n+1 .. params[1][1] };
            end if;

            ad(C_params, [* "Puncturing of",si(params[1])," at",pos *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := PunctureCode( C1, pos );
            end if;

        when "find_puncturing":
            C1 := BKLCRecurse(F,params[1],ind+1);
            n0 := Length(C1);
            mw := MinimumWords(C1:Method:="Zimmermann");
            supp := {{1..n0} diff Support(x):x in mw};

            if #params eq 2 then
                pos := params[2];
            else
                pos := { n+1 .. params };
            end if;
            //first try the stored positions
            if exists{s:s in supp|s meet pos eq {}} then
              if n0-n eq 1 then
                pos := rep{{x1}:x1 in {1..n0}|not exists{s:s in supp|s meet {x1} eq {}}};
              elif n0-n eq 2 then 
                pos := rep{{x1,x2}:x2 in {x1+1..n0},x1 in {1..n0}|not exists{s:s in supp|s meet {x1,x2} eq {}}};
              elif n0-n eq 3 then 
                pos := rep{{x1,x2,x3}:x3 in {x2+1..n0},x2 in {x1+1..n0},x1 in {1..n0}|
                               not exists{s:s in supp|s meet {x1,x2,x3} eq {}}};
              elif n0-n eq 4 then 
                pos := rep{{x1,x2,x3,x4}:x4 in {x3+1-n0},x3 in {x2+1..n0},x2 in {x1+1..n0},x1 in {1..n0}|
                               not exists{s:s in supp|s meet {x1,x2,x3,x4} eq {}}};
              elif n0-n eq 5 then 
                pos := rep{{x1,x2,x3,x4,x5}:x5 in {x4+1..n0},x4 in {x3+1-n0},x3 in {x2+1..n0},x2 in {x1+1..n0},x1 in {1..n0}|
                               not exists{s:s in supp|s meet {x1,x2,x3,x4,x5} eq {}}};
              else
                pos := rep{x:x in Subsets({1..n0},n0-n)|not exists{s:s in supp|s meet x eq {}}};
              end if; 
            end if;

            ad(C_params, [* "Puncturing of",si(params[1])," at",pos *]);

            if ISA(Type(C1),Code) then
                res := PunctureCode( C1, pos );
            end if;

        when "puncture_matrix":
            //this will remove the columns of a matrix
            //must give a set of integers

            ad(C_params, [* "Puncture the matrix",si(params[1]),
                                        " at", params[2] *] );

            C1 := BKLCRecurse(F, params[1],ind+1);

            par := Reverse(Sort(SetToSequence(params[2])));
                    //make sure do higher ones 1st

            if Type(C1) eq ModMatFldElt then
                res := C1;
                for j in par do
                    M1 := Submatrix(res,1,1,k,j-1);
                    M2 := Submatrix(res,1,j+1,k,NumberOfColumns(res)-j);
                    res := HorizontalJoin(M1,M2);
                end for;
            end if;

        when "extend":
            ad(C_params, [* "ExtendCode", si(params[1]),
                                        " by", n - params[1][1] *]);

            C1 := BKLCRecurse(F, params[1],ind+1);

            if ISA(Type(C1),Code) then
                res := ExtendCode( C1 , n - Length(C1) );
            end if;

//added by M. Grassl
        when "add_column":
            C1 := BKLCRecurse(F, params[1],ind+1);
            vec := params[2];
            K_ := Universe(vec);
            if Type(K_) cmpne FldFin then
              K_ := F;
            end if;
            vec := KSpace(K_,#vec)!vec;

            if ISA(Type(C1),Code) then
                ad(C_params, [* "Append to the code",si(params[1]),
                            " the column vector ", vec *]);
                gen := GeneratorMatrix(C1);
                col := KMatrixSpace(K_,Dimension(C1),1)!Eltseq(vec);
                res := LinearCode( HorizontalJoin(gen,col) );
            else
                ad(C_params, [* "Append a column vector to ",si(params[1])*]);
            end if;

        when "constructionB":
            ad(C_params, [* "Construction B of",si(params[1]) *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                if #params eq 1 then
                    res := ConstructionB2Code(C1,Length(C1)-n,0,sp);
                else
//                    res := ConstructionB2Code1(C1,Length(C1)-n,0,params[2],sp);
                    res := ShortenCode(C1,params[2]);
//some checking added
                    if Dimension(res) ne k then //wrong index set for shortening
                      res := ConstructionB2Code(C1,Length(C1)-n,0,sp);
                    end if;
                end if;
            end if;

        when "(u|u+v)":
            ad(C_params, [* "PlotkinSum of",si(params[1])," and",
                                            si(params[2]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
                res :=  PlotkinSum( C1 , C2 );
            end if;

        when "(u|u-v|u+v+w)":
            ad(C_params, [* "PlotkinSum of",si(params[1]),
                                si(params[2]), " and", si(params[3]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            C3 := BKLCRecurse(F,params[3],ind+1);

            if ISA(Type(C1),Code) and ISA(Type(C2),Code)
                                and ISA(Type(C3),Code) then
                res := PlotkinSum( C1, C2, C3);
            end if;


        when "concatenation":
            ad(C_params, [* "Juxtaposition of",si(params[1])," and ",
                                    si(params[2]) *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
                res := Juxtaposition( C1, C2);
            end if;

        when "residue":
            ad(C_params, [* "ResidueCode of", si(params[1]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                if #params eq 1 then
                    res := ResidueCode( C1 );
                else
                    print "Error";
                end if;
            end if;

        when "generalized_residue":
            if #params eq 1 then
              ad(C_params, [* "generalized residue code of", si(params[1]), 
                    "\npuncturing at the support of a word of weight", params[1,1]-n*]);
            else
              ad(C_params, [* "generalized residue code of", si(params[1]), 
                    "\npuncturing at the support of a word of weight", params[2]*]);
            end if;
            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                if #params eq 1 then
                    w := Rep(Words(C1,Length(C1)-n:NumWords:=1));
                    res := PunctureCode( C1, Support(w) );
                elif #params eq 2 then
                   ad(C_params, [* "puncturing at the support of a word of weight", params[2] *]);
                    w := Rep(Words(C1,params[2]:NumWords:=1));
                    res := PunctureCode( C1, Support(w) );
                else
                    print "Error";
                end if;
            end if;

        when "constructionB2":
            ad(C_params, [* "Construction B2 of", si(params[1]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);

            if ISA(Type(C1),Code) then
                if #params eq 3 then
                    res := ConstructionB2Code(C1,params[2],params[3],sp);
                elif #params eq 4 then
                    res:= ConstructionB2Code1(C1,params[2],params[3],params[4],sp);
                end if;
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

            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                if #params eq 1 then
                    res := Subcode( C1 , k );
                elif #params eq 2 then
                    res := Subcode( C1 , params[2] );
                else
                    error "subcode wrong params";
                end if;
            end if;

        when "lengthening":
            delta_n := n - params[1][1];
            ad(C_params, [* "PadCode",si(params[1])," by ",delta_n *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := PadCode( C1 , delta_n );
            end if;

//Codes from here are the non-automatic ones (not downloaded from Brouwer)

        when "sum":
                //params can be any length
            ad(C_params, [* "The Vector space sum:",si(params[1]) *] cat
                    &cat [ [*" +",si(params[i])*] : i in [2..#params] ] );
                         

            S := S2L([ BKLCRecurse(F,params[i],ind+1) : i in [1..#params] ]);



            AreCodes := true;
            for c in S do
                if not ISA(Type(c),Code) then
                    AreCodes := false;
                end if;
            end for;

            if AreCodes eq true and #S ne 0 then
                res := S[1];
                for i in [2..#S] do
                    res +:= S[i];
                end for;
            end if;

        when "gen":
            if Type(params[1]) eq Tup then
                ad(C_params, [* "Code from generator matrix",si(params[1]) *]);
                G := BKLCRecurse(F,params[1],ind+1);
                res := LinearCode(G);
            else
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
                if k gt n div 2 then

                        G := KMatrixSpace(K,n-k,n) ! L;
                        res := Dual( LinearCode(G) );
                    else
                        G := KMatrixSpace(K,k,n) ! L;
                        res := LinearCode(G);
                    end if;
                end if;

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


        when "OctalChen":
            ad(C_params,[* "QuasiCyclicCode of length",params[1],
                            " with Generating Polynomials (in octal):\n",
                                    params[2] *] );

            res := OctalChenCode(params[1],params[2]);

        when "BCH":
            if #params eq 2 then
                ad(C_params,[*"BCHCode with parameters",params[1],params[2]*]);
                res := BCHCode( F,params[1],params[2]);
            elif #params eq 3 then
                ad(C_params,[*"BCHCode with parameters",
                                        params[1],params[2],params[3] *]);
                res := BCHCode( F,params[1],params[2],params[3]);
            else
                print "Error";
            end if;

        when "BCH_field":
            if #params eq 3 then
                ad(C_params,[*"BCHCode over GF(",params[1],
                                ") with parameters",params[2],params[3] *]);
                res := BCHCode(GF(params[1]),params[2],params[3]);
            elif #params eq 4 then
                ad(C_params,[*"BCHCode over GF(",params[1],
                        ") with parameters",params[2],params[3],params[4] *]);
                res := BCHCode(GF(params[1]),params[2],params[3],params[4]);
            else
                //ERROR
            end if;

// Should kill both BCH256 AND XBCH.. use Temp codes
        when "BCH256":
                //should i allow specification of puncture position????
            ad(C_params,[*"Puncturing of BCHCode with parameters",
                                params[1],params[2]," at 257" *]);

            res := PunctureCode(
                    BCHCode(F,params[1],params[2],params[3]),257
                                );

        when "XBCH":
            if #params eq 1 then
                ad(C_params,[*"Extended BCHCode with parameters",
                                                n-1,params[1] *]);
                res := ExtendCode( BCHCode(F,n-1,params[1]) );
            elif #params eq 2 then
                ad(C_params,[*"Extended BCHCode with parameters",
                                                n-1,params[1],params[2] *]);
                res := ExtendCode( BCHCode(F,n-1,params[1],params[2]) );
            end if;

        when "XBCH_field":
            if #params eq 2 then
                ad(C_params,[*"BCHCode over GF(",params[1],
                            ") with parameters",n-1,params[2] *] );
                res := ExtendCode( BCHCode( GF(params[1]) , n-1, params[2]) );
            elif #params eq 3 then
                ad(C_params,[*"Extended BCHCode over GF(",params[1],
                            ") with parameters",n-1,params[2],params[3]*]);
                res:=ExtendCode(BCHCode(GF(params[1]),n-1,params[2],params[3]));
            end if;

        when "QR":
            ad(C_params,[*"QRCode over GF(",#F,") of length",n *]);
            res := QRCode(F,n);

        when "QR_field":
            ad(C_params,[*"QRCode over GF(",params[1],") of length",n *]);
            res := QRCode(GF(params[1]),n);

        when "XQR":
            ad(C_params,[*"Extend the QRCode over GF(",#F,") of length",n-1*]);
            res := ExtendCode(QRCode(F,n-1));

        when "XQR_field":
            ad(C_params,[*"Extend the QRCode over GF(",params[1],
                                                ") of length",n-1 *]);
            res := ExtendCode(QRCode( GF(params[1]),n-1));

        when "cyclic","cyclic_field":
            K    := Universe(params[1]);
            if Type(K) cmpne FldFin then
              P := PolynomialRing(F); x := P.1;
              p := P![F!x:x in params[1]];
            else
              P := PolynomialRing(K); x := P.1;
              p := P!params[1];
            end if;
            ad(C_params,[*"CyclicCode of length",n,
                                    " with generating polynomial",p *]);
            res := CyclicCode(n,p);

        when "cyclic_octal":
            p := OctalStringToPoly(params[1]);
            ad(C_params,[*"CyclicCode of length",n,
                        " with generating polynomial in octal ",params[1] *]);
            res := CyclicCode(n,p);

        when "quasicyclic":
            P := PolynomialRing(F); x := P.1;
            ad(C_params,[*"QuasiCyclicCode of length",n,
                            " with generating polynomials:"*] cat
                     Prune( &cat[ [* P!y, ", "*] : y in params ]) );

            res := QuasiCyclicCode(n, [P!y : y in params ] );

        when "quasicyclic_field":
            P := PolynomialRing(Universe(params[1])); x := P.1;
            ad(C_params,[*"QuasiCyclicCode of length",n,
                            " with generating polynomials:"*] cat
                     Prune( &cat[ [* P!y, ", "*] : y in params ]) );

            res := QuasiCyclicCode(n, [P!y : y in params ] );

        when "quasicyclic_stack":
            P := PolynomialRing(F); x := P.1;
            h := params[1];
            Remove(~params,1);
            polys := [P!y : y in params ];
            ad(C_params,[*"QuasiCyclicCode of length",n,
                " stacked to height",h," with generating polynomials:"*] cat
                    Prune( &cat[ [* P!y, ", "*] : y in params ]) );

            res := QuasiCyclicCode(n,polys,h);

        when "quasicyclic_field_stack":
            P := PolynomialRing(Universe(params[2])); x := P.1;
            h := params[1];
            Remove(~params,1);
            polys := [P!y : y in params ];
            ad(C_params,[*"QuasiCyclicCode of length",n,
                " stacked to height",h," with generating polynomials:"*] cat
                    Prune( &cat[ [* P!y, ", "*] : y in params ]) );

            res := QuasiCyclicCode(n,polys,h);

// added by M. Grassl
        when "quasitwistedcyclic":
            a := params[1];
            Remove(~params,1);
            V:=KSpace(F,#params[1]);
            ad(C_params,[*"QuasiTwistedCyclicCode of length",n,
                                " and constant",a," with generators:"*] cat
                    Prune( &cat[ [* V!v, ", "*] : v in params ]) );

            res := QuasiTwistedCyclicCode([V!v:v in params],a);

        when "PowRes":
            ad(C_params,[*params[2],"-th PowerResidueCode of length",
                                params[1]," over GF(",#F,")" *]);

            res := PowerResidueCode(F,params[1],params[2]);

        when "PowResPunct":
                //should i allow specification of puncture position????
            ad(C_params,[*"Puncturing of",
                      params[2],"-th PowerResidueCode of length",
                                params[2]," over",F, " at 1" *] );

            res := PunctureCode(Dual(
                PowerResidueCode(F,params[1],params[2])
                                    ), 1 );

        when "PG":
            if #params eq 2 then
                res := PGCode1(F,params[1],params[2]);
                ad(C_params,[*"ProjectiveGeometryCode of Belov type with parameters",
                                        params[1],params[2] *]);
            elif #params eq 3 then
                res := PGCode(F,params[1],params[2],params[3]);
                ad(C_params,[*"ProjectiveGeometryCode of Belov type with parameters",
                                    params[1],params[2],params[3] *]);
            else
                //ERROR
            end if;

        when "PG_field":
            if #params eq 3 then
                res := PGCode1(GF(params[1]),params[2],params[3]);
                ad(C_params,[*"ProjectiveGeometryCode of Belov type over GF(",
                        params[1],") with parameters",
                                    params[2],params[3] *]);
            elif #params eq 4 then
                res := PGCode(GF(params[1]),params[2],params[3],params[4]);
                ad(C_params,[*"ProjectiveGeometryCode of Belov type over GF(",
                        params[1],") with parameters",
                                    params[2],params[3],params[4] *]);
            else
                //ERROR
            end if;


        when "Goppa":
            K := GF(n); w := K.1;
            deg := (d - 1) div 2; 
            Kext := ext<K | deg: Optimize := false>;
//if [n,k] eq [256,200] then
//   K,DefiningPolynomial(K):Maximal;
//   Kext,DefiningPolynomial(Kext):Maximal;
//   GetSeed();
//end if;

            repeat
                G := MinimalPolynomial(Random(Kext),K);
            until Degree(G) eq deg;
            L := [x : x in K];
            P := PolynomialRing( K ); x := P.1;
            G := P!G;
            ad(C_params,[*"GoppaCode using: [x : x in GF(",#K,")] and",G,
                                " where w := GF(",n,").1" *]);

            res := GoppaCode(L,G);

        when "Goppa_poly":
//          K := GF(n); w := K.1;
// try to fix the "field represenation bug"

            K := Universe(params[1]);
            P := PolynomialRing(K); x := P.1;
            L := [x : x in K];
            G := P!params[1];
            ad(C_params,[*"GoppaCode with: [x : x in GF(",#K,")] and",G,
                                " where w := GF(",n,").1" *]);
            
            res := GoppaCode(L,G);

        when "BorderedDoublyCirculantQRCode":
            ad(C_params,[*"BorderedDoublyCirculantQRCode with parameters"
                                        ,params[1],params[2],params[3] *]);

            res := BorderedDoublyCirculantQRCode(params[1],params[2],params[3]);

        when "DoublyCirculantQRCodeGF4":
            ad(C_params,[*"DoublyCirculantQRCodeGF4 with parameters"
                                            ,params[1],params[2] *]);
            res := DoublyCirculantQRCodeGF4(params[1],params[2]);

        when "DHM":
            P := KMatrixSpace(F,8,3) !
                    [0,1,1, 1,1,0, 0,1,1, 1,1,0, 0,1,1, 1,1,0, 0,1,1, 1,1,0];
            ad(C_params,[*"HorizontalJoin of the GeneratorMatrix of",
                            si(params[1])," with the stored matrix",P *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := LinearCode(HorizontalJoin(GeneratorMatrix(C1),P));
            end if;

        when "RR":
            ad(C_params,[*"Construction from a stored generator Matrix"*]);
            CR := ReedMullerCode(1,4);
            G := VerticalJoin(
                  VerticalJoin(
                   VerticalJoin(
                     HorizontalJoin([GH,Z1,GH]),
                     HorizontalJoin([Z1,GH,GH])
                   ),
                   HorizontalJoin([GR,Z2,Z2])
                  ),
                  HorizontalJoin([G4,G4,G4])
            )
            where GH is GeneratorMatrix(Dual(CR))
            where Z1 is Zero(KMatrixSpace(GF(2),11,16))
            where GR is GeneratorMatrix(CR)
            where Z2 is Zero(KMatrixSpace(GF(2),5,16))
            where G4 is KMatrixSpace(GF(2),4,16) ! [0,1,1,1,0,0,0,0,1,0,0,0,0,0,0,0, 0,0,1,0,0,0,0,1,1,1,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,1,1,1,0,1,0];
            res := LinearCode(G);

        when "GG":
            ad(C_params,[*"Puncturing of",si(params[1]),
                           " at the Support of a word of weight", params[2] *]);

            C1 := BKLCRecurse(F,params[1],ind+1);       
            if ISA(Type(C1),Code) then
                sup:=Support(Representative(words(C1,params[2] : NumWords := 1)));
                res := PunctureCode(C1, sup );
            end if;

        when "LC":
            K := GF(2^6);
            a := Roots(x^6+x^4+x^3+x+1,K)[1,1]^5 where x:=PolynomialRing(GF(2)).1;
            P := PolynomialRing(K); x := P.1;
            s := {9,12,30,34,41,42,43,50,54};
            G := &*[(x - a ^ i): i in s];
            L := [0] cat [ a^i : i in [0..62] | i notin s ];
            ad(C_params,[*"GoppaCode with",L," and",G,
                                " where w := GF(",n,").1" *]);

            res := GoppaCode(L,G);

        when "CDJ":
            ad(C_params,[*"Construction from a stored generator Matrix"*]);
            K := GF(2^6);
            a := Roots(x^6+x^4+x^3+x+1,K)[1,1]^5 where x:=PolynomialRing(GF(2)).1;
            P := PolynomialRing(K); z := P.1;
            s := {9,12,30,34,41,42,43,50,54};
            G := &*[(z - a ^ i): i in s];
            L := [0] cat [ a^i : i in [0..62] | i notin s ];
            C := GoppaCode(L,G);
            x := [1,1,1,1,1,1,1,1,1,1,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1];
            G := KMatrixSpace(GF(2),17,55) ! &cat([Eltseq(GeneratorMatrix(C)[i]) : i in [1..Dimension(C)] ] cat [x]);
            x := KMatrixSpace(GF(2),17,1) ! ([ 0 : i in [1..16] ] cat [1]);
            for i in [1..4] do G := HorizontalJoin(G,x); end for;
            res := ExtendCode(LinearCode<GF(2),59 | [ Eltseq(G[i]) : i in [1..Nrows(G)] ]>);

        when "X":
            ad(C_params,[*"ConstructionX using",si(params[1]),si(params[2]),
                        " and",si(params[3]) *] );;

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);

            C3 := BKLCRecurse(F,params[3],ind+1);

            if ISA(Type(C1),Code) and ISA(Type(C2),Code) and ISA(Type(C3),Code) then

//MG, 2007-09-15: fixing the problem with possibly varying defining polynomials
//    retry until the codes are nested
                cnt := 0;
                while not C2 subset C1 and cnt lt 20 do

                  empty_Cache();
                  ad(C_params,[*"ConstructionX using",si(params[1]),si(params[2]),
                        " and",si(params[3]) *] );;

                  cnt +:= 1;
//                  vprintf BestCode: "codes for Construction X not nested, attempt %o\n",cnt;
                  printf "codes for Construction X not nested, attempt %o\n",cnt;
                  if IsEven(cnt) then
                    C1 := BKLCRecurse(F,params[1],ind+1);
                    C2 := BKLCRecurse(F,params[2],ind+1);
                  else
                    C2 := BKLCRecurse(F,params[2],ind+1);
                    C1 := BKLCRecurse(F,params[1],ind+1);
                  end if;
                end while;
                if C2 subset C1 then
                  C3 := BKLCRecurse(F,params[3],ind+1);
                  if ISA(Type(C3),Code) then
                    res := ConstructionX(C1,C2,C3);
                  end if;
                else
                  printf "Construction X failed, codes are not nested\n";    
                  C1:= "Construction X failed, codes are not nested\n";    
                end if;
            end if;

        when "X_BCH":
            if #params eq 3 then
                C1 := BCHCode(F,params[1],params[2]);
                C2 := BCHCode(F,params[1],params[3]);
            elif #params eq 5 then
                C1 := BCHCode(F,params[1],params[2],params[3]);
                C2 := BCHCode(F,params[1],params[4],params[5]);
            else
                print "Error";
            end if;
            C2 := SubcodeBetweenCode(C2,C1,k);
                    //warning, vprint swaps names C1 <-> C2

            entry := ReadEntry(F,n-params[1],Dimension(C2)-Dimension(C1));
            pms := <n-params[1],Dimension(C2)-Dimension(C1),entry[3]>;
        
            ad(C_params,[*"Let C1 be the BCHCode over GF(",#F,
                                    ") of parameters",params[1],params[3],
                        ". Let C2 the SubcodeBetweenCode of dimension",k,
                        " between C1 and the BCHCode with \nparameters",
                                    params[1],params[2],
                        ". Return ConstructionX using C1, C2 and", si(pms) *]);

            C3:= BKLCRecurse(F,pms,ind+1);

            if ISA(Type(C3),Code) then
                res := ConstructionX(C2,C1,C3);
            end if;

        when "XX":
            ad(C_params,[*"ConstructionXX using",si(params[1]),si(params[2]),
                    si(params[3]),si(params[4])," and",si(params[5]) *]);;

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            C3 := BKLCRecurse(F,params[3],ind+1);
            C4 := BKLCRecurse(F,params[4],ind+1);
            C5 := BKLCRecurse(F,params[5],ind+1);

            if  ISA(Type(C1),Code) and
                ISA(Type(C2),Code) and
                ISA(Type(C3),Code) and
                ISA(Type(C4),Code) and
                ISA(Type(C5),Code) then

                res := ConstructionXX(C1,C2,C3,C4,C5);

            end if;


        when "Hg":
            ad(C_params,[*"Construction B2 of the NonPrimitiveAlternant code with parameters",params[1],params[2],params[3] *]);    

            res := ConstructionB2Code(
                    NonPrimitiveAlternant(params[1],params[2],params[3]),
                                        params[4],0,sp);

        when "SubfieldSubcode":
            ad(C_params,[*"SubfieldSubcode of",si(params[1])*]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                if #params eq 1 then
                  res := SubfieldSubcode(C1,F);
                else
                  res := SubfieldSubcode(C1,GF(params[2]));
                end if;
            end if;

        when "SubfieldParityCode":
            ad(C_params,[*"SubfieldRepresentationParityCode of",si(params[1])*]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := SubfieldRepresentationParityCode(C1,F);
            end if;

        when "HS":
            ad(C_params,[*"Construction B2 of BCHCode with parameters",
                                                params[1],params[2] *]);
            res := ConstructionB2Code(
                        BCHCode(F,params[1],params[2]),
                                        params[3],0,sp);

        when "Sugiyama":
            ad(C_params,[*"Using the construction of Sugiyama"*]);
            K := GF(2^7); a := K.1;
            P := PolynomialRing(K); x := P.1;
            p := &*[x-a^i: i in params[1]]*P!params[2];
            ad(C_params,[*"Using the construction of Sugiyama with",
                                p," where a := PrimitiveElement(GF(2,7))" *]);
            res := SugiyamaCode( &*[x-a^i: i in params[1]]*P!params[2] );

        when "SubcodeBetweenCode","SubcodeBetweenCodes":
            ad(C_params,[*"SubcodeBetweenCode of dimension",
                        params[3]," of",si(params[1])," and",si(params[2])*]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
                res := SubcodeBetweenCode(C1,C2,params[3]);
            end if;

        when "Concatenate":
            ad(C_params,[*"ConcatenatedCode of",si(params[1])," and",
                            si(params[2]) *]);;

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
                res := ConcatenatedCode(C1,C2);
            end if;

        when "Grassl127":
            P := PolynomialRing(GF(2)); x := P.1;
            polys := [  [1,1,0,1,0,1,0,1], //1
                        [1,1,0,0,1,0,1,1], //2
                        [1,1,0,0,0,0,0,1], //3
                        [1,0,1,1,1,0,0,1], //4
                        [1,0,0,0,1,0,0,1], //5
                        [1,1,1,1,0,1,1,1], //6
                        [1,0,0,0,0,0,1,1], //7
                        [1,1,1,1,1,1,0,1], //8
                        [1,1,1,1,0,0,0,1], //9
                        [1,0,1,0,0,1,1,1], //10
                        [1,0,0,1,1,1,0,1], //11
                        [1,0,1,1,1,1,1,1], //12
                        [1,0,1,0,1,0,1,1], //13
                        [1,1,1,0,0,1,0,1], //14
                        [1,0,0,1,0,0,0,1], //15
                        [1,1,1,0,1,1,1,1], //16
                        [1,1,0,1,0,0,1,1], //17
                        [1,0,0,0,1,1,1,1]  //18
                    ];

            l := 127 - k;
            m := l mod 7;
            if m eq 0 then
                p := P!1;
                for i in [1..l div 7] do
                    p *:= P!polys[i];
                end for;
                ad(C_params,[* "CyclicCode of length 127 with Generating Polynomial",p *]);

                res := CyclicCode(127,p);
            else
                a := (l-m) div 7;
                
                p1 := P!1;
                for i in [1..a] do
                    p1 *:= P!polys[i];
                end for;

                p2 := p1*P!polys[a+1];

                C1 := CyclicCode(127,p1);
                C2 := CyclicCode(127,p2);

                ad(C_params,[*"Subcode of dimension",k,
        " between the CyclicCode's of length 127 with Generating Polynomials",
                    p1," and",p2 *]);

                res := SubcodeBetweenCode(C1,C2,k);
            end if;

        when "DJ":
            //this comment is cheating!
            ad(C_params,[*"Construction from a stored generator Matrix"*]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                delta_n := n-Length(C1);
                w := params[2] cat [1: i in [1..delta_n]];
                g := HorizontalJoin(GeneratorMatrix(C1),
                        KMatrixSpace(F,k-1,delta_n)![0:i in [1..(k-1)*delta_n]]);
                g := VerticalJoin(g,KMatrixSpace(F,1,n)!w);
                res := LinearCode(g);
            end if;

        when "BZ":
            ad(C_params,[*"ZinovievCode using inner codes:"*] cat
                S2L([ si(params[1][i]) : i in [1..#params[1]] ]) cat
                [* ", outer codes:" *] cat
                S2L([ si(params[2][i]) : i in [1..#params[2]] ]) );
                
            Inner := [BKLCRecurse(F,params[1][i],ind+1) : i in [1..#params[1]]];
            Outer := [BKLCRecurse(F,params[2][i],ind+1) : i in [1..#params[1]]];

            res := ZinovievCode( Inner, Outer );

        when "MDS":
            if #params eq 2 then
                 ad(C_params,[*"MDSCode of dimension",params[2],
                                               " over GF(",params[1],")" *]);
                 res := MDSCode( GF(params[1]),params[2]);
            else
                 ad(C_params,[*"MDSCode of length", params[2], 
                                          " and dimension",params[3],
                                               " over GF(",params[1],")" *]);
                 res := ShortenCode (
                          MDSCode( GF(params[1]),
                                   params[3]+params[1]+1-params[2]),
                           {params[2]+1..params[1]+1});  
            end if; 

        when "Augment":
            ad(C_params,[*"AugmentCode",si(params[1]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);

            if ISA(Type(C1),Code) then
                res := AugmentCode(C1);
            end if;

        when "Dual":
            ad(C_params,[*"Dual of",si(params[1]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := Dual(C1);
            end if;

        when "DirectSum":
            ad(C_params,[*"DirectSum of",si(params[1])," and",si(params[2])*]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
                res := DirectSum(C1,C2);
            end if;

        when "Expurgate":
            ad(C_params,[*"ExpurgateCode",si(params[1]) *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                res := ExpurgateCode(C1);
            end if;

        when "SubcodeWordsOfWeight":
            ad(C_params,[*"SubcodeWordsOfWeight using weight",params[2],
                                                " words of",si(params[1]) *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            if ISA(Type(C1),Code) then
                if #params eq 2 then
                    res := SubcodeWordsOfWeight(C1,params[2]);
                elif #params eq 3 then
//                  res := SubcodeWordsOfWeight(C1,params[2]: 
//                                              NumWords := params[3]);
                    if Type(params[2]) cmpne Set then
                       www:=words(C1,params[2]:NumWords:=params[3]);
                       if #www gt params[3] then
                          www:={x:x in Setseq(www)[1..params[3]]};
                       end if;
                    else
                       www:={};
                       for i in params[2] do
                         w:=words(C1,i:NumWords:=params[3]);
                         if #w gt params[3] then
                            w:={x:x in Setseq(w)[1..params[3]]};
                         end if;
                         www join:=w;
                       end for;
                    end if;
                    res:=sub<C1|www>;
                else
                    error "SubcodeWordsOfWeight to many params";
                end if;
            end if;

        when "CordaroWagner":
            ad(C_params,[*"CordaroWagnerCode of length",n*]);
            res := CordaroWagnerCode(n);

        when "ReedMuller":
            ad(C_params,[*"ReedMullerCode with parameters",params[1],
                                                        params[2]*]);
            res := ReedMullerCode(params[1],params[2]);
        
        when "CoordinateMap":
            ad(C_params,[*"The Generator Elements of",si(params[2]),
                        " with respect to the basis of",si(params[1]),
                "\nencoded to new generator elements using",si(params[3]) *]);

            C2 := BKLCRecurse(F,params[2],ind+1);
            C1 := BKLCRecurse(F,params[1],ind+1);
            C3 := BKLCRecurse(F,params[3],ind+1);

            if ISA(Type(C1),Code) and
               ISA(Type(C2),Code) and
               ISA(Type(C3),Code) then

            res := LinearCode(KMatrixSpace(F,Dimension(C2),Dimension(C1))!
            &cat[Coordinates(C1,g): g in Generators(C2)]*GeneratorMatrix(C3));

            end if;

        when "InsertBlockGenMat":
            //format for params is Code,i,j, Code,i,j, .... where i,j is 
            //position to insert the gen mat of the relevant code
        
            if (#params mod 3) ne 0 then
                error "internal error InsertBlockGenMat params wrong";
            end if;
            
            l := #params div 3;
            fail := false;

            ad(C_params,[*"The Zero Matrix inserted with Generator Matrices of:"*] cat
            &cat [ [* si(params[3*i+1])," inserted at",
                        params[3*i+2],params[3*i+3],", " *] : i in [0..l-1] ]);
            
            G := KMatrixSpace(F,k,n) ! 0;

            for i in [0..l-1] do
                C1 := BKLCRecurse(F,params[3*i+1],ind+1);

                if not ISA(Type(C1),Code) then
                    fail := true;
                else
                    InsertBlock(~G,GeneratorMatrix(C1),
                                        params[3*i+2],params[3*i+3]);
                end if;
            end for;
                
            if fail eq false then
                res := G;          //this returns a matrix
            end if;

        when "SubmatrixCode":
            
            ad(C_params,[*"LinearCode from the Submatrix of",si(params[1]),
                            " at (",params[2],",",params[3],
                            ") of Dimensions",params[4]," x",params[5] *]);
            C1 := BKLCRecurse(F,params[1],ind+1);

            if Type(C1) eq ModMatFldElt then
                res := LinearCode(
                    Submatrix(C1,params[2],params[3],params[4],params[5]) );
            else
                error " internal error SubmatrixCode";
            end if;

        when "CodeComplement":

            ad(C_params,[*"CodeComplement of",si(params[1])," with",
                                si(params[2]) *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            
            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
                res := CodeComplement(C1,C2);
            end if;

        when "Curve":
            K := GF(params[1]); w := K.1;
            poly := params[2];
            rank := #poly[1]-1;
            P<[x]> := ProjectiveSpace(K,rank-1);
            p := Parent(P.1)!0;
            for term in poly do
                p_temp := Parent(P.1)!term[1];
                for i in [1..rank] do
                    p_temp *:= (P.i)^term[i+1];
                end for;
                p +:= p_temp;
            end for;

            ad(C_params,[*"A Curve over GF(",params[1],"):",p,
                                    " where w := GF(",#K,").1" *]);
            res := Curve(P,p);

        when "Curve_P2":
            K := GF(params[1]); w := K.1;
            poly := params[2];
            rank := #poly[1];
            P<[x]> := ProjectiveSpace(K,rank-1);
            p := Parent(P.1)!0;
            for term in poly do
                p_temp := Parent(P.1)!term[1];
                for i in [1..rank-1] do
                    p_temp *:= (P.i)^term[i+1];
                end for;
                p +:= p_temp;
            end for;

            p := Homogenization(p,P.rank);

            ad(C_params,[*"A Curve over GF(",params[1],"):",p,
                                    " where w := GF(",#K,").1" *]);
            res := Curve(P,p);


        when "AG":
            //first parameter is a CURVE
            //then 4 sequences representing 2 divisors
            ad(C_params,[*"AlgebraicGeometricCode from the curve",
                                                        si(params[1])*]);
            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X ); 
            places_1 := Places(X,1);
            FF := FunctionField(X);
            rank := #params[2][1]-1;
            P<x,y> := PolynomialRing( K , rank);

            Polys := [P|];
            //now read the 4 polys into Polys[1..4]
            for i in [1..4] do
                poly := params[i+1];

                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;

                Polys[i] := p;
            end for;
            
            //create funs
            funs:=[Evaluate(Polys[1],[FF.1,FF.2])/Evaluate(Polys[2],[FF.1,FF.2])
                  ,Evaluate(Polys[3],[FF.1,FF.2])/Evaluate(Polys[4],[FF.1,FF.2])
                  ];    

            D := DivisorGroup(X) ! Place(funs);
            res := AlgebraicGeometricCode(places_1, D);

        when "AGSub1":
            //this is almost the same as "AG"
            //but the place for the "parent" code must be excluded
            //from places_1 (stored in the last 4 spots)

            ad(C_params,[*"AlgebraicGeometricCode from the curve",
                si(params[1]), " which is designed to have a good subcode"*]);
            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X );
            places_1 := Places(X,1);
            FF := FunctionField(X);
            rank := #params[2][1]-1;
            P<x,y> := PolynomialRing( K , rank);
 
            Polys := [P|];
            //now read the 8 polys into Polys[1..8]
            for i in [1..8] do
                poly := params[i+1];
 
                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;
 
                Polys[i] := p;
            end for;

            //create funs
            funs:=[Evaluate(Polys[1],[FF.1,FF.2])/Evaluate(Polys[2],[FF.1,FF.2])
                  ,Evaluate(Polys[3],[FF.1,FF.2])/Evaluate(Polys[4],[FF.1,FF.2])
                  ];

           funs1:=[Evaluate(Polys[5],[FF.1,FF.2])/Evaluate(Polys[6],[FF.1,FF.2])
                  ,Evaluate(Polys[7],[FF.1,FF.2])/Evaluate(Polys[8],[FF.1,FF.2])
                  ];

            Exclude(~places_1,Place(funs1));
            D := DivisorGroup(X) ! Place(funs);
            res := AlgebraicGeometricCode(places_1, D);


        when "AGSub2":
            //first parameter is a CODE
            //next parameters are 4 polys representing 2 funs

            ad(C_params,[*"AlgebraicGeometricCode which is a subcode of",
                            si(params[1]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            X := Curve(Divisor(C1));
            K<w> := BaseField( X );
            places_1 := Places(X,1);
            FF := FunctionField(X);
            rank := #params[2][1]-1; //should always be 2 yes?
            P<x,y> := PolynomialRing( K , rank);
 
            Polys := [P|];
            //now read the 4 polys into Polys[1..4]
            for i in [1..4] do
                poly := params[i+1];
 
                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;
 
                Polys[i] := p;
            end for;
 
            //create funs

            funs:=[Evaluate(Polys[1],[FF.1,FF.2])/Evaluate(Polys[2],[FF.1,FF.2])
                  ,Evaluate(Polys[3],[FF.1,FF.2])/Evaluate(Polys[4],[FF.1,FF.2])
                  ];  

            P1 := Place(funs);
            Exclude(~places_1, P1);
            D := (DivisorGroup(X) ! P1) + Divisor(C1);
            
            res := AlgebraicGeometricCode(places_1, D);

        when "AGDivDeg1":
            //first parameter is a CURVE
            //then 4 sequences representing 2 divisors

            ad(C_params,[*"AlgebraicGeometricCode from the curve",si(params[1]),
                        " which is based on a Divisor of Degree 1" *]);

            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X );
            places_1 := Places(X,1);
            FF := FunctionField(X);
            rank := #params[2][1]-1;
            P<x,y> := PolynomialRing( K , rank);
 
            Polys := [P|];
            //now read the 4 polys into Polys[1..4]
            for i in [1..4] do
                poly := params[i+1];
 
                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;
 
                Polys[i] := p;
            end for;
 
            //create funs

            funs:=[Evaluate(Polys[1],[FF.1,FF.2])/Evaluate(Polys[2],[FF.1,FF.2])
                  ,Evaluate(Polys[3],[FF.1,FF.2])/Evaluate(Polys[4],[FF.1,FF.2])
                  ];

            Pl := Place(funs); 
            Exclude(~places_1,Pl);
            D := (k+Genus(X)-1)*(DivisorGroup(X) ! Pl);
            res := AlgebraicGeometricCode(places_1, D);

        when "AG_chain":
            //first parameter is a CURVE
            //then 8 sequences representing 2 divisors of degree 2 and 3

            ad(C_params,[*"AlgebraicGeometricCode from the curve",si(params[1]),
                    " which is based on two divisors of degree 2 and 3" *]);
            
            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X );
            places_1 := Places(X,1);
            FF := FunctionField(X);
            rank := #params[2][1]-1;
            P<x,y> := PolynomialRing( K , rank);
 
            Polys := [P|];
            //now read the 8 polys into Polys[1..8]
            for i in [1..8] do
                poly := params[i+1];
 
                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;
 
                Polys[i] := p;
            end for;
 
            //create funs

            funs:=[Evaluate(Polys[1],[FF.1,FF.2])/Evaluate(Polys[2],[FF.1,FF.2]),
                   Evaluate(Polys[3],[FF.1,FF.2])/Evaluate(Polys[4],[FF.1,FF.2]),
                   Evaluate(Polys[5],[FF.1,FF.2])/Evaluate(Polys[6],[FF.1,FF.2]),
                   Evaluate(Polys[7],[FF.1,FF.2])/Evaluate(Polys[8],[FF.1,FF.2])
                  ];
            Pl2 := Place(funs[1..2]); 
            Pl3 := Place(funs[3..4]); 
            Exclude(~places_1,Pl2);
            Exclude(~places_1,Pl3);

            deg:=(k+Genus(X)-1);
            if IsOdd(deg) then
                D := ((deg-3) div 2)*(DivisorGroup(X) ! Pl2)+(DivisorGroup(X) ! Pl3);
            else
                D := (deg div 2)*(DivisorGroup(X) ! Pl2);
            end if;
            res := AlgebraicGeometricCode(places_1, D);

        when "AG_chain2":
            //first parameter is a CURVE
            //then 12 sequences representing 3 divisors of degree 3, 4, and 5

            ad(C_params,[*"AlgebraicGeometricCode from the curve",si(params[1]),
                " which is based on three divisors of degree 3, 4 and 5" *]);

            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X );
            places_1 := Places(X,1);
            FF := FunctionField(X);
            rank := #params[2][1]-1;
            P<x,y> := PolynomialRing( K , rank);
 
            Polys := [P|];
            //now read the 12 polys into Polys[1..12]
            for i in [1..12] do
                poly := params[i+1];
 
                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;
 
                Polys[i] := p;
            end for;
 
            //create funs

            funs:=[Evaluate(Polys[1],[FF.1,FF.2])/Evaluate(Polys[2],[FF.1,FF.2]),
                   Evaluate(Polys[3],[FF.1,FF.2])/Evaluate(Polys[4],[FF.1,FF.2]),
                   Evaluate(Polys[5],[FF.1,FF.2])/Evaluate(Polys[6],[FF.1,FF.2]),
                   Evaluate(Polys[7],[FF.1,FF.2])/Evaluate(Polys[8],[FF.1,FF.2]),
                   Evaluate(Polys[9],[FF.1,FF.2])/Evaluate(Polys[10],[FF.1,FF.2]),
                   Evaluate(Polys[11],[FF.1,FF.2])/Evaluate(Polys[12],[FF.1,FF.2])
                  ];
            Pl3 := Place(funs[1..2]); 
            Pl4 := Place(funs[3..4]); 
            Pl5 := Place(funs[5..6]); 
            Exclude(~places_1,Pl3);
            Exclude(~places_1,Pl4);
            Exclude(~places_1,Pl5);

            deg:=(k+Genus(X)-1);
            case deg mod 4:
              when 0: 
                 D := (deg div 4)*(DivisorGroup(X) ! Pl4);
              when 1: 
                 D := ((deg div 4)-1)*(DivisorGroup(X) ! Pl4) + (DivisorGroup(X) ! Pl5);
              when 2: 
                 D := ((deg div 4)-1)*(DivisorGroup(X) ! Pl4) + 2*(DivisorGroup(X) ! Pl3);
              when 3: 
                 D := (deg div 4)*(DivisorGroup(X) ! Pl4) + (DivisorGroup(X) ! Pl3);
              else:
                 D := 0*(DivisorGroup(X) ! Pl3);
            end case;

            res := AlgebraicGeometricCode(places_1, D);

        when "AG_chain3":
            //first parameter is a CURVE
            //then n*4 sequences representing n divisors

            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X );
            places_1 := Places(X,1);
            FF := FunctionField(X);
            rank := #params[2][1]-1;
            P<x,y> := PolynomialRing( K , rank);
 
            Polys := [P|];

            //now read the 4*n polys into Polys[1..n]
            
            for i in [1..#params-1] do
                poly := params[i+1];
 
                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;
 
                Polys[i] := p;
            end for;
 
            //create funs

            funs:=&cat[
                  [Evaluate(Polys[i],[FF.1,FF.2])/Evaluate(Polys[i+1],[FF.1,FF.2]),
                   Evaluate(Polys[i+2],[FF.1,FF.2])/Evaluate(Polys[i+3],[FF.1,FF.2])]:
                     i in [1..#Polys by 4]];


            places := [Place(funs[i..i+1]): i in [1..#funs by 2]];

            ad(C_params,[*"AlgebraicGeometricCode from the curve",si(params[1]),
                " which is based on",#places," divisors of degree",[Degree(f):f in places] *]);

            for p in places do
              Exclude(~places_1,p);
            end for;

            deg:=(k+Genus(X)-1);
            coeff:=Solution(Matrix([[Degree(p)]: p in places]),Matrix([[deg]]))[1];

            D := &+[coeff[i]*DivisorGroup(X)!places[i]:i in [1..#places]|coeff[i] ne 0];

            res := AlgebraicGeometricCode(places_1, D);

        when "AG_divisor","AG_Divisor","AGDivisor":
            //first parameter is a CURVE
            //second parameter is the list of coefficients for n places
            //then n*4 sequences representing n divisors

            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X );
            places_1 := Places(X,1);
            FF<a,b> := FunctionField(X);
            coeff :=params[2];

            rank := #params[3][1]-1;
            P<x,y> := PolynomialRing( K , rank);
 
            Polys := [P|];

            //now read the 4*n polys into Polys[1..n]
            
            for i in [1..#params-2] do
                poly := params[i+2];
 
                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;
 
                Polys[i] := p;
            end for;
 
            //create funs

            funs:=&cat[
                  [Evaluate(Polys[i],[FF.1,FF.2])/Evaluate(Polys[i+1],[FF.1,FF.2]),
                   Evaluate(Polys[i+2],[FF.1,FF.2])/Evaluate(Polys[i+3],[FF.1,FF.2])]:
                     i in [1..#Polys by 4]];
            places := [Place(funs[i..i+1]): i in [1..#funs by 2]];

            ad(C_params,[*"AlgebraicGeometricCode from the curve",si(params[1]),
                " which is based on",#places," divisors of degree",[Degree(f):f in places] *]);

            for p in places do
              Exclude(~places_1,p);
            end for;

            deg:=(k+Genus(X)-1);

            D := &+[coeff[i]*DivisorGroup(X)!places[i]:i in [1..#places]|coeff[i] ne 0];

            res := AlgebraicGeometricCode(places_1, D);

        when "AG_supercode":
            //first parameter is an AG code
            //then the dimension

            c1 := BKLCRecurse(F,params[1],ind+1); //this is the parent code
            places1 := c1`GeometricSupport;
            D1 := c1`Divisor;
            X := Curve(D1);
            places,coeff1 := Support(D1);

            ad(C_params,[*"AlgebraicGeometricCode which contains the code",si(params[1])*]);

            deg:=(k+Genus(X)-1);

            lp:=LPProcess(Integers(),#coeff1);
            SetIntegerSolutionVariables(lp,[i:i in [1..#coeff1]],true);
            for i:=1 to #coeff1 do
              SetLowerBound(lp,i,coeff1[i]);
            end for;
            AddConstraints(lp,Matrix([[Degree(p):p in places]]),Matrix([[deg]]):Rel:="eq");
            coeff,fl:=Solution(lp);
            if fl ne 0
              then error "No solution found";
            else
              coeff:=coeff[1];
            end if;

            D := &+[coeff[i]*DivisorGroup(X)!places[i]:i in [1..#places]|coeff[i] ne 0];

            res := AlgebraicGeometricCode(places1, D);

        when "AG_subcode":
            //first parameter is an AG code
            //then the dimension

            c1 := BKLCRecurse(F,params[1],ind+1); //this is the parent code
            places1 := c1`GeometricSupport;
            D1 := c1`Divisor;
            X := Curve(D1);
            places,coeff1 := Support(D1);

            ad(C_params,[*"AlgebraicGeometricCode which is contained in the code",si(params[1])*]);

            deg:=(k+Genus(X)-1);

            lp:=LPProcess(Integers(),#coeff1);
            SetIntegerSolutionVariables(lp,[i:i in [1..#coeff1]],true);
            for i:=1 to #coeff1 do
              SetUpperBound(lp,i,coeff1[i]);
            end for;
            AddConstraints(lp,Matrix([[Degree(p):p in places]]),Matrix([[deg]]):Rel:="eq");
            coeff,fl:=Solution(lp);
            if fl ne 0
              then error "No solution found";
            else
              coeff:=coeff[1];
            end if;

            D := &+[coeff[i]*DivisorGroup(X)!places[i]:i in [1..#places]|coeff[i] ne 0];

            res := AlgebraicGeometricCode(places1, D);

        when "GeneralizedAG":
            //first parameter is a CURVE,
            //second parameter is a list with the number n_i places of degree i,
            //then either 4 sequences representing a divisior with support of size 1
            //or alternating a place and the coefficient of the place

            ad(C_params,[*"Generalized Algebraic Geometric Code from the curve",
                                        si(params[1]) *]);
            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X );
            FF := FunctionField(X);
            rank := #params[3][1]-1;
            P<x,y> := PolynomialRing( K , rank);

            num_degs:=params[2];

            D := DivisorGroup(X) ! 0;

            //now read the 4 polys into Polys[1..4]
            for j:=2 to #params-1 by 5 do
              Polys := [P|];
              for i in [1..4] do
                  poly := params[i+j];
  
                  p := P!0;
                  for term in poly do
                      p_temp := P!term[1];
                      for i in [1..rank] do
                          p_temp *:= (P.i)^term[i+1];
                      end for;
                      p +:= p_temp;
                  end for;
  
                  Polys[i] := p;
              end for;
              //create funs
              funs:=[Evaluate(Polys[1],[FF.1,FF.2])/Evaluate(Polys[2],[FF.1,FF.2]),
                     Evaluate(Polys[3],[FF.1,FF.2])/Evaluate(Polys[4],[FF.1,FF.2])
                    ];
              if j+5 le #params then
                coeff:=params[j+5];
              else
                coeff:=1;
              end if;
              D +:= coeff*DivisorGroup(X) ! Place(funs);

            end for;

            K := BaseRing(X);
            ext := Degree(K,F);

//            L_c:=[BLLC(F,ext*i,ext*i):i in [1..#num_degs]];
            L_para:=[<BLLCLowerBound(F,ext*i,ext*i),ext*i,1>:i in [1..#num_degs]];
            L_c:=[];
            for p in L_para do
              ind+:=1;
              Append(~L_c,BKLCRecurse(F,p,ind));
            end for;

            if k mod ext ne 0 then
              error "mismatch between field of the curve and dimension";
            end if;
            deg:=(k div ext)+Genus(X)-1;
            
            if deg mod Degree(D) eq 0 then
              D:=(deg div Degree(D))*D;
            else
              error "wrong divisor",Degree(D),deg;
            end if;
            S := Support(D);
            places:=[];
            for d:=1 to #num_degs do
              pl:=Places(X,d);
              pl:=[p:p in pl|not p in S];
              if #pl lt num_degs[d] then
                 error Sprintf("There no enough places of degree %o",d);
              else
                places cat:=pl[1..num_degs[d]];
              end if;
            end for;

            res := GeneralizedAlgebraicGeometricCode(places, D, L_c);

        when "GeneralizedAG2":
            //first parameter is a CURVE,
            //second parameter is a list with the number n_i places of degree i,
            //then 4 sequences representing 2 divisors
            //then the codes used for the concatenation

            ad(C_params,[*"GeneralizedAlgebraicGeometricCode from the curve",
                                                        si(params[1])*]);

            X := BKLCRecurse(F,params[1],ind+1); //this is the curve
            K<w> := BaseField( X );
            FF := FunctionField(X);
            rank := #params[3][1]-1;
            P<x,y> := PolynomialRing( K , rank);

            num_degs:=params[2];
            L_c:=[BKLCRecurse(F,params[i+6],ind+1):i in [1..#num_degs]];

            Polys := [P|];
            //now read the 4 polys into Polys[1..4]
            for i in [1..4] do
                poly := params[i+2];

                p := P!0;
                for term in poly do
                    p_temp := P!term[1];
                    for i in [1..rank] do
                        p_temp *:= (P.i)^term[i+1];
                    end for;
                    p +:= p_temp;
                end for;

                Polys[i] := p;
            end for;

            //create funs
            funs:=[Evaluate(Polys[1],[FF.1,FF.2])/Evaluate(Polys[2],[FF.1,FF.2])
                  ,Evaluate(Polys[3],[FF.1,FF.2])/Evaluate(Polys[4],[FF.1,FF.2])
                  ];

            D := DivisorGroup(X) ! Place(funs);
            K := BaseRing(X);
            ext := Degree(K,F);

            if k mod ext ne 0 then
              error "mismatch between field of the curve and dimension";
            end if;
            deg:=(k div ext)+Genus(X)-1;
            if deg mod Degree(D) eq 0 then
              D:=(deg div Degree(D))*D;
            else
              error "wr ong divisor",Degree(D),deg;
            end if;
            S := Support(D);
            places:=[];
            for d:=1 to #num_degs do
              pl:=Places(X,d);
              pl:=[p:p in pl|not p in S];
              if #pl lt num_degs[d] then
                 error Sprintf("There no enough places of degree %o",d);
              else
                places cat:=pl[1..num_degs[d]];
              end if;
            end for;
            res := GeneralizedAlgebraicGeometricCode(places, D, L_c);


        when "AGSpecial":

            ad(C_params,[*"An Algebraic Geometric construction" *]);    
            K := GF(16); w := K.1;
            P2<x,y,z> := ProjectiveSpace(K, 2);
            f := x^3+x^2*z+y^3+y^2*z+z^3;
            X := Curve(P2, f);
            FF<p, q> := FunctionField(X);
            funs1 := [
                [ 1/q, (p + q)/q ],
                [ 1/q, (p + w^5*q)/q ],
                [ 1/q, (p + w^10*q)/q ],
                [ q + w^3, p + w^6 ],
                [ q + w^3, p + w^9 ],
                [ q + w^3, p + w^10 ],
                [ q + w^5, p + w^6 ],
                [ q + w^5, p + w^9 ],
                [ q + w^5, p + w^10 ],
                [ q + w^6, p + w^3 ],
                [ q + w^6, p + w^5 ],
                [ q + w^6, p + w^12 ],
                [ q + w^7, p + w^13 ],
                [ q + w^9, p + w^3 ],
                [ q + w^9, p + w^5 ],
                [ q + w^9, p + w^12 ],
                [ q + w^10, p + w^3 ],
                [ q + w^10, p + w^5 ],
                [ q + w^10, p + w^12 ],
                [ q + w^11, p + w^14 ],
                [ q + w^12, p + w^6 ],
                [ q + w^12, p + w^9 ],
                [ q + w^12, p + w^10 ],
                [ q + w^13, p + w^7 ]
            ];

            pls_1 := [ Place(funs1[i]) : i in [1..#funs1] ];
            funs2 := [ [ q + w^7, p^2 + w^6*p + w^4 ],
                       [ q + w^11, p^2 + w^3*p + w^2 ] ];       
             
            pls_2 := [ Place(funs2[i]) : i in [1..#funs2] ];
             
            fun8 := [q^8 + w^4*q^7 + w^14*q^5 + q^4 + w^3*q^3 + 
                    w^9*q^2 + w^3*q + w, p + q^7 + 
                    w^14*q^6 + w^7*q^4 + w^5*q^3 + q^2 + w^8*q + 1];
             
            pl8 := Place(fun8);

            G1 := pls_2[1]+pls_2[2]+pl8;
            G2 := pls_2[1]+pl8;
            G3 := pls_2[2]+pl8;
             
            c1 := AlgebraicGeometricCode(pls_1, G1); 
            c2 := AlgebraicGeometricCode(pls_1, G2);
            c3 := AlgebraicGeometricCode(pls_1, G3);

            A1:=ZinovievCode([ReedMullerCode(1,3),ReedMullerCode(2,3)],
                             [c1 , RepetitionCode(GF(8),24)]);
            A11:=ZinovievCode([ReedMullerCode(1,3)],[c1]);
            A2:=ZinovievCode([ReedMullerCode(1,3)],[c2]);
            A3:=ZinovievCode([ReedMullerCode(1,3)],[c3]);

            res := ConstructionXX(sub<A1|A11,CodeComplement(A1,A11).1>,
             A2,A3,ShortenCode(PunctureCode(GolayCode(GF(2),false),23),{20..22})
                ,ShortenCode(GolayCode(GF(2),true),{22..24}));

        when "XL":
            ad(C_params,[* Sprintf("Subcode of a punctured Reed-Solomon code over GF(%o)",#F^2)*]);
            q:=#F;
            K2:=GF(q^2);
            if #params eq 2 then
              t:=params[1];
              m:=params[2];

              k:=Binomial(m+1,2);
              n:=t+(q^2-q) div 2;
              L:=[x:x in F][1..t] cat Setseq({Rep({x,x^q}):x in K2|not x in F});
              G:=KMatrixSpace(F,k,n)![i eq j select x^(q*i+j) else x^(q*i+j)+x^(q*j+i):
                   x in L,i in [0..j],j in [0..m-1]];
            else
              t:=params[1];
              m:=params[2];
              l:=params[3];

              k:=Binomial(m,2)+l+1;
              n:=t+(q^2-q) div 2;
              L:=[x:x in F][1..t] cat Setseq({Rep({x,x^q}):x in K2|not x in F});
              G:=KMatrixSpace(F,k,n)![i eq j select x^(q*i+j) else x^(q*i+j)+x^(q*j+i):
                   x in L,i in [0..j eq m-1 select l else j],j in [0..m-1]];
            end if;  
            res:=LinearCode(G);
                      
        when "Hamming":
            case params[1]:
               when 1:
                 ad(C_params,[* params[1],"-st order HammingCode over GF(",#F,")"*]);
               when 2:
                 ad(C_params,[* params[1],"-nd order HammingCode over GF(",#F,")"*]);
               when 3:
                 ad(C_params,[* params[1],"-rd order HammingCode over GF(",#F,")"*]);
               else
                 ad(C_params,[* params[1],"-th order HammingCode over GF(",#F,")"*]);
            end case;
            res := HammingCode(F,params[1]);

        when "mat":
            res := KMatrixSpace(Universe(params[1]),k,n) ! params[1];
            ad(C_params,[* "Stored Matrix of dimension" ,k," x",n *]);
            
        when "X3":
            ad(C_params,[*"ConstructionX3 with",si(params[1]),si(params[2]),
                                si(params[3]),si(params[4]),si(params[5]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            C3 := BKLCRecurse(F,params[3],ind+1);
            C4 := BKLCRecurse(F,params[4],ind+1);
            C5 := BKLCRecurse(F,params[5],ind+1);

            if  ISA(Type(C1),Code) and
                ISA(Type(C2),Code) and
                ISA(Type(C3),Code) and
                ISA(Type(C4),Code) and
                ISA(Type(C5),Code)    then
                
                res :=ConstructionX3(C1,C2,C3,C4,C5);
            end if;

//added by MG
        when "X3u":

            ad(C_params,[*"ConstructionX3u with",si(params[1]),si(params[2]),
                                si(params[3]),si(params[4]),si(params[5]) *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            C3 := BKLCRecurse(F,params[3],ind+1);
            C4 := BKLCRecurse(F,params[4],ind+1);
            C5 := BKLCRecurse(F,params[5],ind+1);

            if  ISA(Type(C1),Code) and
                ISA(Type(C2),Code) and
                ISA(Type(C3),Code) and
                ISA(Type(C4),Code) and
                ISA(Type(C5),Code)    then
                
                res :=ConstructionX3u(C1,C2,C3,C4,C5);
            end if;

        when "XXu":

            ad(C_params,[*"ConstructionXXu with",si(params[1]),si(params[2]),
                                si(params[3]),si(params[4]),si(params[5]) *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);
            C3 := BKLCRecurse(F,params[3],ind+1);
            C4 := BKLCRecurse(F,params[4],ind+1);
            C5 := BKLCRecurse(F,params[5],ind+1);

            if  ISA(Type(C1),Code) and
                ISA(Type(C2),Code) and
                ISA(Type(C3),Code) and
                ISA(Type(C4),Code) and
                ISA(Type(C5),Code)    then
                
                res :=ConstructionXXu(C1,C2,C3,C4,C5,params[6]);
            end if;


        when "XChainX":
//similar to X6 below, but using "X" instead of "X3"
            ad(C_params,[*"Apply ConstructionXChain to" *] cat
                    S2L([ si(para) : para in params[1] ]) cat
                    [* " and", si(params[2]), 
            " then apply ConstructionX using",si(params[3]) *]);

            chain := [BKLCRecurse(F,para,ind+1): para in params[1]];
            D1 := BKLCRecurse(F,params[2],ind+1);
     
            chain2 :=ConstructionXChain(chain,D1);

// modification: first code in chain2 may have a higher dimension

            if Dimension(chain2[1]) gt k then
               chain2[1]:=SubcodeBetweenCode(chain2[1],chain2[3],k);
            end if;

            D2 := BKLCRecurse(F,params[3],ind+1);

            res := ConstructionX(chain2[1],chain2[3],D2);

        when "X4":
//similar to X6 below, but using "XX" instead of "X3"
            ad(C_params,[*"Apply ConstructionXChain to" *] cat
                    S2L([ si(para) : para in params[1] ]) cat
                    [* " and", si(params[2]), 
            " then apply ConstructionXX using",si(params[3]),si(params[4]) *]);

            chain := [BKLCRecurse(F,para,ind+1): para in params[1]];
            D1 := BKLCRecurse(F,params[2],ind+1);
     
            chain2 :=ConstructionXChain(chain,D1);

            D2 := BKLCRecurse(F,params[3],ind+1);
            D3 := BKLCRecurse(F,params[4],ind+1);

            res := ConstructionXX(chain2[1],chain2[3],chain2[4],D2,D3);

        when "X6":
            ad(C_params,[*"Apply ConstructionXChain to" *] cat
                    S2L([ si(para) : para in params[1] ]) cat
                    [* " and", si(params[2]), 
            "then apply ConstructionX3 using",si(params[3]),si(params[4]) *]);

            chain := [BKLCRecurse(F,para,ind+1): para in params[1]];
            D1 := BKLCRecurse(F,params[2],ind+1);
     
            chain2 :=ConstructionXChain(chain,D1);

            D2 := BKLCRecurse(F,params[3],ind+1);
            D3 := BKLCRecurse(F,params[4],ind+1);

            res := ConstructionX3(chain2[1],chain2[3],chain2[4],D2,D3);

        when "X6u":
            ad(C_params,[*"Apply ConstructionXChain to" *] cat
                    S2L([ si(para) : para in params[1] ]) cat
                    [* " and", si(params[2]), 
            " then apply ConstructionX3u using",si(params[3]),si(params[4]) *]);

            chain := [BKLCRecurse(F,para,ind+1): para in params[1]];
            D1 := BKLCRecurse(F,params[2],ind+1);
     
            chain2 :=ConstructionXChain(chain,D1);

// modification: first code in chain2 may have a higher dimension

            if Dimension(chain2[1]) gt k then
               chain2[1]:=SubcodeBetweenCode(chain2[1],chain2[3],k);
            end if;
            D2 := BKLCRecurse(F,params[3],ind+1);
            D3 := BKLCRecurse(F,params[4],ind+1);

            res := ConstructionX3u(chain2[1],chain2[3],chain2[4],D2,D3);

        when "X6a":
            ad(C_params,[*"Apply ConstructionXChain to" *] cat
                    S2L([ si(para) : para in params[1] ]) cat
                    [* " and", si(params[2]), 
            " then apply ConstructionX twice using",si(params[3]),"and",si(params[4]) *]);

            chain := [BKLCRecurse(F,para,ind+1): para in params[1]];
            D1 := BKLCRecurse(F,params[2],ind+1);
     
            chain2 :=ConstructionXChain(chain,D1);

// modification: first code in chain2 may have a higher dimension

            if Dimension(chain2[1]) gt k then
               chain2[1]:=SubcodeBetweenCode(chain2[1],chain2[3],k);
            end if;
            D2 := BKLCRecurse(F,params[3],ind+1);
            D3 := BKLCRecurse(F,params[4],ind+1);

            C1 := ConstructionX(chain2[1],chain2[3],D2);
            C2 := PadCode(chain2[4],Length(D2));
            res := ConstructionX(C1,C2,D3);

//added by M. Grassl
        when "Maruta":

           g:=Polynomial(params[1]);

           if #params eq 1 then
             ad(C_params,[* "Take the first",
                 n," points of the orbit of the companion matrix of ",
                 g," as columns of the generator matrix" *]);
             res := MarutaCode(g,n);
           elif #params eq 2 and Type(params[2]) cmpeq RngIntElt then
             ad(C_params,[* "Take the first",
                 n+1," points of the orbit of the companion matrix of ",
                 g," as columns of the generator matrix and delete column",params[2] *]);
             res := MarutaCode2(g,n+1,params[2]);
           else
             vecs:=[KSpace(F,k)|x:x in params[2]];
             ad(C_params,[* "Take the first",
                 n-#vecs," points of the orbit of the companion matrix of ",
                 g," as columns of the generator matrix and append the column vectors", vecs *]);
             res := MarutaCode1(g,n-#vecs,vecs);
           end if;

        when "Intersection":
            
            ad(C_params,[*"The intersection of",si(params[1])," and",
                                si(params[2]) *]);

            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);

            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
                res := C1 meet C2;
            end if;

        when "MultGenMats":
            ad(C_params,[*"The Code generated by the multiplication of",
                            " the GeneratorMatrix's of the codes",
                            si(params[1])," and", si(params[2]) *]);
            C1 := BKLCRecurse(F,params[1],ind+1);
            C2 := BKLCRecurse(F,params[2],ind+1);

            if ISA(Type(C1),Code) and ISA(Type(C2),Code) then
                res := LinearCode( GeneratorMatrix(C1) * GeneratorMatrix(C2) );
            end if;

        when "MultiVarPol":
            //syntax: #GF, [ <coeff,exp1,exp2,..,expn> , <coeff, .. > ];
            //sequence of tuples with coeff followed by exponenets

            K := GF( params[1] );
            poly := params[2];
            rank := #poly[1]-1;
            P<[x]> := PolynomialRing( K , rank);
            p := 0;
            for term in poly do
                p_temp := P!term[1];
                for i in [1..rank] do
                    p_temp *:= (P.i)^term[i+1];
                end for;
                p +:= p_temp;
            end for;

            ad(C_params,[*"Stored Multivariate Polynomial",p *]);
            res := p;

        when "Repetition_field":
            ad(C_params,[*"RepetitionCode of length",params[2],
                                    " over GF(",params[1],")" *]);
            res := RepetitionCode( GF( params[1] ) , params[2] );

        when "Q":
            //format <int> , <int>, <FF_seq>, Code

            ad(C_params,[*"The Sugiyama Q construction using",si(params[4])*]);
            C1 := BKLCRecurse(F,params[4],ind+1);

            if ISA(Type(C1),Code) then
                res := SugiyamaCodeQ(params[1],params[2],params[3],C1);
            end if;

        when "Perm_specific":
            //this construction is way too specific
            //if more codes constructed using Perm Code then genberalise it
            //only 205_21_80 uses it at the moment

            ad(C_params,[*"PermutationCode on",params[1],
                        "with G := Cosetimage(g,sub<g>) where g := SmallGroup(",
                        n,",1)" *]);

            g := SmallGroup(n,1);
            G := CosetImage(g,sub<g|>);
            res := PermutationCode(KSpace(GF(2),n)!params[1],G);

        when "ConstaCyclic":
            P := PolynomialRing(F); x := P.1;
            f := P ! params[1];
            ad(C_params,[*"ConstaCyclicCode generated by",f,
                            " with shift constant",params[2] *]);

            res := ConstaCyclicCode(n, f, params[2]);

        when "ConstaCyclic_field","ConstaCyclic?Field":
            P := PolynomialRing(Universe(params[1])); x := P.1;
            f := P ! params[1];
            ad(C_params,[*"ConstaCyclicCode generated by",f,
                            " with shift constant",params[2] *]);

            res := ConstaCyclicCode(n, f, params[2]);
            
/////////////////////////////////////////////////////////////////////////////
        else
            error "Unknown Construction",Construction;
    end case;


    if ISA(Type(res),Code) then
        if d ne 0 then
            if assigned res`MinimumWeight and res`MinimumWeight ne d then
                print "Incorrect MinimumWeight Error:",[n,k,res`MinimumWeight];
                printf "entry in database is d=%o\n",d;
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
 

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

intrinsic ReadEntry1(F::FldFin, n::RngIntElt,k::RngIntElt) -> Any
{read the data from the n,k -th entry in the code database}
return ReadEntry(F,n,k);
end intrinsic;

ReadEntry := function(F,n,k)
    return ReadEntryFlag(F, n, k, false);
end function;

function GuardedGetEnv(var)
    try
	return GetEnv(var);
    catch E
	return "";
    end try;
end function;

ReadEntryFlag := function(F,n,k,is_quantum)
//read the n,k entry from the binary file

    // Enable use of alternative data files during development
    DATA := GuardedGetEnv("BKLC_DEV_DIR");
    use_lib := is_export_version or DATA eq "";
    Open := LibFileOpen;

    if use_lib then
	BinFilePath := GetLibraryRoot() cat "/data/BKLC/";
    else
	BinFilePath := DATA;
    end if;

    F_str := IntegerToString(#F);
    if is_quantum then
	F_str cat:= "Q";
    end if;

    BinFilePath cat:= "BKLCbi" cat F_str cat ".dat";
    BinFile := Open(BinFilePath, "rb");

    if is_quantum then
       error "Quantum codes are now handled in QECC.m";
    else
	case #F:
	    when 2: Index := GF2Index;
	    when 3: Index := GF3Index;
	    when 4: Index := GF4Index;
	    when 5: Index := GF5Index;
	    when 7: Index := GF7Index;
	    when 8: Index := GF8Index;
	    when 9: Index := GF9Index;
	else
	    error "Internal Error";
	end case;
    end if;

    k_ind := is_quantum select (k+1) else k;

    Seek(BinFile,Index[n][k_ind], 0 );

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

//-------------Now have code creation functions we dont -------------//
//-------------want the user to see ----------//

ConstructionB2Code := function(C,s,j,sp)
//Given a binary linear code, return a new code constructed using the
//ConstructionB2 method

  wordset := words(Dual(C),s: NumWords := 1);
  ExtractRep(~wordset,~word);
 
  return ConstructionB2Code1(C,s,j,Support(word),sp);
end function;


ConstructionB2Code1 := function(C,s,j,I,sp) 
//Give a binary linear code, return a new code constructed using the
//ConstructionB2 method

//this bit is temporary to print out the REAL I
/*
wordset := words(Dual(C),s: NumWords := 1);
ExtractRep(~wordset,~word);
"B2:",Support(word);
*/
////////////////////////////////
 
  Iseq := Sort([i : i in I]);
  J := {x : x in Iseq[1 .. 2 * j + 1]};
  I := I diff J;

/*
    vprint BestCode: "By Shortening at",I;
    vprint BestCode: "and Puncturing at",J;
*/
 
  res := ShortenCode(C,I);
  return (PunctureCode(res,J));
end function;


OctalStringToPoly := function(s)
  P:=PolynomialRing(GF(2));
  s:=&cat[s[i] cat " ": i in [#s..1 by -1]];
  L:=StringToIntegerSequence(s);
  L:=IntegerToSequence(SequenceToInteger(L,8),2);
  return P!L;
end function;
 
OctalChenCode := function(N,L)
  p:=#L;
  n:=N div p;
  P:=PolynomialRing(GF(2));
  LP:=[OctalStringToPoly(s):s in L];
//  if GetVerbose("Code") eq 1 then
//    printf "Common factor: %o\n",GCD(LP);
//  end if;
  f:=P.1^n-1;
  L1:=[[(P.1^i*g) mod f:g in LP]: i in [0..n-1]];
  G:=KMatrixSpace(GF(2),n,N)![
    Coefficient(f,i): i in [0..n-1], f in z,z in L1];
  return LinearCode(G);
end function;
 
SugiyamaCode := function(g);
/*
 
  "Construction P" in
 
  Yasuo Sugiyama, Masao Kasahara, Shigeichi Hirasawa, Toshihiko
  Namekawa,
  Further Results on Goppa Codes and Their Applications to Constructing
  Efficient Binary Codes
  IEEE Transactions on Information Theory, vol. IT-22, no. 5,
  September 1976, pp. 518-526.
*/
 
  R:=Parent(g);
  K:=CoefficientRing(R);
  a:=PrimitiveElement(K);
  m:=Degree(K);
 
// Note that g must be a square; hence we square it here.
 
  F:=Factorisation(g^2);
  s:=#F;
  Z:=[Roots(f[1],SplittingField(f[1]))[1,1]:f  in F];
  s0:=#[f:f  in F|Degree(f[1]) eq 1];
  b:=[f[2]:f in F];
  G:=[f[1]:f in F|Degree(f[1]) gt 1];
 
  t:=Degree(g);
  L:=[x: x in K|not x in Z];
  K:=Parent(Z[1]);
  l:=#L;
 
  H0:=[1/(Z[u]-a)^j: j in [1..b[u]-(u gt s0 select 1 else 3) by 2],
         u in [1..s], a in L];
  H0:=Transpose(KMatrixSpace(K,l,#H0 div l)!H0);
  HU:=[KMatrixSpace(K,1,l)![1/(Z[u]-a)^(b[u]-1): a in L]: u in [1..s0]];
  HI:=KMatrixSpace(K,1,m+1)!([a^i: i in [0..m-1]] cat [0]);
  HJ:=KMatrixSpace(K,1,m+1)!([1: i in [0..m]]);

  HP:=KMatrixSpace(K,m*t+s0,2^m+m*s0)!0;
  InsertBlock(~HP,H0,1,1);
 
  k:=Nrows(H0);
 
  for u:=1 to s0 do
    InsertBlock(~HP,HU[u],k+u,1);
    InsertBlock(~HP,HI,k+u,l+(u-1)*(m+1)+1);
  end for;
 
  for u:=1 to s0 do
    InsertBlock(~HP,HJ,k+s0+u,l+(u-1)*(m+1)+1);
  end for;
 
  IndentPush();
  vprintf Code: "Bounds: ";
  vprintf Code: "n <= %o, ", 2^m+m*s0;
  vprintf Code: "k >= %o, ", 2^m+m*s0-m*t-s0;
  vprintf Code: "d >= %o\n",2*t+1;
  IndentPop();
 
  C:=SubfieldSubcode(Dual(LinearCode(HP)),GF(2));
  C`MinimumWeightLowerBound:=2*t+1;
  return C;
end function;


SugiyamaCodeQ := function(t,t1,L,C);
/*
 
  "Construction Q" in
 
  Yasuo Sugiyama, Masao Kasahara, Shigeichi Hirasawa, Toshihiko
  Namekawa,
  Further Results on Goppa Codes and Their Applications to Constructing
  Efficient Binary Codes
  IEEE Transactions on Information Theory, vol. IT-22, no. 5,
  September 1976, pp. 518-526.
 
  - L is the list of non-zero roots z_u in (25)
  - C is the auxillary code used for the matrix H_B
 
*/
 
  s0:=#L+1;
  //require t+1 ge s0: "Too many roots spezified";
  K:=Universe(L);
  //require Characteristic(K) eq 2: "The constructions works for characteristic
//two only";
 
  m:=Degree(K);
  P:=PolynomialRing(K);
  z:=P.1;
 
  n_prime:=Length(C);
  k_prime:=Dimension(C);
 
  expandMatrix:=function(M);
    F:=CoefficientRing(Parent(M));
    E:=PrimeField(F);
    _,h:=VectorSpace(F,E);
    colMat:=func<x|KMatrixSpace(E,#v,1)!v where v:=Eltseq(h(x))>;
    return VerticalJoin(
          [HorizontalJoin(
            [colMat(M[i,j]): j in [1..Ncols(M)]]):
                i in [1..Nrows(M)]]);
  end function;

  g:=z^(2*(t+1-s0))*&*[P|(z-z_u)^2: z_u in L];
 
  a:=PrimitiveElement(K);
  m:=Degree(K);
 
  F:=Factorisation(g);
 
  s:=#F;
  Z:=[0] cat L;
  b:=[2*(t+1-s0)] cat [2:z_u in L];
 
  non_zeros:=[x: x in K|not x in Z];
  l:=#non_zeros;
 
 
  C_BCH1:=GoppaCode([a^i:i in [1..2^m-s0]],z^(2*t1));
  C_BCH2:=GoppaCode([a^i:i in [1..2^m-s0]],z^(2*(t-s0+1)));
 
 
  d2:=BCHBound(GoppaCode([a^i:i in [1..2^m-1]],z^(2*t1)));
  d1:=BCHBound(GoppaCode([a^i:i in [1..2^m-1]],z^(2*(t-s0+1))));
 
  c1:=Length(C_BCH2)-Dimension(C_BCH2);
  c2:=Length(C_BCH1)-Dimension(C_BCH1);
 
  vprintf Code,3: "m=%o, s0=%o, c1=%o, d1=%o, c2=%o, d2=%o, n'=%o, n'-k'=%o, d'=%o\n",
  m,s0,c1,d1,c2,d2,n_prime,n_prime-k_prime,MinimumWeight(C);
 
  H0:=ParityCheckMatrix(C_BCH1);
  H1:=GeneratorMatrix(CodeComplement(Dual(C_BCH2),Dual(C_BCH1)));
 
  HU:=[expandMatrix(KMatrixSpace(K,1,l)![1/(Z[u]-a)^(b[u]-1): a in non_zeros]): u in [2..s0]];
 
  HB:=ParityCheckMatrix(StandardForm(C));
 
  HA:=KMatrixSpace(GF(2),c1-c2,n_prime)!0;
  for i:=1 to k_prime do
    HA[i,i]:=1;
  end for;
 
  HI:=expandMatrix(KMatrixSpace(K,1,m+1)!([a^i: i in [0..m-1]] cat [0]));
  HJ:=KMatrixSpace(GF(2),1,m+1)!([1: i in [0..m]]);
 
 
  HP:=KMatrixSpace(GF(2),Nrows(H0)+Nrows(H1)+(s0-1)*(m+1)+n_prime-k_prime,Ncols(H0)+Ncols(HA)+(s0-1)*Ncols(HI))!0;
 
  InsertBlock(~HP,H0,1,1);
 
  InsertBlock(~HP,HorizontalJoin(H1,HA),Nrows(H0)+1,1);
 
  k:=Nrows(H0);
 
  for u:=2 to s0 do
    InsertBlock(~HP,HU[u-1],Nrows(H0)+Nrows(H1)+(u-2)*m+1,1);
    InsertBlock(~HP,HI,Nrows(H0)+Nrows(H1)+(u-2)*m+1,Ncols(H0)+Ncols(HA)+(u-2)*(m+1)+1);
  end for;
 
  InsertBlock(~HP,HB,Nrows(H0)+Nrows(H1)+(s0-1)*m+1,Ncols(H0)+1);
 
  for u:=2 to s0 do
    InsertBlock(~HP,HJ,Nrows(H0)+Nrows(H1)+Nrows(HB)+(s0-1)*m+(u-1),Ncols(H0)+Ncols(HB)+(u-2)*(m+1)+1);
  end for;
 
  Ht:=Transpose(HP);
  zero:={i: i in [1..Nrows(Ht)]|Ht[i] eq 0};
  if zero ne {} then
    C:=Dual(ShortenCode(LinearCode(HP),zero));
  else
    C:=Dual(LinearCode(HP));
  end if;
 
  return C;
 
end function;




PGCode1 := function(F,k,L);
  return PGCode(F,k,1,L);
end function;
 
PGCode := function(F,k,s,L);
/*
   Construction "Belov", 
   see A. E. Brouwer, 
   Bounds on the size of linear codes,
   Section 2.4, Theorem 1.
   in: V. S. Pless and W. C. Huffman (eds.), 
   Handbook of Coding Theory, 
   Elsevier, Amsterdam, 1998
 
*/
 
/* TO DO:
 
- treatment of multiplicity of points
- computing bounds
- improvement/verification of the greedy algorithm to find subspaces
 
*/
 
  q:=#F;
 
  P := PolynomialRing(F); x := P.1;
  // s copies of the full projective geometry PG(k-1,q)
 
  PG:={ Normalize(P!Eltseq(v)): v in KSpace(F,k)|v ne 0 };
  PG:=&cat[Setseq(PG): i in [1..s]];
 
  PC:=PG;
 
// find irreducible polynomials of suitable degree
  L_p:=[];
  L_tmp:=[ k-u: u in L ];
  for p in Seqset(PG) do
    if Degree(p) in L_tmp and IsIrreducible(p) then
      Include(~L_p,p);
      Exclude(~L_tmp,Degree(p));
      if #L_tmp eq 0 then 
        break;
      end if;
    end if;
  end for;
 
  subspace:=function(p);
    return {p*P!Eltseq(v): v in KSpace(F,k-Degree(p))|v ne 0};
  end function;
 
// multiplicity is not considered!
  excludedPoints:={};
  for p in L_p do
    U_p:=subspace(p);
    excludedPoints join:=U_p;
    for q in U_p do
      PC:=Exclude(PC,q);
    end for;
  end for;
 
  IndentPush();
 
// test whether all subspaces have been constructed
  if #L_tmp ne 0 then
    L_tmp:=(Sort(L_tmp));
    for u in L_tmp do;
      points:={p: p in PC|Degree(p) eq u};
      if exists(p){p: p in points|
             IsEmpty(subspace(p) meet excludedPoints)} then
        Include(~L_p,p);
        Exclude(~L_tmp,Degree(p));
        U_p:=subspace(p);
        excludedPoints join:=U_p;
        for q in U_p do
          PC:=Exclude(PC,q);
        end for;
        if #L_tmp eq 0 then
          break;
        end if;
      else
        break;
      end if;
    end for;
    if #L_tmp ne 0 then
      if #L_tmp eq 1 then
        vprintf Code: 
          "Warning: Subspace of dimension %o has not been excluded\n",
                     k-L_tmp[1];
      else
        vprintf Code: 
          "Warning: Subspaces of dimensions %o have not been excluded\n",
                     [k-u: u in L_tmp]; 
      end if;
    end if;
  end if;
 
  IndentPop();
 
  G:=KMatrixSpace(F,k,#PC)!
     [Coefficient(f,i): f in PC, i in [0..k-1]];
 
  C:=LinearCode(G);
  return C;
end function;

function MarutaCode(g,n)
//Return the linear code generated by the matrix with columns v*T^i
//where T is the companion matrix of the polynomial g and v is the
//first basis vector of the corresponding vector space

  //require n gt 0: "The length of the code must be non-negative";
  T:=CompanionMatrix(Normalize(g));
  k:=Nrows(T);
  v0:=KSpace(CoefficientRing(T),k).1;
  gens:=[i eq 1 select v0 else Self(i-1)*T:i in [1..n]];
  c:=LinearCode(Transpose(Matrix(gens)));
  return c;
end function;

function MarutaCode1(g,n,L)
//Return the linear code generated by the matrix with columns v*T^i
//where T is the companion matrix of the polynomial g and v is the
//first basis vector of the corresponding vector space, 
//appending the vectors in L

  //require n gt 0: "The length of the code must be non-negative";
  T:=CompanionMatrix(Normalize(g));
  k:=Nrows(T);
  v0:=KSpace(CoefficientRing(T),k).1;
  gens:=[i eq 1 select v0 else Self(i-1)*T:i in [1..n]] cat L;
  c:=LinearCode(Transpose(Matrix(gens)));
  return c;
end function;

function MarutaCode2(g,n,p)
//Return the linear code generated by the matrix with columns v*T^i
//where T is the companion matrix of the polynomial g and v is the
//first basis vector of the corresponding vector space, 
//deleting the p-th column

  //require n gt 0: "The length of the code must be non-negative";
  T:=CompanionMatrix(Normalize(g));
  k:=Nrows(T);
  v0:=KSpace(CoefficientRing(T),k).1;
  gens:=[i eq 1 select v0 else Self(i-1)*T:i in [1..n]];
  c:=PunctureCode(LinearCode(Transpose(Matrix(gens))),p);
  return c;
end function;
