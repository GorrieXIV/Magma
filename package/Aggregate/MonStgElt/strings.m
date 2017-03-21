freeze;

/////////////////////////////////////////////////////////////////////////
// strings.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 43732 $
// $Date: 2013-07-04 03:28:44 +1000 (Thu, 04 Jul 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// A collection of useful string utilities.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local constants
/////////////////////////////////////////////////////////////////////////

// A set defining what characters we regard as white space
white:={" ","\n","\r","\t"};
// A string containing the digits 0-9
numbers:="1234567890";
// The strings defining the upper- and lower-case characters
upper_case:="ABCDEFGHIJKLMNOPQRSTUVWXYZ";
lower_case:="abcdefghijklmnopqrstuvwxyz";

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Removes all characters appearing in the set "remv" from the start and
// end of the string S. Returns the trimmed string.
function trim(S,remv)
    endidx:=#S;
    startidx:=1;
    while startidx le endidx and S[startidx] in remv do
        startidx+:=1;
    end while;
    if startidx gt endidx then return ""; end if;
    while endidx ge startidx and S[endidx] in remv do
        endidx-:=1;
    end while;
    return S[startidx..endidx];
end function;

// Attempts to chomp as much of the string 'S', starting at index 'idx',
// into an integer. Returns true if something exists to be converted, false
// otherwise. In either case, the index of the first character that will not
// form part of an integer is returned as the second value. If the end of the
// string was reached, this index is 0. When true, the third return value is
// the integer.
function is_string_integer(S,idx)
    // Skip over any white space
    idx:=IndexOfNonWhiteSpace(S,idx);
    if idx eq 0 then return false,0,_; end if;
    start:=idx;
    // The first value is allowed to be a negative sign, and this is allowed
    // to have white-space after it
    if S[idx] eq "-" then
        new_idx:=IndexOfNonWhiteSpace(S,idx + 1);
        if new_idx eq 0 or Index(numbers,S[new_idx]) eq 0 then
            return false,idx,_;
        end if;
        idx:=new_idx;
    // Otherwise the first value must be an integer
    elif Index(numbers,S[idx]) eq 0 then
        return false,idx,_;
    end if;
    // We loop until we stop encountering numbers
    n:=#S;
    while idx + 1 le n do
        idx +:= 1;
        if Index(numbers,S[idx]) eq 0 then
            return true,IndexOfNonWhiteSpace(S,idx),
                        StringToInteger(S[start..idx - 1]);
        end if;
    end while;
    // If we're here then we successfully parsed to the end of the string
    return true,0,StringToInteger(S[start..#S]);
end function;

// Attempts to chomp as much of the string 'S', starting at index 'idx',
// into a rational. Returns true if something exists to be converted, false
// otherwise. In either case, the index of the first character that will not
// form part of a rational is returned as the second value. If the end of the
// string was reached, this index is 0. When true, the third return value is
// the numerator and the fourth is the denominator (which may be zero!).
function is_string_rational(S,idx)
    // First we attempt to read in a numerator
    bool,next_idx,num:=is_string_integer(S,idx);
    if not bool then return false,next_idx,_,_; end if;
    // Is there a denominator?
    if next_idx eq 0 or S[next_idx] ne "/" then
        return true,next_idx,num,1;
    end if;
    idx:=next_idx;
    bool,next_idx,den:=is_string_integer(S,idx + 1);
    if not bool then return true,idx,num,1; end if;
    return true,next_idx,num,den;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic StripWhiteSpace( S::MonStgElt ) -> MonStgElt
{Removes all white space from the string}
    newS:="";
    while #S gt 0 do
        idxs:=[Integers() | Index(S,s) : s in white];
        idxs:=[Integers() | i : i in idxs | i ne 0];
        if #idxs eq 0 then
            newS cat:= S;
            S:="";
        else
            idx:=Minimum(idxs);
            newS cat:= S[1..idx - 1];
            S:=S[idx + 1..#S];
        end if;
    end while;
    return newS;
end intrinsic;

intrinsic LTrim( S::MonStgElt ) -> MonStgElt
{Removes all white space from the start of the string}
    startidx:=1;
    while startidx le #S and S[startidx] in white do
        startidx+:=1;
    end while;
    return S[startidx..#S];
end intrinsic;

intrinsic RTrim( S::MonStgElt ) -> MonStgElt
{Removes all white space from the end of the string}
    endidx:=#S;
    while endidx ge 1 and S[endidx] in white do
        endidx-:=1;
    end while;
    return S[1..endidx];
end intrinsic;

intrinsic Trim( S::MonStgElt ) -> MonStgElt
{Removes all white space from the start and end of the string}
    return trim(S,white);
end intrinsic;

intrinsic Trim( S::MonStgElt, R::MonStgElt ) -> MonStgElt
{Removes all characters occurring in the string R from the start and end of the string S}
    if #R eq 0 then return S; end if;
    return trim(S,{R[i] : i in [1..#R]});
end intrinsic;

intrinsic CollateWhiteSpace( S::MonStgElt ) -> MonStgElt
{Collects repeated instances of white space into a single " ". Also trims any white space from the start or end of the string.}
    newstr:="";
    inwhite:=true;
    start:=true;
    for i in [1..#S] do
        c:=S[i];
        if inwhite then
            if not c in white then
                inwhite:=false;
                if start then
                    start:=false;
                    newstr cat:= c;
                else
                    newstr cat:= " " cat c;
                end if;
            end if;
        else
            if c in white then
                inwhite:=true;
            else
                newstr cat:= c;
            end if;
        end if;
    end for;
    return newstr;
end intrinsic;

intrinsic IndexOfNonWhiteSpace( S::MonStgElt ) -> RngIntElt
{}
    return IndexOfNonWhiteSpace(S,1);
end intrinsic;

intrinsic IndexOfNonWhiteSpace( S::MonStgElt, k::RngIntElt ) -> RngIntElt
{The index of the first occurrence of a non-white space character (or 0 if no non-white space is found)}
    n:=#S;
    while k le n and S[k] in white do
        k+:=1;
    end while;
    return k le n select k else 0;
end intrinsic;

intrinsic IndexOfFirstWhiteSpace( S::MonStgElt ) -> RngIntElt
{}
    return IndexOfFirstWhiteSpace(S,1);
end intrinsic;

intrinsic IndexOfFirstWhiteSpace( S::MonStgElt, k::RngIntElt ) -> RngIntElt
{The index of the first occurrence of white space in the string (or 0 if no white space is found)}
    n:=#S;
    while k le n and not S[k] in white do
        k+:=1;
    end while;
    return k le n select k else 0;
end intrinsic;

intrinsic Index( S::MonStgElt, T::MonStgElt, k::RngIntElt ) -> RngIntElt
{The first occurrence of the substring T in S, with offset k (or 0 if T is not found)}
    p:=Index(S[k..#S],T);
    return p eq 0 select 0 else p+k-1;
end intrinsic;

intrinsic Position( S::MonStgElt, T::MonStgElt, k::RngIntElt ) -> RngIntElt
{The first occurrence of the substring T in S, with offset k (or 0 if T is not found)}
    p:=Position(S[k..#S],T);
    return p eq 0 select 0 else p+k-1;
end intrinsic;

intrinsic SubstituteString( S::MonStgElt, T::MonStgElt, R::MonStgElt ) -> MonStgElt
{The string formed by replacing every occurrence of T in the string S with R}
    idx:=Position(S,T);
    while idx gt 0 do
        S:=S[1..idx-1] cat R cat S[idx+#T..#S];
        idx:=Position(S,T,idx+#R);
    end while;
    return S;
end intrinsic;

intrinsic StringToLower( S::MonStgElt ) -> MonStgElt
{Convert all characters to lower-case}
    newS:="";
    for i in [1..#S] do
        idx:=Index(upper_case,S[i]);
        newS cat:= idx eq 0 select S[i] else lower_case[idx];
    end for;
    return newS;
end intrinsic;

intrinsic StringToUpper( S::MonStgElt ) -> MonStgElt
{Convert all characters to upper-case}
    newS:="";
    for i in [1..#S] do
        idx:=Index(lower_case,S[i]);
        newS cat:= idx eq 0 select S[i] else upper_case[idx];
    end for;
    return newS;
end intrinsic;

intrinsic Join( S::SeqEnum[MonStgElt], x::MonStgElt ) -> MonStgElt
{Concatenates the strings in S, using deliminator x}
    if #S eq 0 then return ""; end if;
    s:=S[1];
    for i in [2..#S] do
        s cat:= x cat S[i];
    end for;
    return s;
end intrinsic;

intrinsic Reverse( S::MonStgElt ) -> MonStgElt
{Reverse the order of the characters in S}
    newstr:="";
    for i in [#S..1 by -1] do
        newstr cat:= S[i];
    end for;
    return newstr;
end intrinsic;

intrinsic WordWrap( S::MonStgElt, k::RngIntElt : tolerance:=8 ) -> MonStgElt
{Splits the string S into lines of length at most k}
    // Sanity check
    require k gt 1: "Argument 2 must be a positive integer";
    require Type(tolerance) eq RngIntElt and tolerance ge 0:
        "Parameter 'tolerance' must be a non-negative integer";
    // Start building the string
    lastspace:=0;
    linelength:=0;
    newstr:="";
    while #S gt 0 do
        l:=Minimum(k,#S);
        chunk:=Reverse(S[1..l]);
        S:=S[l + 1..#S];
        idx:=Index(chunk,"\n");
        if idx eq 0 then
            idx:=Index(chunk," ");
            if idx eq 0 or idx gt tolerance then
                if #S eq 0 then
                    newstr cat:= Reverse(chunk);
                else
                    newstr cat:= Reverse(chunk) cat "\n";
                end if;
            else
                S:=Reverse(chunk[1..idx - 1]) cat S;
                if #S eq 0 then
                    newstr cat:= Reverse(chunk[idx..#chunk]);
                else
                    newstr cat:= Reverse(chunk[idx..#chunk]) cat "\n";
                end if;
            end if;
        else
            S:=Reverse(chunk[1..idx - 1]) cat S;
            newstr cat:= Reverse(chunk[idx..#chunk]);
        end if;
    end while;
    // Return the string
    return newstr;
end intrinsic;

intrinsic StringToRational( S::MonStgElt ) -> FldRatElt
{The rational corresponding to S}
    bool,idx,num,den:=is_string_rational(S,1);
    require bool and idx eq 0:
        Sprintf("String \"%o\" does not represent a rational number in base 10",S);
    require den ne 0: "Illegal zero denominator";
    return num / den;
end intrinsic;
