freeze;

/////////////////////////////////////////////////////////////////////////
// strings.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36857 $
// $Date: 2012-01-09 07:02:03 +1100 (Mon, 09 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// A collection of useful utility functions for manipulating strings.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Functions
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// get_brackets, get_separator
/////////////////////////////////////////////////////////////////////////
// Internal use function to get the bracket information and separator
// information.
/////////////////////////////////////////////////////////////////////////

function get_brackets(brackets)
    error if Type(brackets) ne MonStgElt, "Bracket type must be a string";
    idx := Index(["[","(","{","|","<",""],brackets);
    error if idx eq 0, "Bracket style is unknown";
    if idx ne 6 then
        left := ["[ ","(","{", "| ","<"][idx];
        right := [" ]",")","}"," |",">"][idx];
        brackets := true;
    else
        left := "";
        right := "";
        brackets := false;
    end if;
    return brackets,left,right;
end function;

function get_separator(sep)
    error if Type(sep) ne MonStgElt, "Separator type must be a string";
    idx := Index([",",":",";",""],sep);
    error if idx eq 0, "Separator style is unknown";
    sep := [", "," : ","; "," "][idx];
    return sep;
end function;

//////////////////////////////////////////////////////////////////////
// standardise_widths
//////////////////////////////////////////////////////////////////////
// Input: A sequence of column widths to standardise. Set 'dofirst'
//        to true to also standardise the first column.
//////////////////////////////////////////////////////////////////////
// Will look at the widths and, if it's not too extreme, standardise
// them so that all columns are the same width.
//////////////////////////////////////////////////////////////////////

procedure standardise_widths(~widths, dofirst)
    if #widths le 1 then
        return;
    end if;
    max:=Maximum(widths);
    if max gt 3 then
        max:=3;
    end if;
    if dofirst then
        if widths[1] lt max - 1 then
            widths[1]:=max - 1;
        end if;
    end if;
    for i in [2..#widths] do
        if widths[i] lt max then widths[i]:=max; end if;
    end for;
end procedure;

//////////////////////////////////////////////////////////////////////
// seq_calc_widths
//////////////////////////////////////////////////////////////////////
// Input: A sequence 'S' of sequences all of equal length.
// Ouput: A sequence of length equal to the length of the sequences
// in S. The i-th entry in the sequence equals the maximum number of
// characters requited to output the i-th entry in the subsequences
// of S (where the maximum is over all subsequences in S).
//////////////////////////////////////////////////////////////////////
// Note: S can also be a set, an ordered seq, etc. etc.
//////////////////////////////////////////////////////////////////////

function seq_calc_widths(S)
    error if not Type(S) in [SetEnum,SeqEnum,Tup,SetIndx,List],
                              "seq_calc_widths: Argument is of invalid type";
    // Is there anything to do?
    num_rows := #S;
    if num_rows eq 0 then return [Integers()|]; end if;
    num_cols := #Representative(S);
    error if not &and[#s eq num_cols:s in S],
                           "seq_calc_widths: Entries must be of same length";
    if num_cols eq 0 then return [Integers()|]; end if;
    // Work through the subsequences
    widths:=[0:i in [1..num_cols]];
    for s in S do
        for i in [1..num_cols] do
            w:=#Sprintf("%o",s[i]);
            if w gt widths[i] then widths[i]:=w; end if;
        end for;
    end for;
    return widths;
end function;

//////////////////////////////////////////////////////////////////////
// seq_to_aligned_string
//////////////////////////////////////////////////////////////////////
// Input: A sequence 'S' of sequences all of the same length.
// Set 'brackets' equal to one of "[", "(", "{", "|", "<", or "" to
// suppress brackets. Set 'sep' equal to one of ",", ":", ";", or "" to
// suppress the separator. 'prefix' will be prefixed to each row
// except for the first row, so usually should be "". 'widths' should
// be the value returned by seq_calc_widths() above (although you are
// free to adjust them to force realignment of the columns).
// Output: A string representation of the sequences in 'S', aligned
// vertically (in a similar way to a matrix).
//////////////////////////////////////////////////////////////////////
// Note: S can also be a set, an ordered seq, etc. etc.
//////////////////////////////////////////////////////////////////////

function seq_to_aligned_string(S,widths,brackets,sep,prefix)
    error if not Type(S) in [SetEnum,SeqEnum,Tup,SetIndx,List],
        "seq_to_alligned_string: Argument 1 is of invalid type";
    brackets, left, right := get_brackets(brackets);
    sep := get_separator(sep);
    // Is there anything to do?
    num_rows := #S;
    num_cols := #widths;
    if num_rows eq 0 or num_cols eq 0 then return ""; end if;
    // Construct the strings    
    R:=[];
    for s in S do
        for i in [1..num_cols] do
            r:=Sprintf("%o",s[i]);
            Append(~R,r);
        end for;
    end for;
    // See if it's wise to standardise the column widths
    standardise_widths(~widths,brackets);
    // Create the string
    str:="";
    idx:=1;
    for i in [1..num_rows] do
        // First tack on any prefix
        if i ne 1 then
            if brackets then
                str cat:= Sprintf("%o%o",prefix,left);
            else
                str cat:= Sprintf("%o",prefix);
            end if;
        else
            if brackets then
                str cat:= left;
            end if;
        end if;
        // Now output the weights
        for j in [1..num_cols] do
            diffs:=widths[j]-#R[idx];
            if diffs gt 0 then
                str cat:= &cat[" ":k in [1..diffs]];
            end if;
            if j eq num_cols then
                if i eq num_rows then
                    if brackets then
                        str cat:= Sprintf("%o%o",R[idx],right);
                    else
                        str cat:= Sprintf("%o",R[idx]);
                    end if;
                else
                    if brackets then
                        str cat:= Sprintf("%o%o,\n",R[idx],right);
                    else
                        str cat:= Sprintf("%o,\n",R[idx]);
                    end if;
                end if;
            else
                str cat:= Sprintf("%o%o",R[idx],sep);
            end if;
            idx +:= 1;
        end for;
    end for;
    return str;
end function;

/////////////////////////////////////////////////////////////////////////
// seq_to_string
/////////////////////////////////////////////////////////////////////////
// Input: A sequence Q. Set 'brackets' to one of "[", "(", "{", "|",
// "<", or "" to suppress brackets. Set 'sep' equal to one of ",", ":",
// ";", or "" to suppress the separator.
// Output: A string representation of Q.
/////////////////////////////////////////////////////////////////////////
// Note: Q can also be a set, an ordered seq, etc. etc.
/////////////////////////////////////////////////////////////////////////

function seq_to_string(Q, brackets, sep)
    error if not Type(Q) in [SetEnum,SeqEnum,Tup,SetIndx,List],
        "seq_to_string: Argument 1 is of invalid type";
    brackets, left, right := get_brackets(brackets);
    sep := get_separator(sep);
    // Is there anything to do?
    if #Q eq 0 then
        if brackets then
            return left[#left] eq " " select left[1..#left-1] cat right
                                      else left cat right;
        else
            return "";
        end if;
    end if;
    // Construct the string
    s := &cat[Sprintf("%o",i) cat sep : i in Q];
    if brackets then
        return left cat s[1..#s-#sep] cat right;
    else
        return s[1..#s-#sep];
    end if;
end function;

//////////////////////////////////////////////////////////////////////
// mtrx_to_string
//////////////////////////////////////////////////////////////////////
// Input: A matrix 'A'. Set 'brackets' to one of "[", "(", "{", "|",
// "<", or "" to suppress brackets. Set 'sep' equal to one of ",",
// ":", ";", or "" to suppress the separator. 'prefix' will be prefixed
// to each row except for the first row, so usually should be "".
// Output: A string representation of the matrix 'A'.
//////////////////////////////////////////////////////////////////////

function mtrx_to_string(A, brackets, sep, prefix)
    error if Type(prefix) ne MonStgElt,
        "mtrx_to_string: Argument 4 must be strings";
    brackets, left, right := get_brackets(brackets);
    sep := get_separator(sep);
    // Convert the integers to strings a row at a time and calculate the
    // maximum column string width as we go along
    num_cols := NumberOfColumns(A);
    if num_cols eq 0 and brackets then
        left := left[#left] eq " " select left[1..#left-1] else left;
    end if;
    num_rows := NumberOfRows(A);
    S:=[];
    widths:=[0:i in [1..num_cols]];
    for i in [1..num_rows] do
        for j in [1..num_cols] do
            s:=Sprintf("%o",A[i][j]);
            Append(~S,s);
            if #s gt widths[j] then widths[j]:=#s; end if;
        end for;
    end for;
    // See if it's wise to standardise the column widths
    standardise_widths(~widths,brackets);
    // Create the string
    str:="";
    idx:=1;
    for i in [1..num_rows] do
        if i ne 1 then
            if brackets then
                str cat:= prefix cat left;
            else
                str cat:= prefix;
            end if;
        elif brackets then
            str cat:= left;
        end if;
        for j in [1..num_cols] do
            diffs:=widths[j]-#S[idx];
            if diffs gt 0 then
                str cat:= &cat[" ":k in [1..diffs]];
            end if;
            if j eq num_cols then
                if i eq num_rows then
                    if brackets then
                        str cat:= S[idx] cat right;
                    else
                        str cat:= S[idx];
                    end if;
                else
                    if brackets then
                        str cat:= S[idx] cat right cat "\n";
                    else
                        str cat:= S[idx] cat "\n";
                    end if;
                end if;
            else
                str cat:= S[idx] cat sep;
            end if;
            idx +:= 1;
        end for;
    end for;
    return str;
end function;

//////////////////////////////////////////////////////////////////////
// integer_weights_calc_widths
//////////////////////////////////////////////////////////////////////
// Input: A sequence 'Z' of integer weights.
// Ouput: A sequence of length equal to the dimension of the weights
// in Z. The i-th entry in the sequence equals the maximum number of
// characters requited to output the i-th coefficient of the weights
// of Z (where the maximum is over all weights in Z).
//////////////////////////////////////////////////////////////////////
// Note: Z can also be a set, an ordered seq, etc. etc.
//////////////////////////////////////////////////////////////////////

function integer_weights_calc_widths(Z)
    error if not Type(Z) in [SetEnum,SeqEnum,Tup,SetIndx,List],
                "integer_weights_calc_widths: Argument is of invalid type";
    // Is there anything to do?
    num_rows := #Z;
    if num_rows eq 0 then return [Integers()|]; end if;
    num_cols := #Representative(Z);
    error if not &and[#z eq num_cols:z in Z],
            "integer_weights_calc_widths: Entries must be of same dimension";
    if num_cols eq 0 then return [Integers()|]; end if;
    // Work through the weights calculating the lengths
    widths:=[0:i in [1..num_cols]];
    for z in Z do
        for i in [1..num_cols] do
            w:=#IntegerToString(Integers()!z[i]);
            if w gt widths[i] then widths[i]:=w; end if;
        end for;
    end for;
    return widths;
end function;

//////////////////////////////////////////////////////////////////////
// integer_weights_seq_to_aligned_string
//////////////////////////////////////////////////////////////////////
// Input: A sequence 'Z' of integer weights. 'prefix' will be
// prefixed to each row except for the first row, so usually should
// be "". 'widths' should be the value returned by
// integer_weights_calc_widths() above (although you are free to
// adjust them to force realignment of the columns).
// Output: A string representation of the the weights in 'Z', aligned
// vertically (in a similar way to a matrix).
//////////////////////////////////////////////////////////////////////
// Note: Z can also be a set, an ordered seq, etc. etc.
//////////////////////////////////////////////////////////////////////

function integer_weights_seq_to_aligned_string(Z,widths,dofirst,prefix)
    // Is there anything to do?
    num_rows := #Z;
    num_cols := #widths;
    if num_rows eq 0 or num_cols eq 0 then return ""; end if;
    // Construct the strings    
    S:=[];
    for z in Z do
        for i in [1..num_cols] do
            s:=IntegerToString(Integers()!z[i]);
            Append(~S,s);
        end for;
    end for;
    // See if it's wise to standardise the column widths
    standardise_widths(~widths,dofirst);
    // Create the string
    str:="";
    idx:=1;
    for i in [1..num_rows] do
        // First tack on any prefix
        if i ne 1 then
            str cat:= Sprintf("%o",prefix);
        end if;
        // Now output the weights
        for j in [1..num_cols] do
            diffs:=widths[j]-#S[idx];
            if diffs gt 0 then
                str cat:= &cat[" ":k in [1..diffs]];
            end if;
            if j eq num_cols then
                if i eq num_rows then
                    str cat:= Sprintf("%o",S[idx]);
                else
                    str cat:= Sprintf("%o,\n",S[idx]);
                end if;
            else
                str cat:= Sprintf("%o, ",S[idx]);
            end if;
            idx +:= 1;
        end for;
    end for;
    return str;
end function;

//////////////////////////////////////////////////////////////////////
// quotient_weights_calc_widths
//////////////////////////////////////////////////////////////////////
// Input: A sequence 'Q' of quotient weights.
// Ouput: One integer and one sequence of length equal to the
// dimension of the weights in Q. The integer is the maximum
// number of characters required to output "1/d" (where the maximum
// is over all weights in Q). The i-th entry in the sequence equals
// the maximum number of characters requited to output the i-th
// coefficient of the weights of Q (where the maximum is over all
// weights in Q).
//////////////////////////////////////////////////////////////////////
// Note: Q can also be a set, an ordered seq, etc. etc.
//////////////////////////////////////////////////////////////////////

function quotient_weights_calc_widths(Q)
    error if not Type(Q) in [SetEnum,SeqEnum,Tup,SetIndx,List],
                "quotient_weights_calc_widths: Argument is of invalid type";
    // Is there anything to do?
    num_rows := #Q;
    if num_rows eq 0 then return 0,[Integers()|]; end if;
    num_cols := #Representative(Q);
    error if not &and[#q eq num_cols:q in Q],
            "quotient_weights_calc_widths: Entries must be of same dimension";
    if num_cols eq 0 then return 0,[Integers()|]; end if;
    // Work through the weights calculating the lengths
    width_d:=0;
    widths:=[0:i in [1..num_cols]];
    for q in Q do
        d:=LCM([Denominator(i):i in q]);
        w:=#IntegerToString(d);
        if w gt width_d then width_d:=w; end if;
        for i in [1..num_cols] do
            w:=#IntegerToString(Integers()!(d * q[i]));
            if w gt widths[i] then widths[i]:=w; end if;
        end for;
    end for;
    return width_d+2,widths;
end function;
    
//////////////////////////////////////////////////////////////////////
// quotient_weights_seq_to_aligned_string
//////////////////////////////////////////////////////////////////////
// Input: A sequence 'Q' of quotient weights. 'prefix' will be
// prefixed to each row except for the first row, so usually should
// be "". 'width_d' and 'widths' should be the values returned
// by quotient_weights_calc_widths() above (although you are free to
// adjust them to force realignment of the columns).
// Output: A string representation of the the weights in 'Q', aligned
// vertically (in a similar way to a matrix).
//////////////////////////////////////////////////////////////////////
// Note: Q can also be a set, an ordered seq, etc. etc.
//////////////////////////////////////////////////////////////////////

function quotient_weights_seq_to_aligned_string(Q,width_d,widths,prefix)
    width_d-:=2;
    // Is there anything to do?
    num_rows := #Q;
    num_cols := #widths;
    if num_rows eq 0 or num_cols eq 0 then return ""; end if;
    // Construct the strings    
    d:=[];
    S:=[];
    for q in Q do
        qd:=LCM([Denominator(i) : i in q]);
        Append(~d,IntegerToString(qd));
        for i in [1..num_cols] do
            s:=Sprintf("%o",q[i] * qd);
            Append(~S,s);
        end for;
    end for;
    // See if it's wise to standardise the column widths
    standardise_widths(~widths,true);
    // Create the string
    str:="";
    idx:=1;
    for i in [1..num_rows] do
        // First output the fraction for this quotient weight
        diffs:=width_d - #d[i];
        if i ne 1 then
            str cat:= prefix;
        end if;
        if diffs gt 0 then
            str cat:= &cat[" ":k in [1..diffs]];
        end if;
        str cat:= Sprintf("1/%o( ", d[i]);
        // Now output the weights
        for j in [1..num_cols] do
            diffs:=widths[j]-#S[idx];
            if diffs gt 0 then
                str cat:= &cat[" ":k in [1..diffs]];
            end if;
            if j eq num_cols then
                if i eq num_rows then
                    str cat:= Sprintf("%o )",S[idx]);
                else
                    str cat:= Sprintf("%o ),\n",S[idx]);
                end if;
            else
                str cat:= Sprintf("%o, ",S[idx]);
            end if;
            idx +:= 1;
        end for;
    end for;
    return str;
end function;

/////////////////////////////////////////////////////////////////////////
// need_brackets
/////////////////////////////////////////////////////////////////////////
// Input: A string.
// Output: A string.
/////////////////////////////////////////////////////////////////////////
// Makes a sensible guess whether the given string should be surrounded
// with brackets. For example, "Hom Z^2" would be returned as "(Hom Z^2)"
/////////////////////////////////////////////////////////////////////////

function need_brackets(str)
    error if Type(str) ne MonStgElt, "need_brackets: Input must be a string.";
    // First check that the string isn't already contained in brackets
    len:=#str;
    if len gt 1 and str[1] eq "(" and str[len] eq ")" then
        count:=1;
        for i in [2..len-1] do
            if str[i] eq "(" then
                count+:=1;
            elif str[i] eq ")" then
                count-:=1;
                if count eq 0 then return "(" cat str cat ")"; end if;
            end if;
        end for;
        // If we're here then the string is already bracketed
        return str;
    end if;    
    // Now check whether there are any special characters in the string
    // which might mean we require brackets
    chars:=[" ","^","_","+","-","*","/","(",")"];
    for i in [1..len] do
    if str[i] in chars then
    return "(" cat str cat ")";
    end if;
    end for;
    // If we're here, then it's a harmless string
    return str;
end function;

/////////////////////////////////////////////////////////////////////////
// remove_brackets
/////////////////////////////////////////////////////////////////////////
// Input: A string.
// Output: A string.
/////////////////////////////////////////////////////////////////////////
// Given a string of the form "(S)" returns "S".
/////////////////////////////////////////////////////////////////////////

function remove_brackets(str)
    error if Type(str) ne MonStgElt, "remove_brackets: Input must be a string.";
    // Is the string already contained within brackets?
    len:=#str;
    if len gt 1 and str[1] eq "(" and str[len] eq ")" then
        count:=1;
        for i in [2..len-1] do
            if str[i] eq "(" then
                count+:=1;
            elif str[i] eq ")" then
                count-:=1;
                if count eq 0 then return str; end if;
            end if;
        end for;
        return str[2..len-1];
    end if;
    return str;
end function;

/////////////////////////////////////////////////////////////////////////
// impose_brackets
/////////////////////////////////////////////////////////////////////////
// Input: A string.
// Output: A string.
/////////////////////////////////////////////////////////////////////////
// Makes sure that the given string is enclosed within brackets.
/////////////////////////////////////////////////////////////////////////

function impose_brackets(str)
    error if Type(str) ne MonStgElt, "impose_brackets: Input must be a string.";
    // Is the string already contained within brackets?
    len:=#str;
    if len gt 1 and str[1] eq "(" and str[len] eq ")" then
        count:=1;
        for i in [2..len-1] do
            if str[i] eq "(" then
                count+:=1;
            elif str[i] eq ")" then
                count-:=1;
                if count eq 0 then return "(" cat str cat ")"; end if;
            end if;
        end for;
        return str;
    end if;
    return "(" cat str cat ")";
end function;

/////////////////////////////////////////////////////////////////////////
// cross_prod_string
/////////////////////////////////////////////////////////////////////////
// Input: A string.
// Output: A string.
/////////////////////////////////////////////////////////////////////////
// Given a sequence of strings [str1,str2,...], returns the "cross-product"
// string "str1 x str2 x ...", inserting brackets if necessary.
/////////////////////////////////////////////////////////////////////////

function cross_prod_string(strs)
    error if Type(strs) ne SeqEnum or &or[Type(s) ne MonStgElt:s in strs],
        "cross_prod_string: Input must be a sequence of strings.";
    // Is there anything to do?
    len:=#strs;
    if len eq 0 then
        return "";
    elif len eq 1 then
        return strs[1];
    end if;
    // Construct the cross-product string
    str:=need_brackets(strs[1]);
    power:=1;
    last:=strs[1];
    for i in [2..len] do
        if strs[i] eq last then
            power+:=1;
        else
            if power gt 1 then
                str cat:= "^" cat IntegerToString(power);
                power:=1;
            end if;
            str cat:= " x " cat need_brackets(strs[i]);
            last:=strs[i];
        end if;
    end for;
    if power gt 1 then
        str cat:= "^" cat IntegerToString(power);
    end if;
    return str;
end function;
