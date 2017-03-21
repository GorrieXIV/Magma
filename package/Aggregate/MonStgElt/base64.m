freeze;

/////////////////////////////////////////////////////////////////////////
// base64.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36858 $
// $Date: 2012-01-09 07:03:09 +1100 (Mon, 09 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Intrinsics to base64 encode/decode data.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic StringToBytes( S::MonStgElt ) -> SeqEnum[RngIntElt]
{Converts a string S to a sequence of bytes (integers in the range 0..255)}
    // Create the look-up tables -- these are all the characters I think
    // the interpreter supports, but I might be wrong
    str:=["\t", "\n", "\r", " ", "!", "\"", "#", "$", "%", "&", "'", "(", ")",
          "*", "+", ",", "-", ".", "/", "0", "1", "2", "3", "4", "5", "6", "7",
          "8", "9", ":", ";", "<", "=", ">", "?", "@", "A", "B", "C", "D", "E",
          "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S",
          "T", "U", "V", "W", "X", "Y", "Z", "[", "\\", "]", "^", "_", "`", "a",
          "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o",
          "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "{", "|", "}",
          "~"];
    val:=[-1, 9, 10, 13, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
          46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62,
          63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
          80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96,
          97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,109, 110, 111,
          112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
          126];
    // Convert the string
    bytes:=[Integers() | val[Index(str,S[i]) + 1] : i in [1..#S]];
    require Index(bytes,-1) eq 0: "String contains illegal characters";
    return bytes;
end intrinsic;

intrinsic BytesToString( S::SeqEnum[RngIntElt] ) -> MonStgElt
{Converts a sequence of bytes (integers in the range 0..255) to a string}
    // Sanity check
    require &and[s ge 0 and s lt 256 : s in S]:
        "The sequence must be composed of integers in the range 0..255";
    // Create the look-up tables -- these are all the characters I think
    // the interpreter supports, but I might be wrong
    str:=["\t", "\n", "\r", " ", "!", "\"", "#", "$", "%", "&", "'", "(", ")",
          "*", "+", ",", "-", ".", "/", "0", "1", "2", "3", "4", "5", "6", "7",
          "8", "9", ":", ";", "<", "=", ">", "?", "@", "A", "B", "C", "D", "E",
          "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S",
          "T", "U", "V", "W", "X", "Y", "Z", "[", "\\", "]", "^", "_", "`", "a",
          "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o",
          "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "{", "|", "}",
          "~"];
    val:=[9, 10, 13, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
          46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62,
          63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
          80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96,
          97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,109, 110, 111,
          112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125,
          126];
    // Convert the bytes to a string
    SS:="";
    for s in S do
        idx:=Index(val,s);
        require idx ne 0:
            "The sequence contains bytes that cannot be represented as a character in Magma";
        SS cat:= str[idx];
    end for;
    return SS;
end intrinsic;

intrinsic BinaryToBytes( B::SeqEnum[RngIntElt] ) -> SeqEnum[MonStgElt]
{Converts a sequence S of binary values (integers in the range 0..1) to a sequence of bytes (integers in the range 0..255). The length of the sequence S must be divisible by 8.}
    // Sanity check
    require IsDivisibleBy(#B,8) and &and[b eq 0 or b eq 1 : b in B]:
        "The sequence must be composed of 0s and 1s, of length divisible by 8";
    // Covert the binary sequence to a byte sequence
    S:=[Integers()|];
    while #B gt 0 do
        byte:=Reverse(B[1..8]);
        B:=B[9..#B];
        Append(~S,&+[ShiftLeft(byte[i],i - 1) : i in [1..8]]);
    end while;
    // Return the result
    return S;
end intrinsic;

intrinsic IsBase64Encoded( S::MonStgElt ) -> BoolElt
{True iff the given string looks like base64 encoded data}
    // Remove any new lines at the end of the string
    if #S eq 0 then return true; end if;
    while #S gt 0 and (S[#S] eq "\n" or S[#S] eq "\r") do
        Prune(~S);
    end while;
    if #S eq 0 then return true; end if;
    // Check the end of the string for padding (indicated by =) and remove it
    if S[#S] eq "=" then
        Prune(~S);
        if #S eq 0 then return false; end if;
        while #S gt 0 and (S[#S] eq "\n" or S[#S] eq "\r") do
            Prune(~S);
        end while;
        if #S eq 0 then return false; end if;
        if S[#S] eq "=" then
            Prune(~S);
            if #S eq 0 then return false; end if;
        end if;
    end if;
    // Check that the remaining characters are valid
    valid:={"A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
            "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
            "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
            "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "+", "/", "\n",
            "\r"};
    return &and[S[i] in valid : i in [1..#S]];
end intrinsic;

intrinsic Base64Encode( B::SeqEnum[RngIntElt] : length:=76 ) -> MonStgElt
{Encodes the sequence of bytes (integers in the range 0..255) using base64 encoding}
    // Sanity check
    require &and[b ge 0 and b lt 256 : b in B]:
        "The sequence must be composed of integers in the range 0..255";
    require Type(length) eq RngIntElt and length gt 0 and length le 76:
        "Parameter 'length' must be an integer in the range 1..76";
    // Create the character map 
    alpha:=["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
            "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
            "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
            "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "+", "/"];
    // Add padding to the bytes if necessary
    padding:=#B mod 3;
    if padding eq 1 then
        Append(~B,0);
        Append(~B,0);
    elif padding eq 2 then
        Append(~B,0);
    end if;
    // Start base64 encoding the bytes
    str:="";
    stack:=[Integers()|];
    linelen:=0;
    for b in B do
        stack cat:= Reverse([Integers() |
                               ModByPowerOf2(ShiftRight(b,i),1) : i in [0..7]]);
        while #stack ge 6 do
            bin:=Reverse(stack[1..6]);
            stack:=stack[7..#stack];
            idx:=&+[ShiftLeft(bin[i],i - 1) : i in [1..6]];
            str cat:= alpha[idx + 1];
            linelen +:= 1;
            if linelen eq length then
                str cat:= "\n";
                linelen:=0;
            end if;
        end while;
    end for;
    // Remove any trailing newline
    if str[#str] eq "\n" then Prune(~str); end if;
    // Add padding to the base64 encoded string
    if padding eq 1 then
        if str[#str - 1] eq "\n" then
            str:=str[1..#str - 3] cat "=\n=";
        else
            str:=str[1..#str - 2] cat "==";
        end if;
    elif padding eq 2 then
        str:=str[1..#str - 1] cat "=";
    end if;
    // Return the string
    return str;
end intrinsic;

intrinsic Base64Encode( S::MonStgElt : length:=76 ) -> MonStgElt
{Encodes the string using base64 encoding}
    // Sanity check
    require Type(length) eq RngIntElt and length gt 0 and length le 76:
        "Parameter 'length' must be an integer in the range 1..76";
    // Perform the encoding
    return Base64Encode( StringToBytes(S) : length:=length );
end intrinsic;

intrinsic Base64EncodeFile( path::MonStgElt : length:=76 ) -> MonStgElt
{}
    // Sanity check
    require #path ne 0: "The path must not be empty";
    require Type(length) eq RngIntElt and length gt 0 and length le 76:
        "Parameter 'length' must be an integer in the range 1..76";
    // Create the character map
    alpha:=["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
            "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
            "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
            "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "+", "/"];
    // Open the file for reading
    F:=Open(path,"r");
    // Start base64 encoding the bytes
    str:="";
    stack:=[Integers()|];
    linelen:=0;
    B:=ReadBytes(F,2187);
    while #B gt 0 do
        for b in B do
            stack cat:= Reverse([Integers() |
                               ModByPowerOf2(ShiftRight(b,i),1) : i in [0..7]]);
            while #stack ge 6 do
                bin:=Reverse(stack[1..6]);
                stack:=stack[7..#stack];
                idx:=&+[ShiftLeft(bin[i],i - 1) : i in [1..6]];
                str cat:= alpha[idx + 1];
                linelen +:= 1;
                if linelen eq length then
                    str cat:= "\n";
                    linelen:=0;
                end if;
            end while;
        end for;
        B:=ReadBytes(F,2187);
    end while;
    // Close the file
    delete F;
    // Add padding if necessary
    if #stack ne 0 then
        padding:=IsDivisibleBy(#stack + 8,6) select 1 else 2;
        bin:=Reverse(stack cat ZeroSequence(Integers(), 6 - #stack));
        idx:=&+[ShiftLeft(bin[i],i - 1) : i in [1..6]];
        str cat:= alpha[idx + 1];
        linelen +:= 1;
        if linelen eq length then
            str cat:= "\n";
            linelen:=0;
        end if;
        str cat:= "=";
        if padding eq 2 then
            linelen +:= 1;
            if linelen eq length then
                str cat:= "\n";
            end if;
            str cat:= "=";
        end if;
    end if;
    // Remove any trailing newline
    if str[#str] eq "\n" then Prune(~str); end if;
    // Return the string
    return str;
end intrinsic;

intrinsic Base64EncodeFile( path::MonStgElt, dest::MonStgElt : length:=76 )
{Encodes the indicated file using base64 encoding}
    // Sanity check
    require #path ne 0: "The path must not be empty";
    require #dest ne 0: "The destination path must not be empty";
    require Type(length) eq RngIntElt and length gt 0 and length le 76:
        "Parameter 'length' must be an integer in the range 1..76";
    // Create the character map
    alpha:=["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
            "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
            "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
            "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "+", "/"];
    // Open the file for reading, and the destination file for writing
    F:=Open(path,"r");
    DF:=Open(dest,"w");
    // Start base64 encoding the bytes
    str:="";
    stack:=[Integers()|];
    linelen:=0;
    needbr:=false;
    B:=ReadBytes(F,2187);
    while #B gt 0 do
        for b in B do
            stack cat:= Reverse([Integers() |
                               ModByPowerOf2(ShiftRight(b,i),1) : i in [0..7]]);
            while #stack ge 6 do
                bin:=Reverse(stack[1..6]);
                stack:=stack[7..#stack];
                idx:=&+[ShiftLeft(bin[i],i - 1) : i in [1..6]];
                str cat:= alpha[idx + 1];
                linelen +:= 1;
                if linelen eq length then
                    if needbr then str:="\n" cat str; end if;
                    Write(DF,str);
                    needbr:=true;
                    str:="";
                    linelen:=0;
                end if;
            end while;
        end for;
        B:=ReadBytes(F,2187);
    end while;
    // Close the file
    delete F;
    // Add padding if necessary
    if #stack ne 0 then
        padding:=IsDivisibleBy(#stack + 8,6) select 1 else 2;
        bin:=Reverse(stack cat ZeroSequence(Integers(), 6 - #stack));
        idx:=&+[ShiftLeft(bin[i],i - 1) : i in [1..6]];
        str cat:= alpha[idx + 1];
        linelen +:= 1;
        if linelen eq length then
            if needbr then str:="\n" cat str; end if;
            Write(DF,str);
            needbr:=true;
            str:="";
            linelen:=0;
        end if;
        str cat:= "=";
        if padding eq 2 then
            linelen +:= 1;
            if linelen eq length then
                if needbr then str:="\n" cat str; end if;
                Write(DF,str);
                needbr:=true;
                str:="";
                linelen:=0;
            end if;
            str cat:= "=";
        end if;
    end if;
    // Output the remaining data and close the destination file
    if #str gt 0 then
        if needbr then str:="\n" cat str; end if;
        Write(DF,str);
    end if;
    delete DF;
end intrinsic;

intrinsic Base64Decode( S::MonStgElt ) -> SeqEnum[RngIntElt]
{Decodes the string using base64 decoding. The unencoded data is given as a sequence of bytes (integers in the range 0..255).}
    // Remove any white space and get the degenerate case out of the way
    S:=StripWhiteSpace(S);
    if #S eq 0 then return [Integers()|]; end if;
    // Create the character map 
    alpha:=["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
            "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
            "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
            "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "+", "/"];
    // Remove any padding
    if S[#S] eq "=" then
        Prune(~S);
        if S[#S] eq "=" then
            Prune(~S);
            S cat:= "AA";
            padding:=2;
        else
            S cat:= "A";
            padding:=1;
        end if;
    else
        padding:=0;
    end if;
    // Start base64 decoding the string
    stack:=[Integers()|];
    bytes:=[Integers()|];
    for i in [1..#S] do
        b:=Index(alpha,S[i]) - 1;
        require b ne -1:
            "The string does not represent base64 encoded data";
        stack cat:= Reverse([Integers() |
                               ModByPowerOf2(ShiftRight(b,i),1) : i in [0..5]]);
        while #stack ge 8 do
            bin:=Reverse(stack[1..8]);
            stack:=stack[9..#stack];
            Append(~bytes,&+[ShiftLeft(bin[i],i - 1) : i in [1..8]]);
        end while;
    end for;
    // The stack had better be empty
    require #stack eq 0:
        "The string does not represent base64 encoded data";
    // Drop any padding
    if padding eq 1 then
        Prune(~bytes);
    elif padding eq 2 then
        Prune(~bytes);
        Prune(~bytes);
    end if;
    // Return the bytes
    return bytes;
end intrinsic;

intrinsic Base64DecodeFile( path::MonStgElt ) -> SeqEnum[RngIntElt]
{Decodes the indicated file using base64 decoding. The unencoded data is given as a sequence of bytes (integers in the range 0..255).}
    // Sanity check
    require #path ne 0: "The path must not be empty";
    // Create the character map 
    alpha:=["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
            "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
            "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
            "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "+", "/"];
    // Open the file for reading
    F:=Open(path,"r");
    // Start base64 decoding the file
    padding:=0;
    stack:=[Integers()|];
    bytes:=[Integers()|];
    S:=Gets(F);
    while not IsEof(S) do
        S:=StripWhiteSpace(S);
        for i in [1..#S] do
            if S[i] eq "=" then
                b:=0;
                padding +:= 1;
            else
                require padding eq 0:
                    "The file does not represent base64 encoded data";
                b:=Index(alpha,S[i]) - 1;
                require b ne -1:
                    "The file does not represent base64 encoded data";
            end if;
            stack cat:= Reverse([Integers() |
                               ModByPowerOf2(ShiftRight(b,i),1) : i in [0..5]]);
            while #stack ge 8 do
                bin:=Reverse(stack[1..8]);
                stack:=stack[9..#stack];
                Append(~bytes,&+[ShiftLeft(bin[i],i - 1) : i in [1..8]]);
            end while;
        end for;
        S:=Gets(F);
    end while;
    // Close the file
    delete F;
    // The stack had better be empty
    require #stack eq 0:
        "The file does not represent base64 encoded data";
    // Drop any padding
    if padding eq 1 then
        Prune(~bytes);
    elif padding eq 2 then
        Prune(~bytes);
        Prune(~bytes);
    end if;
    // Return the bytes
    return bytes;
end intrinsic;

intrinsic Base64DecodeFile( path::MonStgElt, dest::MonStgElt )
{Decodes the indicated file using base64 decoding}
    // Sanity check
    require #path ne 0: "The path must not be empty";
    require #dest ne 0: "The destination path must not be empty";
    // Create the character map 
    alpha:=["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
            "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
            "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
            "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "+", "/"];
    // Open the file for reading, and the destination file for writing
    F:=Open(path,"r");
    DF:=Open(dest,"w");
    // Start base64 decoding the file
    padding:=0;
    stack:=[Integers()|];
    bytes:=[Integers()|];
    S:=Gets(F);
    while not IsEof(S) do
        S:=StripWhiteSpace(S);
        for i in [1..#S] do
            if S[i] eq "=" then
                b:=0;
                padding +:= 1;
            else
                require padding eq 0:
                    "The file does not represent base64 encoded data";
                b:=Index(alpha,S[i]) - 1;
                require b ne -1:
                    "The file does not represent base64 encoded data";
            end if;
            stack cat:= Reverse([Integers() |
                               ModByPowerOf2(ShiftRight(b,i),1) : i in [0..5]]);
            while #stack ge 8 do
                bin:=Reverse(stack[1..8]);
                stack:=stack[9..#stack];
                Append(~bytes,&+[ShiftLeft(bin[i],i - 1) : i in [1..8]]);
            end while;
        end for;
        if padding eq 0 then
            WriteBytes(DF,bytes);
            bytes:=[Integers()|];
        end if;
        S:=Gets(F);
    end while;
    // Close the file
    delete F;
    // The stack had better be empty
    require #stack eq 0:
        "The file does not represent base64 encoded data";
    // Drop any padding
    if padding eq 1 then
        Prune(~bytes);
    elif padding eq 2 then
        Prune(~bytes);
        Prune(~bytes);
    end if;
    // Write out any remaining data and close the destination file
    if #bytes ne 0 then WriteBytes(DF,bytes); end if;
    delete DF;
end intrinsic;
