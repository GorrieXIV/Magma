freeze;

/////////////////////////////////////////////////////////////////////////
// file.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 37558 $
// $Date: 2012-02-27 22:58:22 +1100 (Mon, 27 Feb 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Read from a file, line by line, as a Process.
/////////////////////////////////////////////////////////////////////////
// Example
// -------
// We will use a FileProcess to work through the lines of a file f. For
// each line we output the line number, followed by the length of the
// line.
//
//  P := FileProcess( f );
//  while not IsEmpty( P ) do
//      printf "%o: %o\n", CurrentLabel( P ), #Current( P );
//      Advance( ~P );
//  end while;
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns true along with a file pointer to the requested file upon success,
// false and an error string otherwise.
function open_file(F)
    try
        fh:=Open(F,"r");
    catch e
        // The real work is to create a sensible error message
        err:="";
        if assigned e`Object and Type(e`Object) eq MonStgElt then
            idx:=Index(e`Object,":");
            if idx gt 0 then
                err:=e`Object[idx + 1..#e`Object];
                err:=SubstituteString(err,"\\\n","");
                err:=SubstituteString(err,"\n"," ");
                err:=Trim(err);
                err:=SubstituteString(err,"  "," ");
                if #err ne 0 and err[#err] eq "." then Prune(~err); end if;
            end if;
        end if;
        if #err eq 0 then
            err := "Unable to open file " cat F;
        end if;
        return false, err;
    end try;
    return true,fh;
end function;

// Returns true iff we have reached the end of the file.
function file_is_empty(info)
    return info[1];
end function;

// Advances the file process to the next line.
procedure file_advance(~info)
    error if info[1], "The process has finished.";
    fh:=info[2];
    S:=Gets(fh);
    if IsEof(S) then
        info:=<true>;
    else
        n:=info[4] + 1;
        info:=<false,fh,S,n>;
    end if;
end procedure;

// Returns the current line of the file process.
function file_value(info)
    error if info[1], "The process has finished.";
    return info[3];
end function;

// Returns the current line number of the file process.
function file_label(info)
    error if info[1], "The process has finished.";
    return info[4];
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic FileProcess( F::MonStgElt ) -> Process
{Create a process to read, line by line, the contents of the file with filename F.}
    bool,fh:=open_file(F);
    require bool: fh;
    S:=Gets(fh);
    if IsEof(S) then
        info:=<true>;
    else
        info:=<false,fh,S,1>;
    end if;
    return InternalCreateProcess("File",info,file_is_empty,file_advance,
                                                         file_value,file_label);
end intrinsic;
