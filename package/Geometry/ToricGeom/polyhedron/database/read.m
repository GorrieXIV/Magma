freeze;

/////////////////////////////////////////////////////////////////////////
// read.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38043 $
// $Date: 2012-04-01 01:05:07 +1100 (Sun, 01 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Utility functions for reading from the databases of polytopes.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Database access functions
/////////////////////////////////////////////////////////////////////////

// Returns the block and line number for the given ID and block size.
function ID_to_block( ID, blocksize )
    block := (ID - 1) div blocksize;
    line := (ID - 1) mod blocksize;
    return block, line + 1;
end function;

// Returns the path to the indicated database directory upon success, an empty
// string otherwise.
// Note: A non-empty string does tells you nothing about whether the
// database directory and files actually exist!
function get_database_dir( dbname )
    libs := GetLibraryRoot();
    if #libs eq 0 then return libs; end if;
    return libs[#libs] eq "/" select libs cat "data/polytopes/" cat dbname cat "/"
                                else libs cat "/data/polytopes/" cat dbname cat "/";
end function;

// Returns true along with a file pointer to the requested file upon success,
// false and an error string otherwise.
function open_database_block( dbname, block : name:=false )
    root := get_database_dir( dbname );
    if #root eq 0 then
        return false, "MAGMA_LIBRARY_ROOT not set";
    end if;
    file := root cat "block" cat IntegerToString( block );
    try
        fh := Open( file, "r" );
    catch e
        // The real work is to create a sensible error message
        err := "";
        if assigned e`Object and Type(e`Object) eq MonStgElt then
            idx:=Index( e`Object, ":" );
            if idx gt 0 then
                err := e`Object[idx + 1..#e`Object];
                err := SubstituteString( err, "\\\n", "" );
                err := SubstituteString( err, "\n", " " );
                err := Trim( err );
                err := SubstituteString( err, "  ", " " );
                if #err ne 0 and err[#err] eq "." then Prune( ~err ); end if;
            end if;
        end if;
        if #err eq 0 then
            err := "Unable to open database file " cat file;
        end if;
        if name cmpeq false then name:=dbname; end if;
        return false, err cat ".\n\nThe database \"" cat name cat "\" should be installed in your Magma library directory, in the \"data/polytopes/" cat name cat "\" subdirectory. You can download this database from:\n   http://magma.maths.usyd.edu.au/magma/download/db/";
    end try;
    return true, fh;
end function;

// Upacks the integer into a sequence of vertices.
function upack_vertices( pack, base )
    // First unpack the sequence
    coeffs := IntegerToSequence( pack, base );
    // The first entry is the dimension, the second entry is the shift
    dim := coeffs[1];
    shift := coeffs[2];
    // Shift the coefficients and regroup them as vertices
    coeffs := [Integers() | c - shift : c in coeffs[3..#coeffs]];
    return [PowerSequence(Integers()) |
                    [Integers() | coeffs[dim * i + j] : j in [1..dim]] :
                    i in [0..#coeffs div dim - 1]];
end function;

// Returns true along with the vertices corresponding to the given line of the
// given block file upon success, false and an error string otherwise.
function read_packed_vertices( dbname, block, line : name:=false )
    // Open the requested block file
    bool, fh := open_database_block( dbname, block : name:=name );
    if not bool then return false, fh; end if;
    // The first line of the file contains the base the data is encoded in
    base := Gets( fh );
    if IsEof( base ) then line := -1; end if;
    // Read the requested line
    while line gt 0 do
        s := Gets( fh );
        if IsEof( s ) then
            line := -1;
            break;
        end if;
        line -:= 1;
    end while;
    // Were we successful?
    if line ne 0 then
        if name cmpeq false then name:=dbname; end if;
        return false, "The database \"" cat name cat "\" is corrupted";
    end if;
    // Try to convert the data we've read
    try
        base := StringToInteger( base );
        s := StringToInteger( s );
        verts := upack_vertices( s, base );
    catch e
        if name cmpeq false then name:=dbname; end if;
        return false, "The database \"" cat name cat "\" is corrupted";
    end try;
    // Return the vertices
    return true, verts;
end function;
