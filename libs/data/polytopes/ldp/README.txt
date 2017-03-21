TO INSTALL
==========

To install place the "ldp" directory inside 
   
    libs/data/polytopes/

where "libs" is your Magma libs directory.

ABOUT
=====

The "ldp" directory contains the database of all LDP-polygons with index <= 17.
This classification is derived in:

    [KKN]  Alexander M. Kasprzyk, Maximilian Kreuzer, Benjamin Nill, "On the
            combinatorial classification of toric log del Pezzo surfaces",
            LMS Journal of Computation and Mathematics, 13 (2010), 33-46.

Each entry in the database has been assigned a unique ID in the range 1..15346.
These ID correspond with the IDs on the Graded Ring Database:

    [GRDB] http://grdb.lboro.ac.uk/forms/toricldp

The format of the files in the "ldp" directory is deliberately transparent; you
are welcome to use this data for your own work, provided that a reference to
the paper [KKN] and a link to [GRDB] is included.

The method for extracting the list of vertices for a given ID is illustrated by
the following Magma code:

    // First we compute which block file to look in
    block := (ID - 1) div 250;
    
    // Now we compute which line number in the file we need
    num := ((ID - 1) mod 250) + 1;
    
    // Open the appropriate block file. The first line tells us the base the
    // data is encoded in. Extract that, then fetch the required line.
    file := "block" cat IntegerToString( block );
    fh := Open( file, "r" );
    base := Gets( fh );
    while num gt 0 do
        line := Gets( fh );
        num -:= 1;
    end while;

    // Convert the base and line into integers
    base := StringToInteger( base );
    line := StringToInteger( line );
    
    // Now unpack the integer into a sequence
    coeffs := IntegerToSequence( line, base );
    
    // The first entry in the sequence is the dimension of the polytope, the
    // second entry is a shift value we'll need
    dim := coeffs[1];
    shift := coeffs[2];
    
    // We need to subtract "shift" from the remaining values.
    coeffs := [ coeffs[i] - shift : i in [3..#coeffs] ];
    
    // Finally collect the coefficients together into groups of the correct
    // dimension
    vertices := [ [ coeffs[dim * i + j] : j in [1..dim] ] :
                                                i in [0..#coeffs div dim - 1]];
