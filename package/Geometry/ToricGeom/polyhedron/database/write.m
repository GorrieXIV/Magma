freeze;

/////////////////////////////////////////////////////////////////////////
// write.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38017 $
// $Date: 2012-03-30 05:06:51 +1100 (Fri, 30 Mar 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Utility functions for creating the databases of polytopes.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Database creation functions
/////////////////////////////////////////////////////////////////////////
// The following procedures are used to create database block files.
// They are included in the distribution for the convenience of any
// users who wish to create their own databases.
/////////////////////////////////////////////////////////////////////////

// Outputs the given collection of vertices to the given block file.
procedure output_block_file( file, vertices )
    // First we need to convert the vertices into flat sequences
    block := [PowerSequence(Integers())|];
    for S in vertices do
        dim := #Representative( S );
        coeffs := &cat S;
        shift := 1 - Minimum( [0] cat coeffs );
        Append( ~block, [dim,shift] cat [c + shift : c in coeffs] );
    end for;
    // Now we need to compute the base we can work in
    base := 1 + Maximum( [Maximum( S ) : S in block] );
    // Create the block file
    fprintf file, "%o\n", base;
    for S in block do
        fprintf file, "%o\n", SequenceToInteger( S, base );
    end for;
end procedure;

// Given a sequence of vertices (given as sequences of integers), the number
// of entries to store per file, and the target directory, this procedure
// will create the "block" files.
procedure generate_block_files( vertices, size, dir )
    // Initialize the data
    i := -1;
    num := size;
    file := "";
    block := [Universe(vertices)|];
    // Start blocking the vertices
    for S in vertices do
        // Do we need to output a block file?
        if num eq size then
            // Output this block
            if i ne -1 then
                output_block_file( file, block );
            end if;
            num := 0;
            i +:= 1;
            file := dir cat "/block" cat IntegerToString( i );
            block := [Universe(vertices)|];
        end if;
        // Add this entry to the current block
        Append( ~block, S );
        num +:= 1;
    end for;
    // Output this block
    if i ne -1 and #block gt 0 then
        output_block_file( file, block );
    end if;
end procedure;
