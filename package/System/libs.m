freeze;
 
intrinsic LibFileOpen(N::MonStgElt, M::MonStgElt) -> File
{Open lib file N in mode M}

    t, F := OpenTest(N, M);
    if not t then
        printf
"Runtime error: The file %o
either does not exist or cannot be read.  If you do not have the file
it may be acquired from http://magma.maths.usyd.edu.au/ ; otherwise, the
library root must be set to the right location.  This can be done by
setting the environment variable MAGMA_LIBRARY_ROOT before invoking Magma,
or by using the intrinsic SetLibraryRoot() during a session.\n", N;
        error "";
    end if;

    return F;
end intrinsic;
