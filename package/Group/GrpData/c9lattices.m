freeze;

intrinsic c9LatticeRecord(filename::MonStgElt) -> Rec
{Returns the c9 lattice data (as a record) from the given file}
    fullpath := &cat[ GetLibraryRoot(),  "/c9lattices/", filename ];
    contents := Read(fullpath);
    return eval contents;
end intrinsic;
