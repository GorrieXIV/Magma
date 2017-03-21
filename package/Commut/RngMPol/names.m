freeze;

intrinsic AssignNamesBase(~I::RngMPol, B::MonStgElt)
{Assign the names of I to be B1, B2, ..., using the value of B as the
base}
    AssignNames(~I, [Sprintf("%o%o", B, i): i in [1 .. Rank(I)]]);
end intrinsic;
