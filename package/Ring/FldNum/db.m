freeze;

intrinsic NumberFields(D::DB, n::RngIntElt) -> SeqEnum[FldNum]
{The sequence of number fields of discriminant n contained in D}
    return NumberFields(sub<D|n,n>);
end intrinsic;

intrinsic NumberOfFields(D::DB, n::RngIntElt) -> RngIntElt
{The number of number fields of discriminant n contained in D}
    return #sub<D|n,n>;
end intrinsic;

