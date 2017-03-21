freeze;

intrinsic Polynomial(a::FldFinElt) -> RngUPolElt
{The polynomial over the ground field corresponding to a.}
    return Polynomial(Eltseq(a));
end intrinsic;

intrinsic Polynomial(a::FldFinElt, S::FldFin) -> RngUPolElt
{The polynomial over subfield S corresponding to a.}
    return Polynomial(Eltseq(a));
end intrinsic;
