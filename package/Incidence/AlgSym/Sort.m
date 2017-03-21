freeze;
 
/*
Removed for internal printing sorting!!

intrinsic Sort(Q::AlgSymElt, compare::UserProgram) -> AlgSymElt
{Sort the partitions of the symmetric function according to the compare function}
    P := Partitions(Q);
    C := Coefficients(Q);
    Sort(~P, compare, ~p);
    v := Vector(C)^p^-1;
    pa := Parent(Q);
    res := Zero(pa);
    for i in [1..#P] do
        c:=v[i] * pa.P[i];
        res +:= c;
    end for;

    return res;
end intrinsic;

intrinsic Sort(Q::AlgSymElt) -> AlgSymElt
{Sort the partitions of the symmetric function according to the lexicographic order}
return Sort(Q, func<x, y | x lt y select -1 else x gt y select 1 else 0>);
end intrinsic;
*/

