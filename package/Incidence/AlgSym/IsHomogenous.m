freeze;
 
/*

AKS: turned off, 19 Mar 2007, since conflicts with C glue
function glue_symmetric_is_homogeneous().

intrinsic IsHomogeneous(s::AlgSymElt) -> BoolElt
{Return true if the labelling partitions of s are of the same weight}
P:=Partitions(s);
if #P eq 0 then 
   return true;
end if;
m:= Weight(P[1]);
for i in [2..#P] do
    if m ne Weight(P[i]) then
        return false;
    end if;
end for;
return true;
end intrinsic;
*/

/*
intrinsic IsSymmetricSFA(m::RngMPolElt) -> BoolElt, AlgSymElt
{returns true if m is symmetric, second result is the corresponding
symmetric monomial function}
M := SFA(CoefficientRing(Parent(m)): Basis := "Monomial");
res := M!0;
while (not IsZero(m)) do
    l := LeadingMonomial(m);
    if (not IsPartition(Exponents(l))) then return false,M!0; end if;
    sub := Coefficients(l)[1] * Polynomial(M.Exponents(l),Parent(m));
    res := res +  Coefficients(l)[1] * M.Exponents(l);
    m := m - sub;
end while;
return true,res;
end intrinsic;
*/

