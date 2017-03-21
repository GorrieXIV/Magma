freeze;

intrinsic ISA(t::Cat, S::{Cat}) -> BoolElt
{}
    return exists{ 1 : u in S | ISA(t,u) };
end intrinsic;

intrinsic ISA(t::ECat, S::{Cat}) -> BoolElt
{Return whether ISA(t,u) is satisfied for some u in S}
    return exists{ 1 : u in S | ISA(t,u) };
end intrinsic;
