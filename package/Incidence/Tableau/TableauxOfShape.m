freeze;

intrinsic TableauxOfShape(part::SeqEnum,m::RngIntElt) -> SetEnum
{Return the Set of all tableaux of shape part and maximal entry m}
requirege m, 0;
require IsPartition(part): "Argument 1 must be Partition";
w := Weight(part);
pp := Partitions(w);
res := {};
for p in pp do
    if p le part and #p le m then
        if #p lt m then
            l := m-#p;
            v := p;
            for i in [1..l] do
                v := Append(v, 0);
            end for;
        else
            v := p;
        end if;

        g := Vector(v)^Sym(m);
        for v in g do
	    res join:= TableauxOnShapeWithContent(part,Eltseq(v));
        end for;
    end if;
end for;
return res;
end intrinsic;
 


intrinsic TableauxOfShape(M::MonTbl,part::SeqEnum,m::RngIntElt) -> SetEnum
{Return the Set of all tableaux of shape part and maximal entry the m-th element of the Monoid M}
require NumberOfLabels(M)    eq 0 or NumberOfLabels(M) ge m: 
   "Argument 3 must <= the number of variables in the first Argument";
requirege m, 0;
require IsPartition(part): "Argument 2 must be Partition";
w := Weight(part);
pp := Partitions(w);
res := {};
for p in pp do
    if p le part and #p le m then
        if #p lt m then
            l := m-#p;
            v := p;
            for i in [1..l] do
                v := Append(v, 0);
            end for;
        else
            v := p;
        end if;
 
        g := Vector(v)^Sym(m);
        for v in g do
	    res join:= TableauxOnShapeWithContent(M,part,Eltseq(v));
        end for;
    end if;
end for;
return res;
end intrinsic;

