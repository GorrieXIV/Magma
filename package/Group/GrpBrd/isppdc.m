freeze;

intrinsic IsProductOfParallelDescendingCycles(s::GrpPermElt) -> BoolElt
{ Return whether p is a product of parallel descending cycles. }

 cycles := Orbits(sub<Parent(s)|s>);
 for i := 1 to #cycles do
    // check whether cycle i is descending
    start := Max(cycles[i]);
    k := start;
    l := k^s;
    while l ne start do
       if l ge k then
          return false;
       end if;
       k := l;
       l := k^s;
    end while;
    for j := i+1 to #cycles do
       // check whether cycles i and j are parallel
       CP := CartesianProduct([cycles[i],cycles[i],cycles[j], cycles[j]]);
       if exists(P){ p : p in CP
                  | (p[1]-p[3])*(p[1]-p[4])*(p[2]-p[3])*(p[2]-p[4]) le 0} then
          return false;
       end if;
    end for;
 end for;

 return true;

end intrinsic;
