
for n in [2,3,4] do 
 "n =", n;
 tr := InverseTransformation(RandomTransformation(n));
 m := tr * RandomModel(n);
 "Minimise"; 
 time
 mm := Minimise(m);
 "Reduce"; 
 time
 rm := Reduce(mm);
 "Equivalence"; 
 time
 assert IsEquivalent(m, mm);
 time
 assert IsEquivalent(m, rm);
end for;
