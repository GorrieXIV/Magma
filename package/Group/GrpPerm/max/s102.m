freeze;

import "sympreds.m": ReduciblesSp;
import "superfield.m": GammaSp;
 
get_standard_gens := function(G)
/* 
   Find standard generators of S(8,2). 
   Assumes G is S(8,2).
   Algorithm and code by Derek Holt 13/05/2005
   Standard gens as defined in Birmingham Atlas at that date. 
*/
    P := RandomProcess(G);
    repeat x := Random(P); until Order(x) eq 34; // 1 in 17
    a := x^17; // a is in 2A
    repeat x := Random(P); ord := Order(x); 
	until ord in {11, 33};// 1 in 11
    x := x ^ (ord div 11);
    repeat b := x^Random(P);
        until Order(a*b) eq 15; //1 1n 31
    return a,b;
end function;

S102Identify := function(group: max:= true, Print:=0)

    if Print gt 1 then "making standard group"; end if;
    sp  := Sp(10,2);
    psp := PSp(10,2);
    factor := hom< sp->psp | psp.1, psp.2 >;
    psp := sp @ factor;

    if Print gt 1 then "making homomorphism"; end if;
    a,b := get_standard_gens(group);  
    a1,b1 := get_standard_gens(psp);

    group := sub<group | a,b >;
    homom := hom< group->psp | a1,b1 >;

    psp := sub< psp | a1,b1 >;
    if Print gt 1 then "Calling FPGroupStrong"; end if;
    F, phi := FPGroupStrong(psp);

    maximals:= [];
    if not max then
      return homom, psp, maximals, F, phi;
    end if;

    if Print gt 1 then print "getting reducibles"; end if;
    maximals cat:= [m@factor: m in ReduciblesSp(10, 2)];

    //two imprimitives are non-maximal - preserve orthogonals

    if Print gt 1 then print "getting semilinears"; end if;
    Append(~maximals, GammaSp(10, 2, 5)@factor);

    if Print gt 1 then "getting orthogonals"; end if;
    Append(~maximals,SOPlus(10,2)@factor);
    isit, form := SymplecticForm(SOMinus(10,2));
    assert isit;
    trans := GL(10,2)!CorrectForm(form,10,2,"symplectic");
    Append(~maximals,(SOMinus(10,2)^trans)@factor);

    return homom, psp, maximals, F, phi;

end function;
