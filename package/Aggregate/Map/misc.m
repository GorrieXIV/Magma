freeze;


intrinsic '^'( a::Map, n::RngIntElt ) -> Map
{ The n-th power of the map a }
     // Let '*' and Inverse do all the necessary checks...
     
     
     // for negative exponents inverse first and then exponentiate
       if    n    lt 0 then   return Inverse(a)^(-n);

     // domain and codomain must match for this to be well defined:
     elif    n    eq 0 then   require Domain(a) cmpeq Codomain(a) : "Domain and Codomain of the map must match for this to be well defined"; 
                              return map< Domain(a)->Domain(a) | x:->x, x:->x >;

     // nothing left to be done here:
     elif    n    eq 1 then   return a;                   

     // using Russian-farmer-exponentiation here
     elif n mod 2 eq 1 then   return (a*a)^(n div 2) * a; // I guess evaluation of this conditional expression is 'cheaper'
     else                     return (a*a)^(n div 2);     // than the additional recursive function call  a^(n mod 2).
     end if;

end intrinsic;

