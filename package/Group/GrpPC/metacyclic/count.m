freeze;

/*
the Liedahl formula for the number of metacyclic groups order p^n 
for odd primes p 
*/

NumberOfMetacyclicPGroupsOdd := function(n)

if n mod 6 eq 0 then return (n^3+12*n^2+12*n+72)/72;
elif n mod 6 eq 1 then return (n^3+12*n^2+3*n+56)/72;
elif n mod 6 eq 2 then return (n^3+12*n^2+12*n+64)/72;
elif n mod 6 eq 3 then return (n^3+12*n^2+3*n+72)/72;
elif n mod 6 eq 4 then return (n^3+12*n^2+12*n+56)/72;
elif n mod 6 eq 5 then return (n^3+12*n^2+3*n+64)/72;
end if;

end function;

/*
the Liedahl formula for the number of metacyclic groups order 2^n 
*/

NumberOfMetacyclicPGroupsEven := function(n)

if n eq 1 then return 1;
elif n eq 2 then return 2;
elif n eq 3 then return 4;
elif n mod 6 eq 0 then return (n^3+48*n^2-168*n+432)/72;
elif n mod 6 eq 1 then return (n^3+48*n^2-177*n+416)/72;
elif n mod 6 eq 2 then return (n^3+48*n^2-168*n+424)/72;
elif n mod 6 eq 3 then return (n^3+48*n^2-177*n+432)/72;
elif n mod 6 eq 4 then return (n^3+48*n^2-168*n+416)/72;
elif n mod 6 eq 5 then return (n^3+48*n^2-177*n+424)/72;
end if;

end function;

intrinsic NumberOfMetacyclicPGroups (p:: RngIntElt, n :: RngIntElt) -> RngIntElt
{Number of metacyclic groups of order p^n}
    require IsPrime (p): "First argument must be prime";
    require n gt 0: "Second argument must be positive integer";
    if IsOdd (p) then 
       return NumberOfMetacyclicPGroupsOdd (n);
    else 
       return NumberOfMetacyclicPGroupsEven (n);
    end if;
end intrinsic; 
  
