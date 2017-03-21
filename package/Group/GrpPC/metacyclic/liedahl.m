freeze;

/* Liedahl (n^3 +12n^2 +(3/12)n +72/56/64)/72

p odd: 3gcd(n,2); 8gcd(n,3)+4gcd(n+1,3)+44

is there a structural explanation for this periodicity?
what does Liedahl say?
what does VLee say?
what does pgpgen tell us

060415
get a good rounding: (n+4-12/n)^3/72 - so about 3 parameters s,t,u
and r determined in terms of n and u
note split are special about n^2 
in Newman-Xu have s,t or u = 0 characterises split

*/

liedahl := function(n);

if n mod 6 eq 0 then return (n^3+12*n^2+12*n+72)/72;

elif n mod 6 eq 1 then return (n^3+12*n^2+3*n+56)/72;

elif n mod 6 eq 2 then return (n^3+12*n^2+12*n+64)/72;

elif n mod 6 eq 3 then return (n^3+12*n^2+3*n+72)/72;

elif n mod 6 eq 4 then return (n^3+12*n^2+12*n+56)/72;

elif n mod 6 eq 5 then return (n^3+12*n^2+3*n+64)/72;

end if;

end function;

for n in [1..100] do

n, liedahl(n), Floor((n+4-12/n)^3/72);

end for;
