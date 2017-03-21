freeze;

/* # of immediate descendants of order p^7 for the
   42 capable groups of order dividing p^5 */

CountStep2 := function (p)

X := [
3,  4 ,
5,  p^2+8*p+25 ,
6,  p+6+(p^2+3*p+10)*Gcd (p-1,3) ,
21, 2*p^2+p+3+2*(p+1)*Gcd (p-1,3)+(2*p+4)*Gcd (p-1,4)+Gcd (p-1,8) ,
22,  p^3+p^2+p-2+2*Gcd (p-1,3)+Gcd (p-1,4)+(p+1)*Gcd (p-1,5)  ,
23, p+14 ,
25, p+8 ,
26, 4*p^2+26*p+107+5*Gcd (p-1,3)+(p+4)*Gcd (p-1,4) ,
27,  2*p+7 ,
29,  3*p^2+17*p+53+Gcd (p-1,3)+Gcd (p-1,4) ,
31,  2*p^5+7*p^4+19*p^3+49*p^2+128*p+256+(p^2+7*p+29)*Gcd (p-1,3) 
    +(p^2+7*p+24)*Gcd (p-1,4)+(p+3)*Gcd (p-1,5) ,
32,  3*p^2+12*p+14+(p+2)*Gcd (p-1,4) ,
33,  p^4+2*p^3+5*p^2+14*p ,
34,  3*p^3+6*p^2+6*p+11+(p+7)*Gcd (p-1,3)+(p+1)*Gcd (p-1,4)+Gcd (p-1,5)  ,
39,  p^5+2*p^4+7*p^3+25*p^2+88*p+270+(p+4)*Gcd (p-1,3)+Gcd (p-1,4) ,
41, p^4+5*p^3+19*p^2+64*p+140+(p+6)*Gcd (p-1,3)+(p+7)*Gcd (p-1,4)+Gcd (p-1,5) ,
42, p^2+15*p+125]; 

L := [0: i in [1..42]];
for i in [1..#X div 2] do
   index := X[2 * i - 1];
   entry := X[2 * i];
   L[index] := entry;
end for;
   
return L;

end function;

/* # of descendants (excluding immediate descendants) of order p^7 
   for the 42 capable groups of order dividing p^5 */

CountStep1 := function (p)

L := [ 
 1,
  4,
  15*p+41+16*Gcd (p-1,3)+4*Gcd (p-1,4),
  2,
  5*p+10+2*Gcd (p-1,3)+Gcd (p-1,4),
  p^3+ 3*p^2+8*p+18+5*Gcd (p-1,3)+(p+5)*Gcd (p-1,4)
   +3*Gcd (p-1,5)+2*Gcd (p-1,8)+Gcd (p-1,9),

 3*p^2+4*p+(p+1)*Gcd (p-1,3)+Gcd (p-1,4),
  (p^2+2*p+1+(p+5)*Gcd (p-1,3)+(p+3)*Gcd (p-1,4)) div 2,
  (p^2+2*p+1+(p+5)*Gcd (p-1,3)+(p+3)*Gcd (p-1,4)) div 2,

p+3,
p+1,
3,
0,
4,
4*p+5+(p+7)*Gcd (p-1,3)+3*Gcd (p-1,4)+2*Gcd (p-1,5),
 (p+1) div 2,
 (p+1) div 2,
 7*p+9+4*Gcd (p-1,3)+6*Gcd (p-1,4)+2*Gcd (p-1,5),
 2,
 2,
 4*p+3+2*Gcd (p-1,3)+4*Gcd (p-1,5)+Gcd (p-1,7)+Gcd (p-1,8),
 2*p^2+p+2*p*Gcd (p-1,3)+p*Gcd (p-1,5),
2*p^2 + 63*p +362 +(p + 19)*Gcd (p-1,3) +5*Gcd(p - 1, 4)+Gcd (p - 1, 5),
p^4+ 4*p^3+ 17*p^2+39*p+72+(p^2+9*p+47)*Gcd (p-1,3)
   +(2*p+8)*Gcd (p-1,4)+2*Gcd (p-1,5)+Gcd (p-1,7),
6,
5*p+49+11*Gcd (p-1,3)+4*Gcd (p-1,4),
 5,
 7,
 2*p+20+7*Gcd (p-1,3)+3*Gcd (p-1,4),
 p+1,
 p^2+9*p+36+(p^2+5*p+29)*Gcd (p-1,3)+(p+7)*Gcd (p-1,4)
   +Gcd (p-1,7)+Gcd (p-1,8),
 10*p+16+(2*p+7)*Gcd (p-1,3)+2*Gcd (p-1,4)+2*Gcd (p-1,5),
 p^3+5*p^2+13*p+6+3*Gcd (p-1,3),
 2*p^2+14*p+10+(2*p+8)*Gcd (p-1,3)+7*Gcd (p-1,4)+Gcd (p-1,5),
 0,
 3,
 p^2+10*p+34+(p+14)*Gcd (p-1,3)+13*Gcd (p-1,4)+6*Gcd (p-1,5)+Gcd (p-1,7),
 p^2+7*p+3+2*Gcd (p-1,3)+3*Gcd (p-1,4)+Gcd (p-1,5),
p^3+13*p^2+96*p+595+(3*p+21)*Gcd (p-1,3)+(p+11)*Gcd (p-1,4)+Gcd(p-1,5),
4,
35+(p+15)*Gcd (p-1,3)+4*Gcd (p-1,4),
30];

return L;
end function;


/* number of capable immediate descendants of order p^6 
   of the capables of order dividing p^5 */

NumberCapablep6 := function (p);
L := [
1 ,
 2 ,
 16 ,
 1 ,
 2 ,
 3 ,
 p+1 ,
 1+Gcd (p-1,3)+Gcd (p-1,4)/2 ,
 1+Gcd (p-1,3)+Gcd (p-1,4)/2 ,
 p+1+Gcd (p-1,3) ,
p ,
2 ,
0 ,
1 ,
2+2*Gcd (p-1,3) ,
(p+1)/2 ,
(p+1)/2 ,
3+Gcd (p-1,4) ,
1 ,
1 ,
2 ,
1 ,
-999 , /* not yet known */
5 * p+37+Gcd (p-1,4) ,
2 ,
9 ,
 1 ,
 2 ,
 3 ,
 1 ,
 3 ,
 2*p+9 ,
 4 ,
 11 ,
 0 ,
 1 ,
 4 ,
 1 ,
24 ,
1 ,
2 ,
2 ];
return L;

end function;
