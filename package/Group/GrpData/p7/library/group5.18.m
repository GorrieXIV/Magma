freeze;

import "misc.m": ProcessPresentation; 

Group5_18 := function (p: Process:=true, Select:=func<x|true>, Limit := 0)

if p lt 5 then "5.18 valid only for p>3"; return false; end if;

limited := not Process and Limit gt 0;
class:=3;

w:=0;
F:=FiniteField(p);
for i in [2..p-1] do
a:=F!i;
S:={a};
for j in [2..p-1] do
  Include(~S,a^j);
end for;
if #S eq p-1 then
  w:=i;
  break;
end if;
end for;
vprint Orderp7, 2:"p equals",p;
vprint Orderp7, 2:"w equals",w;

Z:=Integers();
V2:=VectorSpace(F,2);
V3:=VectorSpace(F,3);
H22:=Hom(V2,V2);
H32:=Hom(V3,V2);
H33:=Hom(V3,V3);

L:=[]; Nmr := 0;

/*
Descendants of 5.18.

Case cb=0
*/

count:=0;

for y5 in [0..p-1] do
for y6 in [0,1] do
range1:=[0..p-1];
if y5 ne 0 then range1:=[0]; end if;
for y1 in range1 do
range2:=[0..p-1];
if y5 eq 0 and y6 ne 0 then range2:=[0]; end if;
for y2 in range2 do
for y3 in range1 do
for y4 in range2 do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),a^p,b^p=(c,a),c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y5+p^4*y6+p^3*y1+p^2*y2+p*y3+y4;

for a in [1..p-1] do
for e in [1..p-1] do

B:=H33![a,0,0,0,a*e,0,0,0,e];
C:=H22![a^3*e,0,0,a^3*e^2];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z5+p^4*z6+p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(b,a,b),(c,b),a^p=e^y1*f^y2,
                          b^p=d*e^y3*f^y4,c^p=e^y5*f^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y1,y2,y3,y4,y5,y6;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count,3*p^2+7*p+13+5*Gcd(p-1,3);


/*
Descendants of 5.18.

Case cb=baa
*/

//count1:=count;

for y5 in [0..p-1] do
for y6 in [0..p-1] do
range1:=[0..p-1];
if y5 ne 0 then range1:=[0]; end if;
for y1 in range1 do
range2:=[0..p-1];
if y5 eq 0 and y6 ne 0 then range2:=[0]; end if;
for y2 in range2 do
for y3 in range1 do
for y4 in range2 do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b)=(b,a,a),a^p,b^p=(c,a),c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y5+p^4*y6+p^3*y1+p^2*y2+p*y3+y4;

for a in [1..p-1] do

B:=H33![a,0,0,0,a^3,0,0,0,a^2];
C:=H22![a^5,0,0,a^7];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z5+p^4*z6+p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; break; end if;

end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(b,a,b),(c,b)=e,a^p=e^y1*f^y2,
                          b^p=d*e^y3*f^y4,c^p=e^y5*f^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y1,y2,y3,y4,y5,y6;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count-count1,
//3*p^3+3*p^2-p-2+(p+2)*Gcd(p-1,3)+(p+1)*Gcd(p-1,4)+Gcd(p-1,5);

vprint Orderp7, 1: "Group 5.18 has",count,"descendants of order p^7 and class 3";

vprint Orderp7, 2: "Total number of groups is 3p^3 + 6p^2 + 6p + 11 + (p+7)gcd(p-1,3) + (p+1)gcd(p-1,4) + gcd(p-1,5) =",
3*p^3+6*p^2+6*p+11+(p+7)*Gcd(p-1,3)+(p+1)*Gcd(p-1,4)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;

Children34 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_18 (p: Process:=Process, Select:=Select);
end function;
