freeze;

import "misc.m": ProcessPresentation; 

Group5_14 := function (p: Process:=true, Select:=func<x|true>, Limit := 0)

if p lt 5 then "5.14 valid only for p>3"; return false; end if;

limited := Limit gt 0;
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

SQ:={};
for x in [1..((p-1) div 2)] do
  y:=x^2 mod p;
  Include(~SQ,y);
end for;
for i in [2..p-1] do
  if i notin SQ then lns:=i; break; end if;
end for;

CU:={1};
for x in [2..p-1] do
  if x^3 mod p eq 1 then Include(~CU,x); end if;
end for;

Z:=Integers();
V1:=VectorSpace(F,1);
V2:=VectorSpace(F,2);
V3:=VectorSpace(F,3);
H12:=Hom(V1,V2);
H22:=Hom(V2,V2);
H32:=Hom(V3,V2);
H33:=Hom(V3,V3);

gtotal:=0;
L:=[]; Nmr := 0;

/*
Descendants of 5.14.

Case 1: cb=caa=cab=cac=0
*/

mats:=[];
//get pc,pb

for y5 in [0,1] do
for y6 in [0,1] do
if y5 eq 1 and y6 eq 1 then continue; end if;
for y3 in [0..p-1] do
for y4 in [0..p-1] do

if y5 eq 1 and y3 ne 0 then continue; end if;
if y6 eq 1 and y4 ne 0 then continue; end if;

A:=H22![y3,y4,y5,y6];
if A eq 0 then
  Append(~mats,A);
  continue;
end if;

new:=1;
index:=p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
for x8 in [1..p-1] do
for x15 in [1..p-1] do

B:=H22![x8,0,0,x15];
C:=H22![x1^2*x8,x1*x2*x8,0,x1*x8^2];

D:=B*A*C^-1;

z3:=Z!(D[1][1]);
z4:=Z!(D[1][2]);
z5:=Z!(D[2][1]);
z6:=Z!(D[2][2]);

if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Append(~mats,A);
  //print y3,y4,y5,y6;
end if;

end for;
end for;
end for;
end for;


count:=0;

for AS in mats do
y3:=Z!(AS[1][1]); y4:=Z!(AS[1][2]); y5:=Z!(AS[2][1]); y6:=Z!(AS[2][2]);
for y1 in [0..p-1] do
for y2 in [0..p-1] do

if y5 eq 1 and y1 ne 0 then continue; end if;
if y6 eq 1 and y2 ne 0 then continue; end if;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(c,a,a),(c,a,b),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
//for x3 in [0..p-1] do
x3:=0;
for x8 in [1..p-1] do
//for x9 in [0..p-1] do
x9:=0;
for x15 in [1..p-1] do

B:=H33![x1,x2,x3,0,x8,x9,0,0,x15];
C:=H22![x1^2*x8,x1*x2*x8,0,x1*x8^2];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

if z5 eq 1 then z3:=0; end if;
if z6 eq 1 then z4:=0; end if;
if z3 ne y3 or z4 ne y4 or z5 ne y5 or z6 ne y6 then continue; end if;


ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b),(c,a,a),(c,a,b),(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y1,y2,y3,y4,y5,y6;
end if;

end for;
end for;

end for;

//print count,3*p+22;
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 2: caa=cab=cac=0, cb=baa
*/

mats:=[];
//get pc,pb

for y5 in [0,1] do
for y6 in [0,1] do
if y5 eq 1 and y6 eq 1 then continue; end if;
for y3 in [0..p-1] do
for y4 in [0..p-1] do

if y5 eq 1 and y3 ne 0 then continue; end if;
if y6 eq 1 and y4 ne 0 then continue; end if;

A:=H22![y3,y4,y5,y6];
if A eq 0 then
  Append(~mats,A);
  continue;
end if;

new:=1;
index:=p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
for x8 in [1..p-1] do
x15:=x1^2;

B:=H22![x8,0,0,x15];
C:=H22![x1^2*x8,x1*x2*x8,0,x1*x8^2];

D:=B*A*C^-1;

z3:=Z!(D[1][1]);
z4:=Z!(D[1][2]);
z5:=Z!(D[2][1]);
z6:=Z!(D[2][2]);

if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Append(~mats,A);
  //print y3,y4,y5,y6;
end if;

end for;
end for;
end for;
end for;


count:=0;

for AS in mats do
y3:=Z!(AS[1][1]); y4:=Z!(AS[1][2]); y5:=Z!(AS[2][1]); y6:=Z!(AS[2][2]);
for y1 in [0..p-1] do
for y2 in [0..p-1] do

if y5 eq 1 and y1 ne 0 then continue; end if;
if y6 eq 1 and y2 ne 0 then continue; end if;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b)=(b,a,a),(c,a,a),(c,a,b),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
//for x3 in [0..p-1] do
x3:=0;
for x8 in [1..p-1] do
//for x9 in [0..p-1] do
x9:=0;
x15:=x1^2;

B:=H33![x1,x2,x3,0,x8,x9,0,0,x15];
C:=H22![x1^2*x8,x1*x2*x8,0,x1*x8^2];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

if z5 eq 1 then z3:=0; end if;
if z6 eq 1 then z4:=0; end if;
if z3 ne y3 or z4 ne y4 or z5 ne y5 or z6 ne y6 then continue; end if;


ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b)=d,(c,a,a),(c,a,b),(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y1,y2,y3,y4,y5,y6;
end if;

end for;
end for;

end for;

//print count,5*p+13+Gcd(p-1,3)+Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 3: cb=bab=bac=cac=0
*/

//first get pb,pc
range:=[[0,1]];
for i in [0..p-1] do
  Append(~range,[1,i]);
end for;
mats:=[];
count:=0;

for y3 in [0,1,lns] do
for y4 in [0,1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H22![y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  Append(~mats,[y3,y4,y5,y6]);
  //print 0,0,0,0;
  continue;
end if;

new:=1;
index:=p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..((p-1) div 2)] do
for r in range do
x8:=r[1]; x9:=r[2];
for x14 in [0..p-1] do
for x15 in [0..p-1] do
if F!(x8*x15-x9*x14) eq 0 then continue; end if;

B:=H22![x8,x9,x14,x15];
C:=H22![x1^2*x8,x1^2*x9,x1^2*x14,x1^2*x15];

D:=B*A*C^-1;

z3:=Z!(D[1][1]);
z4:=Z!(D[1][2]);
z5:=Z!(D[2][1]);
z6:=Z!(D[2][2]);

ind1:=p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  Append(~mats,[y3,y4,y5,y6]);
  //print y3,y4,y5,y6;
end if;

end for;
end for;
end for;
end for;

//now get pa
count:=0;

for SA in mats do
y3:=SA[1]; y4:=SA[2]; y5:=SA[3]; y6:=SA[4];

if F!(y3*y6-y4*y5) ne 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(c,a,a),(c,b),(b,a,b),(b,a,c),(c,a,c),
   a^p,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,y3,y4,y5,y6;
  continue;
end if;

if y3 ne 0 or y4 ne 0 then print "ARgghhh!!!!!"; end if;

for y1 in [0..p-1] do
for y2 in [0..p-1] do

if y1 ne 0 and y5 ne 0 then continue; end if;
if y5 eq 0 and y6 ne 0 and y2 ne 0 then continue; end if;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,b),(b,a,c),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
//for x2 in [0..p-1] do
x2:=0;
//for x3 in [0..p-1] do
x3:=0;
for x8 in [0..p-1] do
for x9 in [0..p-1] do
for x14 in [0..p-1] do
for x15 in [0..p-1] do
if F!(x8*x15-x9*x14) eq 0 then continue; end if;

B:=H33![x1,x2,x3,0,x8,x9,0,x14,x15];
C:=H22![x1^2*x8,x1^2*x9,x1^2*x14,x1^2*x15];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

if z3 ne y3 or z4 ne y4 or z5 ne y5 or z6 ne y6 then continue; end if;
ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(c,a,a),(c,b),(b,a,b),(b,a,c),(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y1,y2,y3,y4,y5,y6;
end if;

end for;
end for;

end for;

//print count,2*p+8+Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 4: bab=bac=cac=0, cb=baa
*/

mats:=[];
//first get pb,pc

for y3 in [0,1,lns] do
for y4 in [0,1] do
if y3 gt 0 and y4 gt 0 then continue; end if;
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H22![y3,y4,y5,y6];
if A eq 0 then
  Append(~mats,A);
  continue;
end if;

new:=1;
index:=p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..((p-1) div 2)] do
for x8 in [1..p-1] do
x9:=0;
for x14 in [0..p-1] do
x15:=x1^2;

B:=H22![x8,x9,x14,x15];
C:=H22![x1^2*x8,x1^2*x9,x1^2*x14,x1^2*x15];

D:=B*A*C^-1;

z3:=Z!(D[1][1]);
if z3 ne y3 then continue; end if;
z4:=Z!(D[1][2]);
if z4 ne y4 then continue; end if;
z5:=Z!(D[2][1]);
z6:=Z!(D[2][2]);

ind1:=p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Append(~mats,A);
  //print y3,y4,y5,y6;
end if;

end for;
end for;
end for;
end for;

count:=0;

for AS in mats do
y3:=Z!(AS[1][1]); y4:=Z!(AS[1][2]); y5:=Z!(AS[2][1]); y6:=Z!(AS[2][2]); 

if F!(y3*y6-y4*y5) ne 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(c,a,a),(c,b)=d,(b,a,b),(b,a,c),(c,a,c),
   a^p,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,y3,y4,y5,y6;
  continue;
end if;

for y1 in [0..p-1] do
for y2 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b)=(b,a,a),(b,a,b),(b,a,c),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
if y3 ne 0 or y4 ne 0 then
  x3:=0;
else;
  x3:=x2;
end if;
for x8 in [1..p-1] do
x9:=0;
for x14 in [0..p-1] do
x15:=x1^2;

B:=H33![x1,x2,x3,0,x8,x9,0,x14,x15];
C:=H22![x1^2*x8,x1^2*x9,x1^2*x14,x1^2*x15];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
if z3 ne y3 then continue; end if;
z4:=Z!(D[2][2]);
if z4 ne y4 then continue; end if;
z5:=Z!(D[3][1]);
if z5 ne y5 then continue; end if;
z6:=Z!(D[3][2]);
if z6 ne y6 then continue; end if;

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(c,a,a),(c,b)=d,(b,a,b),(b,a,c),(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y1,y2,y3,y4,y5,y6;
end if;

end for;
end for;

end for;

//print count,6*p+8+2*Gcd(p-1,3)+Gcd(p-1,4)+Gcd(p-1,5);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 5: cb=bac=cac=0, caa=bab
*/

//first get pc,pb
mats:=[];

for y5 in [0,1] do
range:=[0,1,lns];
if y5 eq 1 then range:=[0]; end if;
for y6 in range do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

A:=H22![y3,y4,y5,y6];
if A eq 0 then
  Append(~mats,A);
  continue;
end if;

new:=1;
index:=p*y3+y4;

for a in [1..p-1] do
for b in [0..p-1] do
for l in [1..p-1] do
for m in [0..p-1] do
n:=(F!a)^-1*(F!l)^2; n:=Z!n;

B:=H22![l,m,0,n];
C:=H22![a^2*l,a^2*m+a*b*l,0,a*l^2];

D:=B*A*C^-1;

z3:=Z!(D[1][1]);
z4:=Z!(D[1][2]);
z5:=Z!(D[2][1]);
z6:=Z!(D[2][2]);
if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Append(~mats,A);
  //print y3,y4,y5,y6;
end if;

end for;
end for;
end for;
end for;

count:=0;

for AS in mats do
y3:=Z!(AS[1][1]); y4:=Z!(AS[1][2]); y5:=Z!(AS[2][1]); y6:=Z!(AS[2][2]); 
for y1 in [0..p-1] do
if y5 ne 0 and y1 ne 0 then continue; end if;
for y2 in [0..p-1] do
if y6 ne 0 and y2 ne 0 then continue; end if;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,c),(c,a,c),(c,a,a)=(b,a,b),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p*y1+y2;

for a in [1..p-1] do
for b in [0..p-1] do
c:=0;
for l in [1..p-1] do
for m in [0..p-1] do
n:=(F!a)^-1*(F!l)^2; n:=Z!n;

B:=H33![a,b,c,0,l,m,0,0,n];
C:=H22![a^2*l,a^2*m+a*b*l,0,a*l^2];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

if z3 ne y3 or z4 ne y4 or z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p*z1+z2;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b),(b,a,c),(c,a,c),(c,a,a)=e,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y1,y2,y3,y4,y5,y6;
end if;

end for;
end for;

end for;

//print count,5*p+13+2*Gcd(p-1,3)+Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 6: bac=cac=0, caa=bab, cb=baa
*/

//get pc

matsc:=[];

for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H12![y5,y6];
if A eq 0 then
  Append(~matsc,A);
  continue;
end if;

new:=1;
index:=p*y5+y6;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
for x8 in [-1,1] do
for x9 in [0..p-1] do

B:=F!(x1^4);
C:=H22![x8*x1^7,x1^4*x9+x8*x1^5*x2,0,x1^8];

D:=B*A*C^-1;

z5:=Z!(D[1][1]);
z6:=Z!(D[1][2]);

ind1:=p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Append(~matsc,A);
  //print y5,y6;
end if;

end for;
end for;

//get pb
matsbc:=[];

for AS in matsc do
y5:=Z!(AS[1][1]); y6:=Z!(AS[1][2]);
for y3 in [0..p-1] do
for y4 in [0..p-1] do

A:=H22![y3,y4,y5,y6];
if A eq 0 then
  Append(~matsbc,A);
  continue;
end if;

new:=1;
index:=p*y3+y4;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
for x8 in [-1,1] do
for x9 in [0..p-1] do

B:=H22![x8*x1^3,x9,0,x1^4];
C:=H22![x8*x1^7,x1^4*x9+x8*x1^5*x2,0,x1^8];

D:=B*A*C^-1;

z3:=Z!(D[1][1]);
z4:=Z!(D[1][2]);
z5:=Z!(D[2][1]);
z6:=Z!(D[2][2]);

if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Append(~matsbc,A);
  //print y3,y4,y5,y6;
end if;

end for;
end for;

end for;

//now get pa

count:=0;

for AS in matsbc do
y3:=Z!(AS[1][1]); y4:=Z!(AS[1][2]); y5:=Z!(AS[2][1]); y6:=Z!(AS[2][2]);
for y1 in [0..p-1] do
if y5 gt 0 and y1 gt 0 then continue; end if;
for y2 in [0..p-1] do
if y6 gt 0 and y2 gt 0 then continue; end if;

A:=H32![y1,y2,y3,y4,y5,y6];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b)=(b,a,a),(b,a,c),(c,a,c),(c,a,a)=(b,a,b),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p*y1+y2;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
x3:=0;
for x8 in [-1,1] do
for x9 in [0..p-1] do

B:=H33![x1^2,x2,x3,0,x8*x1^3,x9,0,0,x1^4];
C:=H22![x8*x1^7,x1^4*x9+x8*x1^5*x2,0,x1^8];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

if z3 ne y3 or z4 ne y4 or z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p*z1+z2;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b)=d,(b,a,c),(c,a,c),(c,a,a)=e,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y1,y2,y3,y4,y5,y6;
end if;

end for;
end for;

end for;

//print count,
//p^2+3*p-3+(p+2)*Gcd(p-1,3)+(p+1)*Gcd(p-1,4)+(p+1)*Gcd(p-1,5);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 7: cb=baa=bac=cac=0
*/

count:=0;

for y1 in [0..w] do
for y2 in [0,1] do
for y3 in [0,1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
if y1 ne 0 and y5 ne 0 then continue; end if;
for y6 in [0..p-1] do
if y5 eq 0 and y6 ne 0 and y2 ne 0 then continue; end if;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,a),(b,a,c),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
//for x3 in [0..p-1] do
x3:=0;
for x8 in [1..p-1] do
for x15 in [1..p-1] do

B:=H33![x1,0,x3,0,x8,0,0,0,x15];
C:=H22![x1*x8^2,0,0,x1^2*x15];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

//if z3 ne y3 or z4 ne y4 or z5 ne y5 or z6 ne y6 then continue; end if;
//if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(c,a,a),(c,b),(b,a,a),(b,a,c),(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,2*p^2+11*p+43+Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 8: cb=caa, baa=bac=cac=0
*/

count:=0;

for y1 in [0..p-1] do
for y2 in [0,1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
if y1 ne 0 and y5 ne 0 then continue; end if;
for y6 in [0..p-1] do
if y5 eq 0 and y6 ne 0 and y2 ne 0 then continue; end if;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b)=(c,a,a),(b,a,a),(b,a,c),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
//for x3 in [0..p-1] do
x3:=0;
//for x8 in [1..p-1] do
x8:=x1^2;
for x15 in [1..p-1] do

B:=H33![x1,0,x3,0,x8,0,0,0,x15];
C:=H22![x1*x8^2,0,0,x1^2*x15];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

//if z3 ne y3 or z4 ne y4 or z5 ne y5 or z6 ne y6 then continue; end if;
//if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(c,a,a),(c,b)=e,(b,a,a),(b,a,c),(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//p^3+4*p^2+6*p+(p+5)*Gcd(p-1,3)+3*Gcd(p-1,4)+Gcd(p-1,5);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Cases 9 & 10: cb=bac=caa=0, cac=kbab (k=1,w)
*/

for k in [1,w] do
count:=0;

for y1 in [0,1] do
for y2 in [0,1,lns] do
for y3 in [0..p-1] do
if y1 eq 1 and y3 gt 0 then continue; end if;
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,c),(c,a,a),(c,a,c)=(b,a,b)^k,a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
for x8 in [1..p-1] do
for x15 in [-1,1] do

B:=H33![x1,x2,0,0,x8,0,0,0,x15*x8];
C:=H22![x1^2*x8,x1*x2*x8,0,x1*x8^2];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

//if z3 ne y3 or z4 ne y4 or z5 ne y5 or z6 ne y6 then continue; end if;
//if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b),(b,a,c),(c,a,a),(c,a,c)=e^k,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//p^3+5*p^2/2+7*p+19/2+(p+4)*Gcd(p-1,4)/2;
gtotal:=gtotal+count;

end for;

/*
Descendants of 5.14.

Cases 11 & 12: bac=caa=0, cb=baa, cac=kbab (k=1,w)
*/

for k in [1,w] do

count:=0;

for y1 in [0..p-1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
if y1 gt 0 and y3 gt 0 then continue; end if;
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do
//y3:=0; y5:=0;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b)=(b,a,a),(b,a,c),(c,a,a),(c,a,c)=(b,a,b)^k,a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for x1 in [1..p-1] do
for x2 in [0..p-1] do
for x8 in [-1,1] do

B:=H33![x1,x2,0,0,x8*x1^2,0,0,0,x1^2];
C:=H22![x1^4*x8,x1^3*x2*x8,0,x1^5];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

//if z3 ne y3 or z5 ne y5 then continue; end if;
//if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b)=d,(b,a,c),(c,a,a),(c,a,c)=e^k,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//(p^4+p^3+4*p^2+p-1+(p^2+2*p+3)*Gcd(p-1,3)+(p+2)*Gcd(p-1,4))/2;
gtotal:=gtotal+count;

end for;

/*
Descendants of 5.14.

Case 13, cb=bac=0, caa=baa, cac=-bab
*/

count:=0;

mats:={};

for y1 in [0..p-1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

A:=H22![y1,y2,y3,y4];
if A eq 0 then
  count:=count+1;
  //print 0,0,0,0;
  Include(~mats,A);
  continue;
end if;

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

for a in [1..p-1] do
for b in [0..p-1] do
for l in [0..p-1] do
for m in [0..p-1] do
if F!(l^2-m^2) eq 0 then continue; end if;

B:=H22![l,m,m,l];
C:=H22![a^2*(l+m),a*b*(l+m),0,a*(l^2-m^2)];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  //print y1,y2,y3,y4;
  Include(~mats,A);
end if;

end for;
end for;
end for;
end for;

//print count,14;
count:=0;

for A in mats do

y1:=Z!(A[1][1]);
y2:=Z!(A[1][2]);
y3:=Z!(A[2][1]);
y4:=Z!(A[2][2]);

for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
index:=p*y5+y6;

A1:=H32![y5,y6,y1,y2,y3,y4];

for a in [1..p-1] do
for b in [0..p-1] do
for l in [0..p-1] do
for m in [0..p-1] do
if F!(l^2-m^2) eq 0 then continue; end if;

B:=H22![l,m,m,l];
C:=H22![a^2*(l+m),a*b*(l+m),0,a*(l^2-m^2)];

D:=B*A*C^-1;
if D ne A then continue; end if;

E:=H33![a,b,-b,0,l,m,0,m,l];
D:=E*A1*C^-1;

z5:=Z!(D[1][1]);
z6:=Z!(D[1][2]);

ind1:=p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b),(b,a,c),(c,a,a)=d,(c,a,c)=e^-1,
   a^p=d^y5*e^y6,b^p=d^y1*e^y2,c^p=d^y3*e^y4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y5,y6,y1,y2,y3,y4;
end if;

end for;
end for;

end for;

//print count,2*p^2+11*p+27+Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 14, bac=0, cb=caa=baa, cac=-bab
*/

count:=0;
r:=(p+1) div 2;

mats:={};

for y1 in [0..p-1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

A:=H22![y1,y2,y3,y4];
if A eq 0 then
  count:=count+1;
  //print 0,0,0,0;
  Include(~mats,A);
  continue;
end if;

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

for a in [1..p-1] do
for b in [0..p-1] do
for x in [1..p-1] do

l:=r*(x+a^2);
m:=r*(x-a^2);

B:=H22![l,m,m,l];
C:=H22![a^2*x,a*b*x,0,a^3*x];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  //print y1,y2,y3,y4;
  Include(~mats,A);
end if;

end for;
end for;
end for;
end for;

//print count;
count:=0;

for A in mats do

y1:=Z!(A[1][1]);
y2:=Z!(A[1][2]);
y3:=Z!(A[2][1]);
y4:=Z!(A[2][2]);

for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
index:=p*y5+y6;

A1:=H32![y5,y6,y1,y2,y3,y4];

for a in [1..p-1] do
for b in [0..p-1] do
for x in [1..p-1] do

l:=r*(x+a^2);
m:=r*(x-a^2);

B:=H22![l,m,m,l];
C:=H22![a^2*x,a*b*x,0,a^3*x];

D:=B*A*C^-1;
if D ne A then continue; end if;

E:=H33![a,b,-b,0,l,m,0,m,l];
D:=E*A1*C^-1;

z5:=Z!(D[1][1]);
z6:=Z!(D[1][2]);

ind1:=p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b)=d,(b,a,c),(c,a,a)=d,(c,a,c)=e^-1,
   a^p=d^y5*e^y6,b^p=d^y1*e^y2,c^p=d^y3*e^y4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print y5,y6,y1,y2,y3,y4;
end if;

end for;
end for;

end for;

//print count,p^3+2*p^2+6*p+10+(p+4)*Gcd(p-1,3);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 15, cb=baa=bac=caa=0
*/

count:=0;

for y1 in [0,1,lns] do
for y2 in [0,1,lns] do
if y1 gt y2 then continue; end if;
for y3 in [0,1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,a),(b,a,c),(c,a,a),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
for b in [1..p-1] do
for c in [1..p-1] do

B:=H33![a,0,0,0,b,0,0,0,c];
C:=H22![a*b^2,0,0,a*c^2];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

//if z3 eq y3 and z6 eq y6 then

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

//end if;

B:=H33![a,0,0,0,0,b,0,c,0];
C:=H22![0,a*b^2,a*c^2,0];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

//if z3 ne y3 or z6 ne y6 then continue; end if;

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;


if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(c,a,c),(c,b),(b,a,a),(b,a,c),(c,a,a),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//p^3+(7*p^2+17*p+59+5*Gcd(p-1,3)+(p+1)*Gcd(p-1,4))/2;
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 16, cb=bac=caa=0, baa=cac
*/

count:=0;

for y1 in [0,1,lns] do
for y2 in [0,1,lns] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do
//y5:=1;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,c),(c,a,a),(c,a,c)=(b,a,a),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
a1:=(F!a)^-1; a1:=Z!a1;
for c in [1..p-1] do

B:=H33![a,0,0,0,a1*c^2,0,0,0,c];
C:=H22![a*c^2,0,0,a1*c^4];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

//if z5 ne y5 then continue; end if;

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b),(b,a,c),(c,a,a),(c,a,c)=d,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//2*p^4+4*p^3+8*p^2+14*p+11+4*Gcd(p-1,3)+3*Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 17, cb=bac=0, cac=baa, caa=bab
*/

count:=0;

for y1 in [0,1,lns] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b),(b,a,c),(c,a,a)=e,(c,a,c)=d,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
for x in CU do

a1:=(F!a)^-1; a1:=Z!a1; c:=a*x;
B:=H33![a,0,0,0,a1*c^2,0,0,0,c];
C:=H22![a*c^2,0,0,a^2*c];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

B:=H33![a,0,0,0,0,a1*c^2,0,c,0];
C:=H22![0,a*c^2,a^2*c,0];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b),(b,a,c),(c,a,a)=e,(c,a,c)=d,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
/*
if p mod 3 ne 1 then
  print p^5+p^4+p^3+p^2+p+2+(p^2+p+1)*Gcd(p-1,4)/2;
else;
  print (p^5+p^4+p^3+p^2+7*p+10)/3+(p^2+p+1)*Gcd(p-1,4)/2;
end if;
*/
//(p^4+2*p^3+3*p^2+4*p+2)*(p-1)/Gcd(p-1,3)+3*p+4+(p^2+p+1)*Gcd(p-1,4)/2;
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 18, cb=bac=0, cac=baa, caa=wbab (p=1mod3 only)
*/
if p mod 3 eq 1 then

count:=0;

for y1 in [0,1,lns] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,c),(c,a,a)=(b,a,b)^w,(c,a,c)=(b,a,a),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
for x in CU do

a1:=(F!a)^-1; a1:=Z!a1; c:=a*x;
B:=H33![a,0,0,0,a1*c^2,0,0,0,c];
C:=H22![a*c^2,0,0,a^2*c];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,b),(c,b),(b,a,c),(c,a,a)=e^w,(c,a,c)=d,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//(2*p^5+2*p^4+2*p^3+2*p^2+14*p+17)/3;
gtotal:=gtotal+count;

end if;

/*
Descendants of 5.14.

Case 19, cb=baa=caa=cac=0
*/

count:=0;

for y1 in [0,1,lns] do
for y2 in [0,1] do
if y1 gt 0 and y2 gt 0 then continue; end if;
for y3 in [0,1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,a),(c,a,a),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
for b in [1..p-1] do
for c in [0..p-1] do
for d in [1..p-1] do

B:=H33![a,0,0,0,b,c,0,0,d];
C:=H22![a*b^2,2*a*b*c,0,a*b*d];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,c),(c,b),(b,a,a),(c,a,a),(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,2*p^2+11*p+27+Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 20, cb=baa=cac, caa=bab
*/

count:=0;

for y1 in [0,1,lns] do
for y2 in [0,1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,a),(c,a,a)=(b,a,b),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
for b in [1..p-1] do

a1:=(F!a)^-1; a1:=Z!a1;

B:=H33![a,0,0,0,b,0,0,0,a1*b^2];
C:=H22![a*b^2,0,0,b^3];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,c),(c,b),(b,a,a),(c,a,a)=d,(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//2*p^4+4*p^3+6*p^2+11*p+11+2*Gcd(p-1,3)+(p+1)*Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 21, cb=caa=cac=0, bab=baa
*/

count:=0;

for y1 in [0,1,lns] do
for y2 in [0,1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
if y1 gt 0 and y5 gt 0 then continue; end if;
for y6 in [0..p-1] do
//y5:=0; y6:=0;

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,b)=(b,a,a),(c,a,a),(c,a,c),a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
for b in [0..p-1] do
for c in [1..p-1] do

B:=H33![a,0,2*b,0,a,b,0,0,c];
C:=H22![a^3,2*a^2*b,0,a^2*c];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

//if z5 ne y5 or z6 ne y6 then continue; end if;

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,a),e=(b,a,c),(c,b),(b,a,b)=d,(c,a,a),(c,a,c),
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//2*p^3+6*p^2+7*p+7+(p+1)*Gcd(p-1,4);
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 22, cb=baa=caa=0, cac=wbab
*/


//first get 3 values for pa

mats:=[[0,0],[0,1]];
y1:=1;
for y2 in [0..p-1] do

A:=H12![y1,y2];
new:=1;
index:=p*y1+y2;

for b in [0..p-1] do
for c in [0..p-1] do
if b+c eq 0 then continue; end if;

C:=H22![w*(w*b^2+c^2),2*w*b*c,2*w^2*b*c,w*(w*b^2+c^2)];

D:=A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);

ind1:=p*z1+z2;

if ind1 lt index then new:=0; end if;

C:=H22![w*(w*b^2+c^2),-2*w*b*c,2*w^2*b*c,-w*(w*b^2+c^2)];

D:=A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);

ind1:=p*z1+z2;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  Append(~mats,[y1,y2]);
end if;

if #mats eq 3 then break; end if;
end for;

//if #mats ne 3 then print "Argghhhhh!!!!"; end if;
//print mats;

count:=0;

for A1 in mats do
y1:=A1[1]; y2:=A1[2];
for y3 in [0,1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,a),(c,a,a),(c,a,c)=(b,a,b)^w,a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
for b in [0..p-1] do
for c in [0..p-1] do
if b+c eq 0 then continue; end if;

B:=H33![a,0,0,0,w*b,c,0,w*c,w*b];
C:=H22![w*a*(w*b^2+c^2),2*w*a*b*c,2*w^2*a*b*c,w*a*(w*b^2+c^2)];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

B:=H33![a,0,0,0,w*b,-c,0,w*c,-w*b];
C:=H22![w*a*(w*b^2+c^2),-2*w*a*b*c,2*w^2*a*b*c,-w*a*(w*b^2+c^2)];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,c),(c,b),(b,a,a),(c,a,a),(c,a,c)=d^w,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,
//(2*p^3+3*p^2+3*p+13-Gcd(p-1,3)+(p+1)*Gcd(p-1,4))/2;
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 23, cb=baa=0, caa=bac, cac=wbab
*/
sol:=0;
if p mod 3 eq 2 then
  //look for solution of 12wx^2=-1
  for x in [1..p-1] do
    if F!(12*w*x^2+1) eq 0 then sol:=x; break; end if;
  end for;
end if;

count:=0;

for y1 in [0,1,lns] do
for y2 in [0..((p-1) div 2)] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

A:=H32![y1,y2,y3,y4,y5,y6];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c|(c,b),(b,a,a),(c,a,a)=(b,a,c),(c,a,c)=(b,a,b)^w,a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do
for b in [-1,1] do

B:=H33![a,0,0,0,a,0,0,0,a*b];
C:=H22![a^3,0,0,a^3*b];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

if p mod 3 eq 2 then
for x in [sol,-sol] do

B:=H33![4*w*x*a,-3*w*x*a,-6*w*x^2*a,
        0,-2*w*x*a,a,
        0,w*a*b,-2*w*x*a*b];
C:=H22![16*w^3*x^3*a^3+4*w^2*x*a^3,-16*w^2*x^2*a^3,
        -16*w^3*x^2*a^3*b,16*w^3*x^3*a^3*b+4*w^2*x*a^3*b];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; end if;

end for;
end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,c),(c,b),(b,a,a),(c,a,a)=e,(c,a,c)=d^w,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

if p mod 3 eq 1 then
  expect:=p^5+p^4+p^3+p^2+p+2+(p^2+p+1)*Gcd(p-1,4)/2;
else;
  expect:=p^5/3+p^4/3+p^3/3+p^2/3+p+2+(p^2+p+1)*Gcd(p-1,4)/2;
end if;
//print count,expect;
gtotal:=gtotal+count;

/*
Descendants of 5.14.

Case 24, cb=baa=0, caa=xbab+bac, cac=wbab
where x is not a value of y(y^2+3w)/(3y^2+w)

p=2 mod 3 only
*/

if p mod 3 eq 2 then

val:={};
for x in [0..p-1] do
  if F!(3*x^2+w) ne 0 then
    a:=F!(x*(x^2+3*w))*(F!(3*x^2+w))^-1;
    Include(~val,Z!a);
  end if;
end for;
for a in [1..p-1] do
  if a notin val then x:=a; break; end if;
end for;
//This is the value of x we need for the presentation

//look for solution of wb^2=-3
for y in [1..p-1] do
  if F!(w*y^2+3) eq 0 then b:=y; break; end if;
end for;

//Get w^-1
winv:=(F!w)^-1; winv:=Z!winv;

count:=0;

for y1 in [0,1,lns] do
range2:=[0..p-1];
if y1 eq 0 then range2:=[0,1,lns]; end if;
for y2 in range2 do
range3:=[0..p-1];
if y1+y2 eq 0 then range3:=[0,1,lns]; end if;
for y3 in range3 do
range4:=[0..p-1];
if y1+y2+y3 eq 0 then range4:=[0,1,lns]; end if;
for y4 in range4 do
range5:=[0..p-1];
if y1+y2+y3+y4 eq 0 then range5:=[0,1,lns]; end if;
for y5 in range5 do
range6:=[0..p-1];
if y1+y2+y3+y4+y5 eq 0 then range6:=[0,1,lns]; end if;
for y6 in range6 do

A:=H32![y1,y2,y3,y4,y5,y6];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,c),(c,b),(b,a,a),(c,a,a)=d^x*e,(c,a,c)=d^w,
   a^p,b^p,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if limited and Nmr ge Limit then
    if Process then return Nmr; else return L; end if;
  end if;
  //print 0,0,0,0,0,0;
  continue;
end if;

new:=1;
index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [1..p-1] do

B:=H33![-4*a,x*a*b+3*a,3*x*winv*a+a*b,
        0,2*a,2*a*b,
        0,2*w*a*b,2*a];

C:=H22![32*a^3,-32*a^3*b,
        -32*w*a^3*b,32*a^3];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; break; end if;

B:=H33![-4*a,-x*a*b+3*a,3*x*winv*a-a*b,
        0,2*a,-2*a*b,
        0,-2*w*a*b,2*a];

C:=H22![32*a^3,32*a^3*b,
        32*w*a^3*b,32*a^3];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);
z5:=Z!(D[3][1]);
z6:=Z!(D[3][2]);

ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;

if ind1 lt index then new:=0; break; end if;

end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(b,a,b),e=(b,a,c),(c,b),(b,a,a),(c,a,a)=d^x*e,(c,a,c)=d^w,
   a^p=d^y1*e^y2,b^p=d^y3*e^y4,c^p=d^y5*e^y6>;
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

//print count,2*(p^5+p^4+p^3+p^2)/3+2*p+3;
gtotal:=gtotal+count;

end if;

vprint Orderp7, 1: "Group 5.14 has",gtotal,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 2p^5+7p^4+19p^3+49p^2+128p+256+(p^2+7p+29)gcd(p-1,3)+
(p^2+7p+24)gcd(p-1,4)+(p+3)gcd(p-1,5) =",
2*p^5+7*p^4+19*p^3+49*p^2+128*p+256+(p^2+7*p+29)*Gcd(p-1,3)+
(p^2+7*p+24)*Gcd(p-1,4)+(p+3)*Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;

Children31 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_14 (p: Process:=Process, Select:=Select);
end function;
