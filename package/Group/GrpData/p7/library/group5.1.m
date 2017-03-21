freeze;

import "misc.m": ProcessPresentation; 

Group5_1 := function (p: Process:=true, Select:=func<x|true>)

class:=2;

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


M:=MatrixAlgebra(F,2);
A:=M!0;
B:=A;
C:=A;
A[1][1]:=1;
A[1][2]:=0;
mats:=[];
for x in [0..p-1] do
for y in [1..p-1] do
x1:=F!x;
y1:=F!y;
A[2][1]:=x1;
A[2][2]:=y1;
new:=1;
for m in F do
for n in F do
if (m ne 0) or (n ne 0) then

B[1][1]:=m;
B[1][2]:=n;
B[2][1]:=w*n;
B[2][2]:=m;
C[1][1]:=m+n*x1;
C[1][2]:=n*y1;
C[2][1]:=w*n*y1;
C[2][2]:=m+n*x1;
D:=B*A*C^-1;
if D[1][1] ne 1 or D[1][2] ne 0 then
   print "ARghhh";
end if;
x2:=Integers()!(D[2][1]);
y2:=Integers()!(D[2][2]);
if x2 lt x then
  new:=0;
  break;
end if;
if x2 eq x and y2 lt y then
  new:=0;
  break;
end if;

end if;
end for;
if new eq 0 then
  break;
end if;
end for;

if new eq 1 then
  k:=#mats;
  mats[k+1]:=[x,y];
end if;

end for;
end for;

SQ:={};
for x in [0..p-1] do
  y:=F!x;
  Include(~SQ,y^2);
end for;
INV:={1};
for x in [2..p-1] do
  y:=F!x;
  y:=y^-1;
  z:=Integers()!y;
  if x le z then
    Include(~INV,x);
  end if;
end for;

for x in [2..p-1] do
  y:=F!x;
  if y notin SQ then
    ns:=x;
    break;
  end if;
end for;
//ns is least non-square

Z:=Integers();count :=0;
expect:=(p^2-1) div 2;
if (p mod 3) eq 2 then
  expect:=expect+1;
end if;

xend:=(p-1) div 2;
mats2:=[];

for w3 in [1,ns] do
//The experimental evidence is that w3=1 is enough,
//(i.e. w3=ns never arises), but I don't have a proof
//of this.  However, no time is wasted as the loop
//aborts when the expected number of orbits is found.
w1:=F!w3;
for x in [0..xend] do
x1:=F!x;
for y in [1..p-1] do
y1:=F!y;
if x eq 0 then zend:=(p-1) div 2; else; zend:=p-1; end if;
for z in [0..zend] do
z1:=F!z;

delta:=(w1*z1-y1*x1)^2-w1*y1;
if delta notin SQ then

new:=1;
for a in F do
for b in F do
for d in F do
//We are transforming w3,x,y,z by a non-singular
//2x2 matrix with entries a,b,c,d.
//We need only consider non-zero values of c, and
//we take c=1 and then there is at most one k
//such that ak,bk,c,dk is a possible matrix.
e:=a*d-b;
if e ne 0 then

if b*d*w1 eq a*y1 then
  continue;
end if;

k:=2*(b*d*w1-a*y1)*e^-1;
f:=e^-2*k^-1;

if a*d+b+2*(b*d*x1-a*z1) ne e*d*k then
  continue;
end if;

w2:=Z!(f*(d^3*w1-d*y1-d-d^2*x1+z1));
if w2 lt w3 then
  new:=0;
  break;
end if;
if w2 gt w3 then
  continue;
end if;

x2:=Z!(f*(-b*d^2*w1+b*y1+a*d+a*d^2*x1-a*z1));
if x2 lt x then
  new:=0;
  break;
end if;
if x2 gt x then
  continue;
end if;

y2:=Z!(f*(-b^2*d*w1+d*a^2*y1+a*b+b^2*x1-a^2*z1));
if y2 lt y then
  new:=0;
  break;
end if;
if y2 gt y then
  continue;
end if;

z2:=Z!(f*(b^3*w1-b*a^2*y1-a^2*b-a*b^2*x1+a^3*z1));
if z2 lt z then
  new:=0;
  break;
end if;

end if;
end for;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  n:=#mats2;
  mats2[n+1]:=[w3,x,y,z];
  count:=count+1;
end if;

end if;
if count eq expect then break; end if;
end for;
if count eq expect then break; end if;
end for;
if count eq expect then break; end if;
end for;
if count eq expect then break; end if;
end for;



L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e | (b,a), (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), (d,c),
(e,c), (e,d), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c),
(e,d), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c),
(e,d), a^p, b^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c),
(e,d), a^p, b^p, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c),
(e,d), a^p=(b,a), b^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c),
(e,d), b^p, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c),
(e,d), b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), 
(d,c)=(b,a), (e,c), (e,d), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), 
(d,c)=(b,a), (e,c), (e,d), a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), 
(d,c)=(b,a), (e,c), (e,d), a^p=(b,a), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), 
(d,c)=(b,a), (e,c), (e,d), b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), 
(d,c)=(b,a), (e,c), (e,d), b^p, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,a), (d,a), (e,a), (c,b), (d,b), (e,b), 
(d,c)=(b,a), (e,c), (e,d), b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), (e,d),
a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(b,a), (e,b), (d,c), 
(e,c), (e,d), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), 
(d,c)=(b,a)^w, (e,c), (e,d), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p=(b,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p=(c,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p, c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a)*(c,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a)*(c,a), b^p=(b,a)*(c,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p, d^p, e^p=(b,a)*(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(c,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p=(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p, d^p, e^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c)=(b,a)^w, (e,a), 
(e,b), (e,c), (e,d), a^p=(b,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c)=(b,a)^w, (e,a), 
(e,b), (e,c), (e,d), a^p, b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p=(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(c,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(b,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(c,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p=(b,a)^w, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(b,a), b^p, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), (e,d),
a^p, b^p, c^p, d^p=(b,a), e^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p=(c,a), b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p=(b,a), b^p=(c,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=59;
for x in INV do
count:=count+1;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p=(b,a), c^p=(c,a)^x, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p=(b,a)*(c,a), c^p=(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p=(c,a)^w, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [1..p-1] do
y:=F!x;
if (1+4*y) notin SQ then
count:=count+1;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p=(c,a)^x, c^p=(b,a)*(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
end for;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p=(b,a), b^p, c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b), (d,c), (e,a), (e,b), (e,c), (e,d),
a^p, b^p, c^p=(b,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p=(b,a), c^p=(c,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a)*(c,a)^-1, b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(c,a)^-1, b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+8;
for x in [2..p-1] do
count:=count+1;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a)*(c,a), b^p=(b,a)*(c,a)^x, c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a)*(c,a), b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a)*(c,a), b^p=(c,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p=(c,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(c,a), b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(c,a), b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(c,a)^-1, b^p, c^p, d^p=(c,a), e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p, d^p=(c,a), e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(c,a), b^p, c^p, d^p, e^p=(b,a)*(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(b,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p, d^p=(c,a), e^p=(b,a)*(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p=(c,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(c,a), b^p, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p=(c,a), c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p=(c,a)^w, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p, c^p=(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+14;
for x in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p=(b,a)^x, c^p=(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p=(b,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(c,a), b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p=(c,a), d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p=(b,a), b^p, c^p, d^p, e^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c), (e,a), (e,b), 
(e,c), (e,d), a^p, b^p, c^p=(b,a), d^p, e^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c)=(b,a)^w, (e,a), 
(e,b), (e,c), (e,d), a^p, b^p, c^p=(b,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
for s in mats do
x:=s[1];
y:=s[2];
count:=count+1;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c)=(b,a)^w, (e,a), 
(e,b), (e,c), (e,d), a^p, b^p=(b,a), c^p=(b,a)^x*(c,a)^y, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (c,b), (d,a), (d,b)=(c,a), (d,c)=(b,a)^w, (e,a), 
(e,b), (e,c), (e,d), a^p=(c,a), b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p, d^p=(b,a), e^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p=(b,a), e^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(c,a), d^p=(b,a), e^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(c,a), b^p, c^p, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(b,a), b^p, c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(c,a), b^p, c^p=(b,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(b,a), b^p, c^p=(c,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(c,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p, c^p=(c,a), d^p=(b,a)*(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(c,a), b^p, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(b,a), b^p, c^p=(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+13;
for x in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(b,a), c^p=(c,a)^x, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(b,a), c^p=(c,a)^x, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(c,a), b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(c,a), b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(b,a), c^p=(b,a)*(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(b,a), c^p=(b,a)*(c,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(b,a), b^p=(c,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(b,a), b^p=(c,a), c^p, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(b,a), b^p=(c,a), c^p=(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p=(c,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p=(b,a), b^p=(c,a), c^p=(c,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^w, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^w, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+15;
for x in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^x*(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b), (e,b), (d,c), (e,c), 
(e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^x*(c,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in INV do
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(b,a), b^p, c^p, d^p=(c,a)^x, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(b,a)*(c,a), b^p, c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a)^w, b^p, c^p, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [1..p-1] do
y:=F!x;
if (1+4*y) notin SQ then
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a)^x, b^p, c^p, d^p=(b,a)*(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
end for;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a), b^p, c^p, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p, d^p=(c,a), e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a), b^p, c^p, d^p=(c,a), e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a), b^p, c^p=(b,a), d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [0..((p-1) div 2)] do
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a),a^p=(c,a)^x,b^p,c^p=(b,a),d^p=(c,a),e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a), b^p, c^p=(b,a)^w, d^p, e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
for x in [0..((p-1) div 2)] do
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a),a^p=(c,a)^x,b^p,c^p=(b,a)^w,d^p=(c,a),e^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a), b^p=(b,a), c^p, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a), b^p=(b,a), c^p, d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p=(c,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p=(c,a), b^p, c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+5;
for x in [0..p-1] do
for y in [x..p-1] do
if (x*y) mod p ne 1 then
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p=(b,a)^x*(c,a), d^p, 
e^p=(b,a)*(c,a)^y>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
end for;
end for;
for x in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p=(b,a)^x, d^p, e^p=(b,a)*(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p, e^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
if p mod 3 eq 1 then
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p, c^p=(b,a), d^p, e^p=(c,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
for s in mats2 do
count:=count+1;
x1:=s[1];
x2:=s[2];
x3:=s[3];
x4:=s[4];
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^x1*(c,a)^x2, d^p, 
e^p=(b,a)^x3*(c,a)^x4>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for y in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p, d^p, e^p=(b,a)^y>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p, d^p=(c,a), e^p=(b,a)^y>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p, d^p, e^p=(b,a)^-1*(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p, d^p=(c,a), 
e^p=(b,a)^-1*(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^w, d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^w, d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
for y in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^y*(c,a), d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
GR:=Group<a,b,c,d,e | (d,a), (e,a), (c,b), (d,b)=(c,a), (e,b), (d,c), 
(e,c), (e,d)=(b,a), a^p, b^p=(c,a), c^p=(b,a)^y*(c,a), d^p=(b,a), e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 5.1 has",count,"descendants order p^7 and p-class 2";

expect:=p^2+15*p+125;
if p eq 3 then
  vprint Orderp7, 2: "Total number of groups is 178";
else;
  vprint Orderp7, 2: "Total number of groups is p^2+15p+125 =",expect;
end if;

if Process then return Nmr; else return L; end if;

end function;

Children42 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_1 (p: Process := Process, Select := Select);
end function;
