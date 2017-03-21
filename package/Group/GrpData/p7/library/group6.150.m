freeze;

import "misc.m": ProcessPresentation; 

Group6_150 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.150 valid only for p>3"; return false; end if;

class:=4;

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
V1:=VectorSpace(F,1);
V3:=VectorSpace(F,3);
H31:=Hom(V3,V1);
H33:=Hom(V3,V3);

SQ:={};
for i in [1..((p-1) div 2)] do
  Include(~SQ,i^2 mod p);
end for;
for i in [2..p-1] do
  if i notin SQ then lns:=i; break; end if;
end for;

r:=(p-1) div 2;

gtotal:=0;

L:=[]; Nmr := 0;

/*
Descendants of 6.150

Case 1: baaa=baab=ca-baa=cb=0
*/

count:=0;

for y1 in [0..p-1] do
for y2 in [0..p-1] do
range:=[0,1,lns];
if y1+y2 gt 0 then range:=[0]; end if;
for y3 in range do

A:=H31![y1,y2,y3];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c | (b,a,a,a), (b,a,a,b), (c,a)=(b,a,a), (c,b), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print 0,0,0;
  continue;
end if;

new:=1;
index:=p^2*y1+p*y2+y3;

for a in [1..p-1] do
//for c in [0..p-1] do
for d in [1..p-1] do
//for e in [0..p-1] do
c:=0; e:=0;

B:=H33![a,0,c,
        0,d,e,
        0,0,a*d];

C:=F!(a*d^3);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

end for;
if new eq 0 then break; end if;
end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d | d=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=(b,a,a), (c,b),
                                   a^p=d^y1, b^p=d^y2, c^p=d^y3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print y1,y2,y3;
end if;

end for;
end for;
end for;

gtotal:=gtotal+count;
//print count,4+2*Gcd(p-1,3);

/*
Descendants of 6.150

Case 2: baaa=baab=ca-baa-babb=cb=0
*/

count:=0;

for y1 in [0..p-1] do
for y2 in [0..p-1] do
range:=[0,1,lns];
if y1+y2 gt 0 then range:=[0]; end if;
for y3 in range do

A:=H31![y1,y2,y3];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e,
                                  (c,b), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print 0,0,0;
  continue;
end if;

new:=1;
index:=p^2*y1+p*y2+y3;

//for c in [0..p-1] do
for d in [1..p-1] do
//for e in [0..p-1] do
c:=0; e:=0;

B:=H33![d^2,0,c,
        0,d,e,
        0,0,d^3];

C:=F!(d^5);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(b,a,b,b),(b,a,a,a), (b,a,a,b), (c,a)=d*e,(c,b),
                                   a^p=e^y1, b^p=e^y2, c^p=e^y3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print y1,y2,y3;
end if;

end for;
end for;
end for;

gtotal:=gtotal+count;
//print count,p+2+Gcd(p-1,3)+Gcd(p-1,4);

/*
Descendants of 6.150

Case 3: baaa=baab=babb, ca-baa=cb=0
*/

count:=0;

for y1 in [0..p-1] do
for y2 in [0..p-1] do
range:=[0,1,lns];
if y1 gt 0 then range:=[0]; end if;
for y3 in range do

A:=H31![y1,y2,y3];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,a),(b,a,a,b)=e, (b,a,b,b)=e, 
                                  (c,a)=d*e^-1, (c,b), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print 0,0,0;
  continue;
end if;

new:=1;
index:=p^2*y3+p*y1+y2;

for a in [1..p-1] do
for c in [0..p-1] do

B:=H33![a,0,c,
        0,a,-c,
        0,0,a^2];

C:=F!(a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z3+p*z1+z2;

if ind1 lt index then new:=0; break; end if;

B:=H33![0,a,c,
        a,0,-c,
        0,0,a^2];

C:=F!(-a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z3+p*z1+z2;

if ind1 lt index then new:=0; break; end if;

end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,a),(b,a,a,b)=e, (b,a,b,b)=e, 
                       (c,a)=d*e^-1, (c,b), a^p=e^y1, b^p=e^y2, c^p=e^y3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print y1,y2,y3;
end if;

end for;
end for;
end for;

gtotal:=gtotal+count;
//print count,(p+1+(p+3)*Gcd(p-1,3)+Gcd(p-1,4))/2;

/*
Descendants of 6.150

Case 4: babb+baaa=baab=ca-baa=cb=0
*/

count:=0;

for y1 in [0..p-1] do
for y2 in [0..p-1] do
range:=[0,1,lns];
if y1+y2 gt 0 then range:=[0]; end if;
for y3 in range do

A:=H31![y1,y2,y3];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,a),(b,a,b,b)=e^-1, (b,a,a,b), 
                                  (c,a)=d*e^r, (c,b), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print 0,0,0;
  continue;
end if;

new:=1;
index:=p^2*y1+p*y2+y3;

for a in [1..p-1] do
for b in [1,-1] do
//for c in [0..p-1] do
//for e in [0..p-1] do
c:=0; e:=0;

B:=H33![a*b,0,c,
        0,a,e,
        0,0,a^2];

C:=F!(a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

B:=H33![0,a*b,c,
        a,0,e,
        0,0,a^2];

C:=F!(a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

end for;
if new eq 0 then break; end if;
end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,a),(b,a,b,b)=e^-1, (b,a,a,b), 
                       (c,a)=d*e^r, (c,b), a^p=e^y1, b^p=e^y2, c^p=e^y3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print y1,y2,y3;
end if;

end for;
end for;
end for;

gtotal:=gtotal+count;
//print count,3+Gcd(p-1,3)*(p+3+Gcd(p-1,4))/4;

/*
Descendants of 6.150

Case 5: babb+wbaaa=baab=ca-baa=cb=0
*/

count:=0;

for y1 in [0..p-1] do
for y2 in [0..p-1] do
range:=[0,1];
if y1+y2 gt 0 then range:=[0]; end if;
for y3 in range do

A:=H31![y1,y2,y3];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,a),(b,a,b,b)=e^-w, (b,a,a,b), 
                                  (c,a)=d*e^r, (c,b), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print 0,0,0;
  continue;
end if;

new:=1;
index:=p^2*y1+p*y2+y3;

for a in [1..p-1] do
for b in [1,-1] do
//for c in [0..p-1] do
//for e in [0..p-1] do
c:=0; e:=0;

B:=H33![a*b,0,c,
        0,a,e,
        0,0,a^2];

C:=F!(a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

B:=H33![0,a*b,c,
        w*a,0,e,
        0,0,w*a^2];

C:=F!(w^2*a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

end for;
if new eq 0 then break; end if;
end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,a),(b,a,b,b)=e^-w, (b,a,a,b), 
                       (c,a)=d*e^r, (c,b), a^p=e^y1, b^p=e^y2, c^p=e^y3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print y1,y2,y3;
end if;

end for;
end for;
end for;

gtotal:=gtotal+count;
//print count,2+Gcd(p-1,3)*(p+7-Gcd(p-1,4))/4;

/*
Descendants of 6.150

Case 6: baaa=babb=ca-baa=cb=0
*/

count:=0;

for y1 in [0..p-1] do
for y2 in [0..p-1] do
range:=[0,1];
if y1+y2 gt 0 then range:=[0]; end if;
for y3 in range do

A:=H31![y1,y2,y3];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,b),(b,a,a,a), (b,a,b,b), (c,a)=d*e^r, 
                                  (c,b), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print 0,0,0;
  continue;
end if;

new:=1;
index:=p^2*y1+p*y2+y3;

for a in [1..p-1] do
//for c in [0..p-1] do
for d in [1..p-1] do
//for e in [0..p-1] do
c:=0; e:=0;

B:=H33![a,0,c,
        0,d,e,
        0,0,a*d];

C:=F!(a^2*d^2);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

B:=H33![0,a,c,
        d,0,e,
        0,0,-a*d];

C:=F!(a^2*d^2);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

end for;
if new eq 0 then break; end if;
end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,b),(b,a,a,a), (b,a,b,b), (c,a)=d*e^r, (c,b),
                                   a^p=e^y1, b^p=e^y2, c^p=e^y3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print y1,y2,y3;
end if;

end for;
end for;
end for;

gtotal:=gtotal+count;
//print count,3+Gcd(p-1,3);

/*
Descendants of 6.150

Case 7: babb=baab, baaa=ca-baa=cb=0
*/

count:=0;

for y1 in [0..p-1] do
for y2 in [0..p-1] do
range:=[0,1,lns];
if y1+y2 gt 0 then range:=[0]; end if;
for y3 in range do

A:=H31![y1,y2,y3];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,b),(b,a,b,b)=e, (b,a,a,a), 
                                  (c,a)=d*e^r, (c,b), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print 0,0,0;
  continue;
end if;

new:=1;
index:=p^2*y1+p*y2+y3;

for a in [1..p-1] do
//for c in [0..p-1] do
//for e in [0..p-1] do
c:=0; e:=0;

B:=H33![a,0,c,
        0,a,e,
        0,0,a^2];

C:=F!(a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,b),(b,a,b,b)=e, (b,a,a,a), 
                       (c,a)=d*e^r, (c,b), a^p=e^y1, b^p=e^y2, c^p=e^y3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print y1,y2,y3;
end if;

end for;
end for;
end for;

gtotal:=gtotal+count;
//print count,3+(p+1)*Gcd(p-1,3);

/*
Descendants of 6.150

Case 8: baaa=baab, babb=xbaaa, ca-baa=cb=0 (2<=x<p)
*/

count:=0;

for x in [2..p-1] do

for y1 in [0..p-1] do
for y2 in [0..p-1] do
range:=[0,1,lns];
if y1+y2 gt 0 then range:=[0]; end if;
for y3 in range do

A:=H31![y1,y2,y3];

if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,a),(b,a,a,b)=e, (b,a,b,b)=e^x, 
                                  (c,a)=d*e^-1, (c,b), a^p, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print 0,0,0;
  continue;
end if;

new:=1;
index:=p^2*y1+p*y2+y3;

for a in [1..p-1] do
//for c in [0..p-1] do
//for e in [0..p-1] do
c:=0; e:=0;

B:=H33![a,0,c,
        0,a,e,
        0,0,a^2];

C:=F!(a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

B:=H33![0,a,c,
        x*a,0,e,
        0,0,-x*a^2];

C:=F!(x^2*a^4);

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[2][1]);
z3:=Z!(D[3][1]);

ind1:=p^2*z1+p*z2+z3;

if ind1 lt index then new:=0; break; end if;

end for;
//if new eq 0 then break; end if;
//end for;
//if new eq 0 then break; end if;
//end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(b,a,a),e=(d,a),(b,a,a,b)=e, (b,a,b,b)=e^x, 
                       (c,a)=d*e^-1, (c,b), a^p=e^y1, b^p=e^y2, c^p=e^y3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  //print y1,y2,y3;
end if;

end for;
end for;
end for;

end for;

gtotal:=gtotal+count;
//print count,(5*p-7+(p^2-5)*Gcd(p-1,3)-Gcd(p-1,4))/2;

vprint Orderp7, 1: "Group 6.150 has",gtotal,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 4p + 14 + (p^2+4p+13)gcd(p-1,3)/2 + gcd(p-1,4) =",
4*p+14+(p^2+4*p+13)*Gcd(p-1,3)/2+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
