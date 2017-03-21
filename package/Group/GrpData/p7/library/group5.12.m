freeze;

import "misc.m": ProcessPresentation; 

Group5_12 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "5.12 valid only for p>3"; return false; end if;

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
for x in [0..p-1] do
  y:=x^2 mod p;
  Include(~SQ,y);
end for;

w2:=w^2 mod p;

Z:=Integers();
V2:=VectorSpace(F,2);
H22:=Hom(V2,V2);

//ca=bab, cb=baa
mats1:=[];

for y1 in [0..p-1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

A:=H22![y1,y2,y3,y4];
if A eq 0 then Append(~mats1,[0,0,0,0]); continue; end if;

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

for a in [0..p-1] do
for b in [0..p-1] do

e:=F!(a^2-b^2);
if e eq 0 then continue; end if;

P:=H22![a,b,b,a];

D:=e^-1*P*A*P^-1;

z1:=Z!(D[1,1]);
z2:=Z!(D[1,2]);
z3:=Z!(D[2,1]);
z4:=Z!(D[2,2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then
  new:=0;
end if;

P:=H22![a,b,-b,-a];

D:=-e^-1*P*A*P^-1;

z1:=Z!(D[1,1]);
z2:=Z!(D[1,2]);
z3:=Z!(D[2,1]);
z4:=Z!(D[2,2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then
  new:=0;
end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then 
  Append(~mats1,[y1,y2,y3,y4]);
end if;

end for;
end for;
end for;
end for;

//print #mats1,p^2+(7*p+15)/2;

//ca=wbab, cb=baa
mats2:=[];

for y1 in [0..p-1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

A:=H22![y1,y2,y3,y4];
if A eq 0 then Append(~mats2,[0,0,0,0]); continue; end if;

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

for a in [0..p-1] do
for b in [0..p-1] do

e:=F!(a^2-w*b^2);
if e eq 0 then continue; end if;

P:=H22![a,w*b,b,a];

D:=e^-1*P*A*P^-1;

z1:=Z!(D[1,1]);
z2:=Z!(D[1,2]);
z3:=Z!(D[2,1]);
z4:=Z!(D[2,2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then
  new:=0;
end if;

P:=H22![a,w*b,-b,-a];

D:=-e^-1*P*A*P^-1;

z1:=Z!(D[1,1]);
z2:=Z!(D[1,2]);
z3:=Z!(D[2,1]);
z4:=Z!(D[2,2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then
  new:=0;
end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then 
  Append(~mats2,[y1,y2,y3,y4]);
end if;

end for;
end for;
end for;
end for;

//print #mats2,p^2+(3*p+5)/2;

L:=[]; Nmr := 0;
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b), a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b), a^p=(b,a,a), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b), a^p, b^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b), a^p, b^p=(b,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e | d=c^p,e=(b,a,a),(b,a,b),(c,a)=d^p,(c,b),a^p,b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d | d=c^p,(b,a,b), (c,a)=d^p, (c,b), a^p=(b,a,a), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b)=(b,a,a), a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b)=(b,a,a), a^p=(b,a,a), b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b)=(b,a,a), a^p, b^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b)=(b,a,a), a^p, b^p=(b,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=p+9;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=c^p,e=(b,a,a),(b,a,b),(c,a)=d^p,(c,b)=e,a^p,b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | d=c^p,e=(b,a,a),(b,a,b),(c,a)=d^p,(c,b)=e,a^p=e,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p,(b,a,b), (c,a), (c,b)=d^p, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p,(b,a,b), (c,a), (c,b)=d^p, a^p, b^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=c^p,(b,a,b), (c,a), (c,b)=d^p, a^p, b^p=(b,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=c^p,e=(b,a,a),(b,a,b), (c,a), (c,b)=d^p, a^p=e, b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f | d=c^p,e=(b,a,a),f=d^p,(b,a,b), (c,a), (c,b)=e*f, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=c^p,e=(b,a,a),f=d^p,(b,a,b),(c,a),(c,b)=e*f,a^p,b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=c^p,e=(b,a,a),f=d^p,(b,a,b),(c,a),(c,b)=e*f,a^p,b^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=c^p,e=(b,a,a),f=d^p,(b,a,b),(c,a), (c,b)=e*f, a^p=e,b^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
//print count,4*p+16;
count1:=count;
count:=count+1;
GR:=Group<a,b,c,d,e|d=c^p,e=(b,a,a),d^p, (c,a), (c,b), a^p=e, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [1..p-1] do
  x1:=(F!x)^-1; x1:=Z!x1;
  if x le x1 then
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b), a^p=e, b^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end if;
end for;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b), a^p=e*f, b^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b), a^p=e*f^w, b^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b), a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b), a^p=f, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b), a^p=f^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b), a^p=f^w, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
for x in [1..p-1] do
  if (1+4*x) mod p notin SQ then
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b), a^p=f^x, b^p=e*f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end if;
end for;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p, b^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p, b^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=e, b^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=e, b^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=e, b^p=e^w*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=f, b^p=e^x*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=f, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=f, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=f, b^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=f^w, b^p=e^x*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=f^w, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=f^w, b^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p, (c,a), (c,b)=e, a^p=f^w, b^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for M in mats1 do;
  x:=M[1]; y:=M[2]; z:=M[3]; t:=M[4];
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p,(c,a)=f,(c,b)=e,a^p=e^x*f^y,b^p=e^z*f^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for M in mats2 do;
  x:=M[1]; y:=M[2]; z:=M[3]; t:=M[4];
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p,(c,a)=f^w,(c,b)=e,a^p=e^x*f^y,b^p=e^z*f^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
//print count-count1,2*p^2+9*p+29;
count1:=count;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a), (c,b), a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a), (c,b)=e, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a), (c,b)=f, a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a)=f, (c,b), a^p, b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f,(c,b)=e,a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f,(c,b)=e^w,a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a), (c,b), a^p, b^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a), (c,b)=e, a^p, b^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a), (c,b)=f, a^p, b^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+9;
if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [0..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a)=f, (c,b)=e^x, a^p, b^p=f>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a)=f^w, (c,b)=e^x, a^p, b^p=f>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a)=f^w2, (c,b)=e^x, a^p, b^p=f>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+3;
    end if;
  end for;
else;
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a)=f, (c,b)=e^x, a^p, b^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a), (c,b)=e^x, a^p=f, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e, (c,a), (c,b)=e^x*f, a^p=f, b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
if p mod 4 eq 3 then
  for x in [0..p-1] do
  for y in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f,(c,b)=e^x*f^y,a^p=f,b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
else;
  for x in [0..((p-1) div 2)] do
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f,(c,b)=e^x,a^p=f,b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f^w,(c,b)=e^x,a^p=f,b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for y in [1..((p-1) div 2)] do
    y1:=(QU*y) mod p; y2:=p-y1;
    if y le y1 and y le y2 then
      for x in [0..p-1] do
        GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f,(c,b)=e^x*f^y,a^p=f,b^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f^w,(c,b)=e^x*f^y,a^p=f,b^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        count:=count+2;
      end for;
    end if;
  end for;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a),(c,b)=e^x,a^p=f^w,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a),(c,b)=e^x*f,a^p=f^w,b^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
if p mod 4 eq 3 then
  for x in [0..p-1] do
  for y in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f,(c,b)=e^x*f^y,a^p=f^w,b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
else;
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [0..((p-1) div 2)] do
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f,(c,b)=e^x,a^p=f^w,b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f^w,(c,b)=e^x,a^p=f^w,b^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
  for y in [1..((p-1) div 2)] do
    y1:=(QU*y) mod p; y2:=p-y1;
    if y le y1 and y le y2 then
      for x in [0..p-1] do
        GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f,(c,b)=e^x*f^y,a^p=f^w,b^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(b,a,b),d^p=e,(c,a)=f^w,(c,b)=e^x*f^y,a^p=f^w,b^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        count:=count+2;
      end for;
    end if;
  end for;
end if;

//print count-count1,p^2+4*p+8+Gcd(p-1,3)+Gcd(p-1,4);

vprint Orderp7, 1: "Group 5.12 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 3p^2 + 17p + 53 + gcd(p-1,3) + gcd(p-1,4) =",
3*p^2+17*p+53+Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;

Children29 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_12 (p: Process:=Process, Select:=Select);
end function;

