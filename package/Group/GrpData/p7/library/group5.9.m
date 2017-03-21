freeze;

import "misc.m": ProcessPresentation; 

Group5_9 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "5.9 valid only for p>3"; return false; end if;

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

w2:=w^2;
w3:=w^3;

L:=[]; Nmr := 0;
GR:=Group<a,b,c | (b,a,a), (c,a), (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,g | g=(b,a,b), (b,a,a), (c,a)=g, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p, e=d^p, (b,a,a), (c,a)=e, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a),(c,a)=g*e, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^w*e, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p,e=d^p,(b,a,a), (c,a), (c,b)=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g, (c,b)=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p,e=d^p,(b,a,a), (c,a)=e, (c,b)=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g*e, (c,b)=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^w*e, (c,b)=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (c,a), (c,b), b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (c,a)=(b,a,b), (c,b), b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=e, (c,b), b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g*e, (c,b), b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^w*e, (c,b), b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a), (c,b)=e, b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g, (c,b)=e, b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=17;
if p mod 3 ne 1 then
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^x*e, (c,b)=e, b^p, c^p=g>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
else;
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [0..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      count:=count+1;
      GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^x*e, (c,b)=e, b^p, c^p=g>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+1;
      GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^x*e, (c,b)=e^w, b^p, c^p=g>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+1;
      GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^x*e, (c,b)=e^w2, b^p, c^p=g>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end if;
  end for;
  GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a), (c,b)=e^w, b^p, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g, (c,b)=e^w, b^p, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a), (c,b)=e^w2, b^p, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g, (c,b)=e^w2, b^p, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end if;
GR:=Group<a,b,c | (b,a,a), (c,a), (c,b), b^p=(b,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,g | g=(b,a,b), (b,a,a), (c,a)=g, (c,b), b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=e, (c,b), b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g*e, (c,b), b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^w*e, (c,b), b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a), (c,b)=e, b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g, (c,b)=e, b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^w, (c,b)=e, b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+8;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^w2, (c,b)=e, b^p=g, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^w3, (c,b)=e, b^p=g, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^x*e, (c,b)=e, b^p=g, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,g | d=a^p,e=d^p,g=(b,a,b),(b,a,a), (c,a)=g^x*e^w, (c,b)=e, b^p=g, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
//print count,3*p+20+3*Gcd(p-1,3)+Gcd(p-1,4);
count1:=count;
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p,e=d^p,(b,a,b), (c,a)=e, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b)=(b,a,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e, (c,b)=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e^w, (c,b)=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p,e=d^p,(b,a,b), (c,a), (c,b)=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f*e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b), b^p, c^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e, (c,b), b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,f | f=(b,a,a), (b,a,b), (c,a), (c,b)=f, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e, (c,b)=f, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e^w, (c,b)=f, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=e, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f*e, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b), b^p=(b,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e, (c,b), b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+16;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e^x, (c,b)=f, b^p=f, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=e, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f*e, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a), (c,b), b^p=(b,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e, (c,b), b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a)=e^x, (c,b)=f, b^p=f^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=e, b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p,e=d^p,f=(b,a,a),(b,a,b), (c,a), (c,b)=f*e, b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
//print count-count1,2*p+22;
count1:=count;
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p=(b,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p=(b,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p=(b,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p, c^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p=(b,a,b), c^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p=(b,a,a), c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b), b^p=(b,a,a)^w, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b)=(b,a,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b)=(b,a,b), b^p=(b,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b)=(b,a,b), b^p=(b,a,a)^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | d=a^p, d^p, (c,a), (c,b)=(b,a,b), b^p=(b,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=g, b^p=f*g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=g, b^p=f^w*g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=g, b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=g, b^p=f, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=g, b^p=f^w, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=g, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=g, b^p=g, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+20;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=g, b^p=g^x, c^p=f*g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=f*g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=f^w*g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=f, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=f^w, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+9;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=f^w2, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=f^w3, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=g, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f, b^p=g^x, c^p=f*g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f*g, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f*g, b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f*g, b^p=g^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
for y in [1..((p+1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f*g, b^p=f*g^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for y in [0..p-1] do
  y1:=(p+w-y) mod p;
  if y le y1 then
    count:=count+1;
    GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f*g, b^p=f^w*g^y, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end if;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f*g, b^p=f^x, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  for y in [1..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f*g, b^p=g^x, c^p=f*g^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end for;
z:=(p+1) div 2;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a), (c,b)=f*g, b^p=g^x, c^p=f*g^z>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p=g, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p=g^w, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p=g^w2, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b), b^p=f^x, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b)=f^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b)=f^w, b^p=g, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b)=f^w, b^p=g^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
for y in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b)=f^w, b^p=f*g^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b)=f^w, b^p=f^w*g^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b)=f^w, b^p=f^x, c^p=g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b)=f^w, b^p=g^x, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p, (c,a)=g, (c,b)=f^w, b^p=g^y, c^p=f^x*g>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
//print count-count1,p^2+7*p+39+2*Gcd(p-1,4)+Gcd(p-1,3);
count1:=count;
count:=count+1;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b), b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b), b^p=g^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=f, b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=f, b^p, c^p=g^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=f, b^p, c^p=g^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=f, b^p=g^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=g, b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=g, b^p=g^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for y in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=f*g, b^p, c^p=g^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=f*g, b^p=g^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for y in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=f^w*g, b^p, c^p=g^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a), (c,b)=f^w*g, b^p=g^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b), b^p, c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b), b^p=g^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
if p mod 4 eq 1 then
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [1..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=p-x1;
    if x le x1 and x le x2 then
      for y in [1,w,w2,w3] do
        count:=count+1;
        GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b)=f^y, b^p, c^p=g^x>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      end for;
    end if;
  end for;
  for x in [0..p-1] do
    for y in [1,w,w2,w3] do
      count:=count+1;
      GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b)=f^y, b^p=g^x, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
  end for;
else;
  for x in [1..((p-1) div 2)] do
  for y in [1,w] do
    count:=count+1;
    GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b)=f^y, b^p, c^p=g^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  end for;
  for x in [0..p-1] do
    for y in [1,w] do
      count:=count+1;
      GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b)=f^y, b^p=g^x, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
  end for;
end if;
for x in [0..p-1] do
  for y in [1..((p-1) div 2)] do
    GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b)=f^x*g, b^p, c^p=g^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b)=f^x*g^w, b^p, c^p=g^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
end for;
  for y in [0..p-1] do
    GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b)=f^x*g, b^p=g^y, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=f, (c,a)=g, (c,b)=f^x*g^w, b^p=g^y, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
end for;
//print count-count1,3*p^2+7*p+1+Gcd(p-1,3)+p*Gcd(p-1,4);
count1:=count;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a), (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a), (c,b), b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a), (c,b), b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a), (c,b), b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=f, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=f, (c,b), b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=f, (c,b), b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=f, (c,b), b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g, (c,b), b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g, (c,b), b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g, (c,b), b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+12;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g, (c,b), b^p, c^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a), (c,b)=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a), (c,b)=f, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a), (c,b)=f, b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a), (c,b)=f, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g, (c,b)=f, b^p=f^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g, (c,b)=f, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g^w, (c,b)=f, b^p=f^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g, (c,a)=g^w, (c,b)=f, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
//print count-count1,(7*p+25+Gcd(p-1,4))/2;
count1:=count;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a), (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a), (c,b), b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a), (c,b), b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a), (c,b), b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=f, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=f, (c,b), b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=f, (c,b), b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=f, (c,b), b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g, (c,b), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g, (c,b), b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g, (c,b), b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g, (c,b), b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+12;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g, (c,b), b^p, c^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a), (c,b)=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a), (c,b)=f, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a), (c,b)=f, b^p=f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a), (c,b)=f, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g, (c,b)=f, b^p=f^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g, (c,b)=f, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g^w, (c,b)=f, b^p=f^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f,g | f=(b,a,a), g=(b,a,b), d=a^p, d^p=g^w, (c,a)=g^w, (c,b)=f, b^p, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
//print count-count1,(7*p+25+Gcd(p-1,4))/2;

vprint Orderp7, 1: "Group 5.9 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 4p^2 + 26p + 107 + 5gcd(p-1,3) + (p+4)gcd(p-1,4) =",
4*p^2+26*p+107+5*Gcd(p-1,3)+(p+4)*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;

Children26 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_9 (p: Process:=Process, Select:=Select);
end function;

