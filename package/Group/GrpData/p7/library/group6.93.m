freeze;

import "misc.m": ProcessPresentation; 

Group6_93 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.93 valid only for p>3"; return false; end if;

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

r:=(p-1) div 2;
w2:=w^2 mod p;
w3:=w^3 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d|d=(c,a),(b,a,a), (b,a,b), (c,a,a), (c,b), b^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a),e=a^p,(b,a,a), (b,a,b), (c,a,a), (c,b)=e^p, b^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=e^p,(b,a,a), (b,a,b), (c,a,a), (c,b)=f^w, b^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(c,a,a),(b,a,a), (b,a,b), e^p, (c,b), b^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(c,a,a),(b,a,a), (b,a,b), e^p=f, (c,b), b^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e|d=(c,a),e=a^p,(b,a,a), (c,a,a), e^p, (c,b), b^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a),e=a^p,(b,a,a), (c,a,a), e^p, (c,b), b^p=d, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,b),(b,a,a), (c,a,a), e^p, (c,b), b^p=d*f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a),e=a^p,(b,a,a), (c,a,a), e^p=(b,a,b), (c,b), b^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a),e=a^p,(b,a,a), (c,a,a), e^p=(b,a,b)^w, (c,b), b^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(c,a),(b,a,a),e=a^p,f=(b,a,b),(c,a,a)=f,e^p=f^x,(c,b),b^p=d*f^r,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|d=(c,a),(b,a,a),e=a^p,f=(b,a,b),(c,a,a)=f,e^p=f^-1,(c,b),b^p=d*f^r,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),(b,a,a),e=a^p,f=(b,a,b),(c,a,a)=f,e^p=f^-1,(c,b),b^p=d*f^r,c^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=p+12;

GR:=Group<a,b,c,d,e|d=(c,a),e=a^p,(b,a,b),(c,a,a),e^p,(c,b),b^p=d,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p,(c,b),b^p=d,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p,(c,b),b^p=d,c^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p,(c,b),b^p=d,c^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p,(c,b)=f,b^p=d,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p,(c,b)=f,b^p=d,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p,(c,b)=f,b^p=d,c^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p,(c,b)=f,b^p=d,c^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p=f,(c,b),b^p=d,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p=f,(c,b)=f,b^p=d,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p=f,(c,b)=f^w,b^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p=f,(c,b)=f^w2,b^p=d,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=a^p,f=(b,a,a),(b,a,b),(c,a,a),e^p=f,(c,b)=f^w3,b^p=d,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.93 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p + 15 + 2gcd(p-1,3) + gcd(p-1,4) =",
p+15+2*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
