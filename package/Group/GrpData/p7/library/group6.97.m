freeze;

import "misc.m": ProcessPresentation; 

Group6_97 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.97 valid only for p>3"; return false; end if;

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

w2:=w^2 mod p;

L:=[]; Nmr := 0;

for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f | d=(c,a),e=b^p,f=e^p,(b,a,a),(b,a,b),(b,a,c),(c,b)=f^x,a^p=d,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | d=(c,a),e=b^p,(b,a,a), (b,a,b), e^p, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(c,a),e=b^p,(b,a,a), (b,a,b), e^p=(b,a,c), (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e | d=(c,a),e=b^p,(b,a,a), (b,a,c), e^p, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(c,a),e=b^p,f=(b,a,b),(b,a,a), (b,a,c), e^p, (c,b), a^p=d*f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(c,a),e=b^p,f=(b,a,b),(b,a,a), (b,a,c), e^p, (c,b), a^p=d*f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(c,a),e=b^p,f=(b,a,b),(b,a,a), (b,a,c), e^p, (c,b), a^p=d, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(c,a),e=b^p,f=(b,a,b),(b,a,a), (b,a,c), e^p=f, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), (b,a,c), e^p, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), (b,a,c), e^p, (c,b)=f, a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), (b,a,c), e^p, (c,b)=f^w, a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), (b,a,c), e^p, (c,b), a^p=d, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), (b,a,c), e^p, (c,b)=f, a^p=d, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), (b,a,c), e^p, (c,b)=f^w, a^p=d, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=p+13;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), (b,a,c), e^p=f, (c,b)=f^x, a^p=d, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), (b,a,c), e^p=f^w, (c,b)=f^x, a^p=d, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, (b,a,c), e^p, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, (b,a,c), e^p, (c,b), a^p=d*f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, (b,a,c), e^p, (c,b), a^p=d*f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, (b,a,c), e^p, (c,b), a^p=d, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, (b,a,c), e^p, (c,b), a^p=d, c^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, (b,a,c), e^p, (c,b), a^p=d, c^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, (b,a,c), e^p=f, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, (b,a,c), e^p=f^w, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;

vprint Orderp7, 1: "Group 6.97 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 3p + 18 + gcd(p-1,3) =",
3*p+18+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
