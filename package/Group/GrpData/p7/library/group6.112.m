freeze;

import "misc.m": ProcessPresentation; 

Group6_112 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.112 valid only for p>3"; return false; end if;

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
s:=(p+1) div 2;
w2:=w^2 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (b,a,b), (c,b,b), a^p=(b,a), b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,b,c),(b,a,b), (c,b,b), a^p=d*e, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a),e=(c,b,c),(b,a,b), (c,b,b), a^p=d*e^w, b^p=(c,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a),e=(c,b,c),(b,a,b), (c,b,b), a^p=d*e^w2, b^p=(c,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=4;
end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e | d=(b,a),e=(c,b,c),(b,a,b), (c,b,b), a^p=d*e^x, b^p=(c,a), c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,b), (c,b,c), a^p=(b,a), b^p=(c,a), c^p=(c,b,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(c,a),e=(c,b,b),(b,a,b), (c,b,c), a^p=(b,a), b^p=d*e, c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
end for;
for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | d=(c,a),e=(c,b,b),(b,a,b), (c,b,c)=e, a^p=(b,a), 
                            b^p=d*e^x, c^p=e^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a),f=(d,b),(c,b,b), (c,b,c), a^p=d*f^r, 
                            b^p=e*f^s, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a),f=(d,b),(c,b,b), (c,b,c)=f, a^p=d*f^r, 
                            b^p=e*f^s, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a),f=(d,b),(c,b,b), (c,b,c)=f^w, a^p=d*f^r, 
                              b^p=e*f^s, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a),f=(d,b),(c,b,b), (c,b,c)=f^w2, a^p=d*f^r, 
                              b^p=e*f^s, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a),f=(d,b),(c,b,b)=f, (c,b,c)=f^x, 
                              a^p=d*f^r, b^p=e*f^s, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a),f=(d,b),(c,b,b)=f^w, (c,b,c)=f^x, 
                              a^p=d*f^r, b^p=e*f^s, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.112 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p^2 + 4p + 3 + 2gcd(p-1,3) =",
p^2+4*p+3+2*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
