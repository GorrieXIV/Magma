freeze;

import "misc.m": ProcessPresentation; 

Group6_371 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.371 is valid only for p>3"; return false; end if;

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

w2:=w^2 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c | c=a^p,(b,a,a,a), c^p, b^p=(b,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(b,a,b,b),(b,a,a,a), c^p, b^p=d^w*e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(b,a,b,b),(b,a,a,a), c^p, b^p=d^w*e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
count:=count+1;
GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(b,a,b,b),(b,a,a,a), c^p=e, b^p=d^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(b,a,b,b),(b,a,a,a), c^p=e^w, b^p=d^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(b,a,b,b),(b,a,a,a), c^p=e^w2, b^p=d^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(d,a),(b,a,b,b), c^p, b^p=d^w*e^(x-w)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(d,a),(b,a,b,b), c^p=e, b^p=d^w*e^-w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(d,a),(b,a,b,b)=e, c^p, b^p=d^w*e^(x-w)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(d,a),(b,a,b,b)=e, c^p=e^x, b^p=d^w*e^-w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(d,a),(b,a,b,b)=e^w, c^p, b^p=d^w*e^(x-w)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e | c=a^p,d=(b,a,a),e=(d,a),(b,a,b,b)=e^w, c^p=e^x, b^p=d^w*e^-w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.371 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2p + 2 + (p+1)/2 + gcd(p-1,3) + gcd(p-1,4)/2 =",
2*p+2+(p+1)/2+Gcd(p-1,3)+Gcd(p-1,4)/2;

if Process then return Nmr; else return L; end if;

end function;
