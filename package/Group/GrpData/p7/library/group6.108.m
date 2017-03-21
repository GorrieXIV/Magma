freeze;

import "misc.m": ProcessPresentation; 

Group6_108 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.108 valid only for p>3"; return false; end if;

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
r:=(p-1) div 2;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (b,a,a), (b,a,b), a^p=(c,a), b^p=(c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,c), a^p=(c,a), b^p=(c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(c,a),e=(b,a,b),(b,a,a), (b,a,c), a^p=d*e, b^p=(c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(c,a),e=(b,a,b),(b,a,a), (b,a,c), a^p=d*e^w, b^p=(c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,c), a^p=(c,a), b^p=(c,b), c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (b,a,c)=(b,a,b), a^p=(c,a), b^p=(c,b)^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=6;
for x in [2..p-2] do
  y:=(F!x)^-1; y:=Integers()!y;
  if x gt y then continue; end if;
  GR:=Group<a,b,c | (b,a,a), (b,a,b), a^p=(c,a), b^p=(c,b)^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a), (b,a,c), a^p=(c,a), b^p=(c,b)^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(c,a),e=(b,a,b),(b,a,a), (b,a,c), a^p=d*e, b^p=(c,b)^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(c,a),e=(b,a,b),(b,a,a), (b,a,c), a^p=d*e^w, b^p=(c,b)^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,a), (b,a,c), a^p=(c,a), b^p=(c,b)^x, c^p=(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,b), (b,a,c), a^p=(c,a), b^p=(c,b)^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(c,b),e=(b,a,a),(b,a,b), (b,a,c), a^p=(c,a), b^p=d^x*e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(c,b),e=(b,a,a),(b,a,b), (b,a,c), a^p=(c,a), b^p=d^x*e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,b), (b,a,c), a^p=(c,a), b^p=(c,b)^x, c^p=(b,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,b)=(b,a,a), (b,a,c), a^p=(c,a), b^p=(c,b)^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(c,b),e=(b,a,a),(b,a,b)=e, (b,a,c), a^p=(c,a), b^p=d^x*e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(c,b),e=(b,a,a),(b,a,b)=e, (b,a,c), a^p=(c,a), b^p=d^x*e^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,b)=(b,a,a), (b,a,c), a^p=(c,a), b^p=(c,b)^x, c^p=(b,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+13;
  if p mod 3 eq 1 then
    GR:=Group<a,b,c | (b,a,b)=(b,a,a), (b,a,c), a^p=(c,a), b^p=(c,b)^x, c^p=(b,a,a)^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c | (b,a,b)=(b,a,a), (b,a,c), a^p=(c,a), b^p=(c,b)^x, c^p=(b,a,a)^w2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
GR:=Group<a,b,c | (b,a,a), (b,a,b), a^p=(c,a), b^p=(c,b)^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (c,a,b), a^p=(c,a), b^p=(c,b)^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(c,a),e=(b,a,b),(b,a,a), (c,a,b), a^p=d*e, b^p=(c,b)^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(c,a),e=(b,a,b),(b,a,a), (c,a,b), a^p=d*e^w, b^p=(c,b)^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,a), (c,a,b), a^p=(c,a), b^p=(c,b)^-1, c^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b)=(b,a,a), (c,a,b), a^p=(c,a), b^p=(c,b)^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b)=(b,a,a), (c,a,b), a^p=(c,a), 
                             b^p*(c,b)=(b,a,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+7;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c | (b,a,b)=(b,a,a), (c,a,b), a^p=(c,a), 
                            b^p*(c,b)=(b,a,a)^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
GR:=Group<a,b,c | (b,a,b)=(b,a,a), (c,a,b), a^p=(c,a), b^p=(c,b)^-1, 
                             c^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+1;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (b,a,b)=(b,a,a), (c,a,b), a^p=(c,a), b^p=(c,b)^-1, 
                              c^p=(b,a,a)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (b,a,b)=(b,a,a), (c,a,b), a^p=(c,a), b^p=(c,b)^-1, 
                              c^p=(b,a,a)^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.108 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is (p-1)(12 + gcd(p-1,3))/2 + gcd(p-1,4)/2 =",
(p-1)*(12+Gcd(p-1,3))/2+Gcd(p-1,4)/2;

if Process then return Nmr; else return L; end if;

end function;
