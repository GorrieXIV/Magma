freeze;

import "misc.m": ProcessPresentation; 

Group6_281 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.281 valid only for p>3"; return false; end if;
 
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

GR:=Group<a,b,c | (c,b), (c,a,a), a^p, b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b), (c,a,a), a^p=(c,a,c,c), b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c | (c,b), (c,a,a), a^p=(c,a,c,c)^w, b^p=(b,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (c,a,a), a^p=(c,a,c,c)^w2, b^p=(b,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=4;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c | (c,b), (c,a,a), a^p=(c,a,c,c)^x, b^p=(b,a), 
                              c^p=(c,a,c,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (c,a,a), a^p=(c,a,c,c)^x, b^p=(b,a), 
                              c^p=(c,a,c,c)^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  for y in [0..p-1] do
    GR:=Group<a,b,c | (c,b), (c,a,a)=(c,a,c,c), a^p=(c,a,c,c)^x, 
                                b^p=(b,a), c^p=(c,a,c,c)^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c | (c,b), (c,a,a)=(c,a,c,c)^w, a^p=(c,a,c,c)^x, 
                                b^p=(b,a), c^p=(c,a,c,c)^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
end for;
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c,c),(c,b), (c,a,a), a^p, b^p=d*e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c,c),(c,b), (c,a,a), a^p=e, 
                            b^p=d*e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c,c),(c,b), (c,a,a), a^p=e^w, 
                              b^p=d*e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c,c),(c,b), (c,a,a), a^p=e^w2, 
                              b^p=d*e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c,c),(c,b), (c,a,a), a^p=e^x, 
                              b^p=d*e, c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c,c),(c,b), (c,a,a), a^p=e^x, 
                              b^p=d*e, c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  for y in [0..p-1] do
    GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c,c),(c,b), (c,a,a)=e, a^p=e^x, 
                                b^p=d*e, c^p=e^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e | d=(b,a),e=(c,a,c,c),(c,b), (c,a,a)=e^w, a^p=e^x, 
                                b^p=d*e, c^p=e^y>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
end for;

vprint Orderp7, 1: "Group 6.281 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2p^2 + 4p + 4 + 2gcd(p-1,3) =",
2*p^2+4*p+4+2*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
