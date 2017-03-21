freeze;

import "misc.m": ProcessPresentation; 

Group6_113 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.113 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (b,a,b), (c,a,c), a^p=(b,a), b^p=(c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a,c), a^p=(b,a), b^p=(c,b), c^p=(c,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (b,a,b), (c,a,c), a^p=(b,a), b^p=(c,b), c^p=(c,a,a)^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
for x in [0..p-1] do
  GR:=Group<a,b,c,e,f | e=(c,b),f=(c,a,a),(b,a,b), (c,a,c), a^p=(b,a), b^p=e*f, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,e,f | e=(c,b),f=(c,a,a),(b,a,b), (c,a,c), a^p=(b,a), b^p=e*f^w, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f | d=(b,a),f=(c,a,c),(b,a,b), (c,a,a), a^p=d*f^x, b^p=(c,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,f | d=(b,a),f=(c,a,c),(b,a,b), (c,a,a), a^p=d*f^x, b^p=(c,b), c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
count:=count+1;
GR:=Group<a,b,c,d,f | d=(b,a),f=(d,b),(c,a,a), (c,a,c), a^p=d*f^r, b^p=(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,f | d=(b,a),f=(d,b),(c,a,a), (c,a,c)=f^x, a^p=d*f^r, b^p=(c,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,f | d=(b,a),f=(d,b),(c,a,a)=f, (c,a,c)=f^-2, 
                          a^p=d*f^r, b^p=(c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.113 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 5p + 4 =",5*p+4;

if Process then return Nmr; else return L; end if;

end function;
