freeze;

import "misc.m": ProcessPresentation; 

Group6_289 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.289 valid only for p>3"; return false; end if;
 
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

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-1] do
  GR:=Group<a,b,c | (c,b), (c,a,c), a^p, b^p=(b,a), c^p=(c,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b), (c,a,c)=(c,a,a,a), a^p, b^p=(b,a), 
                              c^p=(c,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c), a^p, b^p=(b,a), 
                              c^p=(c,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c)=(c,a,a,a), a^p, 
                              b^p=(b,a), c^p=(c,a,a,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+4;
end for;
GR:=Group<a,b,c | (c,b), (c,a,c), a^p=(c,a,a,a), b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c), a^p=(c,a,a,a), 
                            b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [1..p-1] do
  GR:=Group<a,b,c | (c,b), (c,a,c)=(c,a,a,a), a^p=(c,a,a,a)^x, 
                              b^p=(b,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c | (c,b)=(c,a,a,a), (c,a,c)=(c,a,a,a), a^p=(c,a,a,a)^x,
                              b^p=(b,a), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.289 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 6p =",6*p;

if Process then return Nmr; else return L; end if;

end function;
