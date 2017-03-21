freeze;

import "misc.m": ProcessPresentation; 

Group6_276 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.276 valid only for p>3"; return false; end if;
 
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

GR:=Group<a,b,c,d,e | d=(c,a,a),e=(d,a),(c,b), (c,a,c), a^p=(b,a), b^p, 
                      c^p=d^w*e^-w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.276 has 1 descendant of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 1";

if Process then return Nmr; else return L; end if;

end function;
