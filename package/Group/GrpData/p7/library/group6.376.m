freeze;

import "misc.m": ProcessPresentation; 

Group6_376 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.376 is valid only for p>3"; return false; end if;

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
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,f|c=a^p,d=(b,a,a),f=(d,a),c^p=(b,a,b)^w, b^p=d*f^(x-1)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|c=a^p,d=(b,a,a),e=(b,a,b),f=(d,a),c^p=e^w*f^x, b^p=d*f^-1>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.376 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p =",p;

if Process then return Nmr; else return L; end if;

end function;
