freeze;

import "misc.m": ProcessPresentation; 

Group6_116 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.116 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=(c,b)^-1,g=(c,a,c),(b,a,b), a^p=d, b^p=e*g^r, 
                      c^p=f*g^s>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=(c,b)^-1,g=(c,a,c),(b,a,b), a^p=d*g, 
                      b^p=e*g^r, c^p=f*g^s>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=(c,b)^-1,g=(c,a,c),(b,a,b), a^p=d*g^w, 
                      b^p=e*g^r, c^p=f*g^s>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.116 has 3 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 3";

if Process then return Nmr; else return L; end if;

end function;
