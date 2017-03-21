freeze;

import "misc.m": ProcessPresentation; 

Group6_215 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.215 valid only for p>3"; return false; end if;
 
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

r:=(p-1) div 2;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=a^p,f=e^p,g=f^p,(c,a)=f,(c,b),b^p,c^p=d*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=a^p,f=e^p,g=f^p,(c,a)*f^-1,(c,b)=g,b^p,c^p=d*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=a^p,f=e^p,g=f^p,(c,a)*f^-1,(c,b)=g^w,b^p, 
                         c^p=d*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.215 has 3 descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 3";

if Process then return Nmr; else return L; end if;

end function;
