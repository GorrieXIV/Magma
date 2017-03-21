freeze;

import "misc.m": ProcessPresentation; 

Group6_87 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.87 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;

GR:=Group<a,b,c,e,f | e=a^p,f=b^p,e^p, f^p, (c,a), (c,b), c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=a^p,e^p, d^p, (c,a), (c,b), c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=a^p,f=b^p,e^p, d^p, (c,a), (c,b)=f^p, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=a^p,f=b^p,e^p, d^p, (c,a)=f^p, (c,b), c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=a^p,f=b^p,g=f^p,e^p, d^p, (c,a)=g^w, (c,b), c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.87 has 5 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 5";

if Process then return Nmr; else return L; end if;

end function;
