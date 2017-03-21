freeze;

import "misc.m": ProcessPresentation; 

Group6_18 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.18 valid only for p>3"; return false; end if;

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
for x in [0..p-1] do
GR:=Group<a,b,c,d,e,f,g | e=(b,a),f=a^p,g=f^p,(c,a), (c,b), (d,a)=g^x, (d,b), (d,c)=e, b^p,
c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f,g | e=(b,a),f=a^p,g=f^p,(c,a)=g, (c,b), (d,a), (d,b), (d,c)=e, b^p, 
c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | e=(b,a),f=a^p,g=f^p,(c,a), (c,b), (d,a), (d,b), (d,c)=e*g, b^p, 
c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | e=(b,a),f=a^p,g=f^p,(c,a), (c,b), (d,a), (d,b)=g, (d,c)=e, b^p, 
c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | e=(b,a),f=a^p,g=f^p,(c,a)=g, (c,b), (d,a), (d,b)=g, (d,c)=e,
b^p, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g | e=(b,a),f=a^p,g=f^p,(c,a)=g^w, (c,b), (d,a), (d,b)=g, 
(d,c)=e, b^p, c^p=e, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=p+5;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f,g | e=(b,a),f=a^p,g=f^p,(c,a),(c,b)=g,(d,a)=g^x,(d,b),
   (d,c)=e,b^p,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f,g | e=(b,a),f=a^p,g=f^p,(c,a),(c,b)=g^w,(d,a)=g^x,(d,b),
   (d,c)=e,b^p,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.18 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 3p+5 =",3*p+5;

if Process then return Nmr; else return L; end if;

end function;
