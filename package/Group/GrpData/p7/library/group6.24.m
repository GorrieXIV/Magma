freeze;

import "misc.m": ProcessPresentation; 

Group6_24 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.24 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d,e,f,g|e=(b,a),f=(c,a),g=(e,b),(c,b),(d,a),(d,b),(d,c),a^p=e*g^r,
b^p=f*g^s,c^p,d^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a),f=(c,a),g=(e,b),(c,b),(d,a),(d,b),(d,c),a^p=e*g^r,
b^p=f*g^s,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a),f=(c,a),g=(e,b),(c,b),(d,a),(d,b),(d,c),a^p=e*g^r,
b^p=f*g^s,c^p=g,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a),f=(c,a),g=(e,b),(c,b),(d,a),(d,b),(d,c),a^p=e*g^r,
b^p=f*g^s,c^p*(b,a,b)^-w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|e=(b,a),f=(c,a),g=(e,b),(c,b),(d,a),(d,b),(d,c)=g,
a^p=e*g^r,b^p=f*g^s,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.24 has 5 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 5";

if Process then return Nmr; else return L; end if;

end function;
