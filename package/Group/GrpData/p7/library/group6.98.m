freeze;

import "misc.m": ProcessPresentation; 

Group6_98 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.98 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a),f=a^p,(b,a,a), (c,a,a), (c,b), b^p=d, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a),f=a^p,(b,a,a), (c,a,a), (c,b)=f^p, b^p=d, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(c,a,a),(b,a,a),f^p, (c,b), b^p=d, c^p=e*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(c,a,a),(b,a,a),f^p, (c,b), b^p=d*g,c^p=e*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=4;
for x in [2..p-2] do
  y:=(F!x)^-1; y:=Integers()!y;
  if x le y then
    z:=(r*x) mod p;
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a),f=a^p,(b,a,a), (c,a,a), (c,b), b^p=d, c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a),f=a^p,(b,a,a), (c,a,a), (c,b)=f^p, b^p=d, c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(c,a,a),(b,a,a),f^p, (c,b), b^p=d, c^p=e^x*g^z>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(b,a,a),(c,a,a),f^p,(c,b),b^p=d*g^r,c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(b,a,a),(c,a,a)=g,f^p,(c,b),b^p=d*g^r,c^p=e^x*g^z>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+5;
  end if;
end for;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a),f=a^p,(b,a,a), (c,a,a), (c,b), b^p=d, c^p=e^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a),f=a^p,(b,a,a), (c,a,a), (c,b)=f^p, b^p=d, c^p=e^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(c,a,a),(b,a,a),f^p,(c,b),b^p=d,c^p=e^-1*g^s>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=(c,a),f=a^p,g=(b,a,a),(c,a,a)=g,f^p,(c,b),b^p=d*g^r,c^p=e^-1*g^s>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;

vprint Orderp7, 1: "Group 6.98 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is (5p + 1)/2 =",(5*p+1)/2;

if Process then return Nmr; else return L; end if;

end function;
