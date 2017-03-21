freeze;

import "misc.m": ProcessPresentation; 

Group6_89 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.89 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=b^p,f=c^p,g=(d,b),e^p,f^p,(c,a),(c,b),a^p=d*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,f | f=c^p,(b,a,b), f^p, (c,a), (c,b), a^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e,f | e=b^p,f=c^p,(b,a,b), f^p, (c,a), (c,b)=e^p, a^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e,f | e=b^p,f=c^p,(b,a,b), f^p, (c,a)=e^p, (c,b), a^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,e,f,g | e=b^p,f=c^p,g=f^p,(b,a,b), e^p, (c,a), (c,b)=g^x, a^p=(b,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,e,f | e=b^p,f=c^p,(b,a,b), e^p, (c,a)=f^p, (c,b), a^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f,g | d=(b,a),e=b^p,f=c^p,g=(d,b),e^p, f^p=g, (c,a), (c,b), a^p=d*g^r>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;

vprint Orderp7, 1: "Group 6.89 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p + 6 =",p+6;

if Process then return Nmr; else return L; end if;

end function;
