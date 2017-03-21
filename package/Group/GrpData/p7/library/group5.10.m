freeze;

import "misc.m": ProcessPresentation; 

Group5_10 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "5.10 valid only for p>3"; return false; end if;

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

r:=(p+1) div 2;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e | d=(b,a), e=(d,a), (c,a), (c,b), b^p=d*e^-r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a), e=(d,a), (c,a)=e, (c,b), b^p=d*e^-r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a), e=(d,a), f=a^p, (c,a)=f^p, (c,b), b^p=d*e^-r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f,g | d=(b,a), e=(d,a), f=a^p, g=f^p, (c,a)=g^x, (c,b)=e, b^p=d*e^-r, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f,g | d=(b,a), e=(d,a), f=a^p, g=f^p, (c,a)=e*g, (c,b)=e, b^p=d*e^-r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=p+4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g | d=(b,a), e=(d,a), f=a^p, g=f^p, (c,a)=e^x*g, (c,b)=g, b^p=d*e^-r, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f | d=(b,a), e=(d,a), f=a^p, (c,a), (c,b)=f^p, b^p=d*e^-r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a), e=(d,a), f=a^p, (c,a)=e,(c,b)=f^p, b^p=d*e^-r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a), e=(d,a), f=a^p, (c,a)=e^w,(c,b)=f^p, b^p=d*e^-r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;

vprint Orderp7, 1: "Group 5.10 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 2p+7 =",2*p+7;

if Process then return Nmr; else return L; end if;

end function;

Children27 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_10 (p: Process:=Process, Select:=Select);
end function;

