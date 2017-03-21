freeze;

import "misc.m": ProcessPresentation; 

Group5_8 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "5.8 valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c,d,e | d=a^p, e=b^p, (b,a), (c,a)=d^p, (c,b)=e^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p, e=b^p, (b,a), (c,a)=e^p, (c,b)=d^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=a^p, e=b^p, f=e^p, (b,a), (c,a)=f^w, (c,b)=d^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g | d=a^p,e=b^p,f=d^p,g=e^p,(b,a),(c,a)=g^x,(c,b)=f*g,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | d=a^p, e=b^p, (b,a), (c,a), (c,b)=d^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p, e=b^p, (b,a)=e^p, (c,a), (c,b)=d^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p, e=b^p, (b,a), (c,a), (c,b)=e^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p, e=b^p, (b,a)=d^p, (c,a), (c,b)=e^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p, e=b^p, (b,a), (c,a), (c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=a^p, e=b^p, (b,a)=d^p, (c,a), (c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;

vprint Orderp7, 1: "Group 5.8 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p+8 =",p+8;

if Process then return Nmr; else return L; end if;

end function;

Children25 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_8 (p: Process:=Process, Select:=Select);
end function;
