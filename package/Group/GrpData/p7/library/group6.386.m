freeze;

import "misc.m": ProcessPresentation; 

Group6_386 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.386 is valid only for p>3"; return false; end if;

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
GR:=Group<a,b,c | c=b^p,(b,a,a), (b,a,b), (b,a)^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | c=a^p,d=c^p,e=b^p,(b,a,a)=d^p, (b,a,b), (b,a)^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | c=a^p,d=c^p,e=b^p,(b,a,a), (b,a,b)=d^p, (b,a)^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | c=a^p,d=c^p,e=b^p,f=d^p,(b,a,a), (b,a,b)=f^w, (b,a)^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f | c=a^p,d=c^p,e=b^p,f=d^p,(b,a,a), (b,a,b)=f^x, (b,a)^p=f, e^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e | c=a^p,d=c^p,e=b^p,(b,a,a)=d^p, (b,a,b), (b,a)^p=d^p, e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.386 has",p+5,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p+5 =",p+5;

if Process then return Nmr; else return L; end if;

end function;
