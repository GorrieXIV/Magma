freeze;

import "misc.m": ProcessPresentation; 

Group6_382 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.382 is valid only for p>3"; return false; end if;

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
GR:=Group<a,b | (b,a,a,a), (b,a,b), b^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d | c=a^p,d=c^p,(b,a,a,a), (b,a,b)=d^p, b^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | c=a^p,d=c^p,e=d^p,(b,a,a,a), (b,a,b)=e^w, b^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | c=a^p,d=c^p,e=(b,a,a),f=(e,a),d^p, (b,a,b), b^p=e*f^(x-1)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f | c=a^p,d=c^p,e=(b,a,a),f=(e,a),d^p, (b,a,b)=f, b^p=e*f^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | c=a^p,d=c^p,e=(b,a,a),f=(e,a),d^p=f, (b,a,b)=f^x, 
                         b^p=e*f^-1>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.382 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p + 5 + (p-1)/2 =",
p+5+(p-1)/2;

if Process then return Nmr; else return L; end if;

end function;
