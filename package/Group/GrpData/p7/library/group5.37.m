freeze;

import "misc.m": ProcessPresentation; 

Group5_37 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "5.37 valid only for p>3"; return false; end if;

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

SQ:={};
for x in [0..p-1] do
  y:=F!x;
  Include(~SQ,y^2);
end for;
INV:={1};
for x in [2..p-1] do
  y:=F!x;
  y:=y^-1;
  z:=Integers()!y;
  if x le z then
    Include(~INV,x);
  end if;
end for;
L:=[]; Nmr := 0;
GR:=Group<a,b | (b,a,a), (b,a,b), (b,a)^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | c=b^p, (b,a,a), (b,a,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c | c=b^p, (b,a,a), (b,a,b), c^p=(b,a)^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
for x in [0..p-1] do
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p,e^p=f^x*g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p=f,e^p=f^x*g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p,e^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p=g,e^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p,e^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p=g,e^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p,e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p=f,e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p=g,e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=c^p,(c,b),d^p=f*g,e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=e^p,(c,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=e^p,(c,b),c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=e^p,(c,b),c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=e^p,(c,b),c^p=f,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=d^p,(c,b),c^p,e^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=d^p,(c,b),c^p,e^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=d^p,(c,b),c^p,e^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+15;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=d^p,(c,b),c^p=f,e^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=f,e^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in INV do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=f,e^p=g^x,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=f*g,e^p=g,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=f*g^w,e^p=g,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p,e^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=g,e^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=g^w,e^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=g^w,e^p=f,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+6;
for x in [1..p-1] do
if F!(1+4*x) notin SQ then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=g^x,e^p=f*g,c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end if;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=g,e^p=f^x,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=g^w,e^p=f^x,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
for x in [0..p-1] do
for y in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=g^y,e^p=f^x*g,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p,e^p=f^x,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=f,e^p=f^x*g,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p,e^p=g,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|c=(b,a),d=a^p,e=b^p,f=(c,a),g=(c,b),d^p=f,e^p=g^x,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 5.37 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p^2+8p+25 =",p^2+8*p+25;

if Process then return Nmr; else return L; end if;

end function;

Children5 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_37 (p: Process:=Process, Select:=Select);
end function;

