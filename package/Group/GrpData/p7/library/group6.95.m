freeze;

import "misc.m": ProcessPresentation; 

Group6_95 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.95 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d | d=(c,a),(b,a,a), (b,a,b), (c,b), a^p, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(c,a),e=b^p,(b,a,a), (b,a,b), (c,b)=e^p, a^p, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e | d=(c,a),e=b^p,(b,a,a), e^p, (c,b), a^p, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,b),(b,a,a), e^p, (c,b), a^p=f, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,b),(b,a,a), e^p, (c,b), a^p=f^w, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,b),(b,a,a), e^p, (c,b), a^p, c^p=d*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,b),(b,a,a), e^p, (c,b), a^p=f,c^p=d*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,b),(b,a,a), e^p, (c,b), a^p=f^w,c^p=d*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,b),(b,a,a), e^p=f, (c,b), a^p, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=9;

for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), e^p=f^x, (c,b), a^p, c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), e^p=f^x, (c,b)=f, a^p,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), e^p, (c,b), a^p=f, c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b), e^p, (c,b)=f, a^p=f,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, e^p=f^x, (c,b), a^p,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, e^p, (c,b), a^p=f^x,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=b^p,f=(b,a,a),(b,a,b)=f, e^p, (c,b), a^p=f^x,c^p=d*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.95 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 5p + 10 =",5*p+10;

if Process then return Nmr; else return L; end if;

end function;
