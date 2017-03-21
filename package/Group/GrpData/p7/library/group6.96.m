freeze;

import "misc.m": ProcessPresentation; 

Group6_96 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.96 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c | (b,a,b), (c,a,a), (c,a,c), (c,b), a^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e | e=b^p,(b,a,b), (c,a,a), (c,a,c), (c,b)=e^p, a^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,e | e=b^p,(b,a,b), (c,a,a), e^p, (c,b), a^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(b,a,b), (c,a,a), e^p, (c,b), a^p=d*f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(b,a,b), (c,a,a), e^p, (c,b), a^p=d*f^w, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(b,a,b), (c,a,a), e^p, (c,b), a^p=d, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(b,a,b), (c,a,a), e^p, (c,b), a^p=d*f,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(b,a,b), (c,a,a), e^p, (c,b), a^p=d*f^w,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(b,a,b), (c,a,a), e^p=f, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(b,a,b), (c,a,c), e^p, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(b,a,b), (c,a,c), e^p, (c,b), a^p=d, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(b,a,b), (c,a,c), e^p, (c,b), a^p=d, c^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=12;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(b,a,b), (c,a,c), e^p, (c,b)=f, a^p=d, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(b,a,b), (c,a,c), e^p, (c,b)=f^w, a^p=d,c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(b,a,b), (c,a,c), e^p=f, (c,b), a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(b,a,b), (c,a,c), e^p=f, (c,b)=f, a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(b,a,b), (c,a,c), e^p=f, (c,b)=f^w,a^p=d, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,a), (c,a,c), e^p, (c,b), a^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,a), (c,a,c), e^p, (c,b), a^p=d*f^r,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,a), (c,a,c), e^p=f, (c,b), a^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,a), (c,a,c)=f^-1, e^p, (c,b), a^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,a), (c,a,c)=f^-1, e^p=f, (c,b),  a^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,a), (c,a,c)=f^-w, e^p, (c,b), a^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,a), (c,a,c)=f^-w, e^p=f, (c,b), a^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,c), (c,a,a)=f, e^p, (c,b), a^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,c), (c,a,a)=f, e^p, (c,b), a^p=d*f^r, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,c), (c,a,a)=f, e^p, (c,b), a^p=d*f^r, c^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(b,a,b),(c,a,c), (c,a,a)=f, e^p=f, (c,b), a^p=d*f^r, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+14;

vprint Orderp7, 1: "Group 6.96 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 2p + 26 =",2*p+26;

if Process then return Nmr; else return L; end if;

end function;
