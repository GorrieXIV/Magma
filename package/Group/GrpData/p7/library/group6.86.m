freeze;

import "misc.m": ProcessPresentation; 

Group6_86 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.86 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,e,f | e=a^p,f=b^p,(b,a,a), (b,a,b), e^p, f^p, (c,a), (c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e | d=(b,a),e=a^p,(d,a), (d,b), d^p, e^p, (c,a), (c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=a^p,f=b^p,(d,a),(d,b),d^p,e^p,(c,a),(c,b)=f^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=a^p,f=b^p,(d,a),(d,b),d^p,e^p,(c,a)=f^p,(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=a^p,f=b^p,(d,a),(d,b),d^p=f^p,e^p,(c,a),(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p,f^p,(c,a),(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p,f^p,(c,a),(c,b),c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p,f^p,(c,a)=g,(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p,f^p,(c,a)=g,(c,b),c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p,f^p=g,(c,a),(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p,f^p=g,(c,a)=g,(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p=g,f^p,(c,a),(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p=g,f^p,(c,a)=g,(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p=g^w,f^p,(c,a),(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a),d^p,e^p=g^w,f^p,(c,a)=g,(c,b),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=15;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a), d^p=g, e^p=g^x, f^p, 
                           (c,a), (c,b), c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a), d^p=g, e^p=g^-1, f^p, (c,a), 
                           (c,b), c^p=g>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f,g|d=(b,a),e=a^p,f=b^p,g=(d,b),(d,a), d^p=g, e^p, f^p=g, 
                           (c,a), (c,b), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;

vprint Orderp7, 1: "Group 6.86 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is p + 17 =",p+17;

if Process then return Nmr; else return L; end if;

end function;
