freeze;

import "misc.m": ProcessPresentation; 

Group6_280 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.280 valid only for p>3"; return false; end if;
 
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

u1:=p-w;
u2:=(2*w) mod p;
u3:=(w*(p+1)) div 2; u3:=u3 mod p;

L:=[]; Nmr := 0;
count:=0;

for x in [1..p-1] do
  if x eq u1 or x eq u2 or x eq u3 then continue; end if;
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(c,a,a),e=(d,a),(c,b)=d^w*e^-w, (c,a,c), a^p=(b,a), b^p, 
                            c^p=d^x*e^-x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e|d=(c,a,a),e=(d,a),(c,b)=d^w*e^-w, (c,a,c), a^p=(b,a), b^p, 
                              c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|d=(c,a,a),e=(d,a),(c,b)=d^w*e^-w, (c,a,c), a^p=(b,a), 
                              b^p=e, c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e|d=(c,a,a),e=(d,a),(c,b)=d^w*e^-w, (c,a,c), a^p=(b,a), b^p, 
                            c^p=d^-w*e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a,a),e=(d,a),(c,b)=d^w*e^-w, (c,a,c), a^p=(b,a), 
                            b^p=e, c^p=d^-w*e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e|d=(c,a,a),e=(d,a),(c,b)=d^w*e^-w, (c,a,c), a^p=(b,a), b^p, 
                            c^p=d^(2*w)*e^(x-2*w)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e|d=(c,a,a),e=(d,a),(c,b)=d^w*e^-w, (c,a,c), a^p=(b,a), b^p, 
                            c^p=d^u3*e^-u3>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=(c,a,a),e=(d,a),(c,b)=d^w*e^-w, (c,a,c)=e, 
                            a^p=(b,a), b^p, c^p=d^u3*e^-u3>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;

vprint Orderp7, 1: "Group 6.280 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (5p + 3)/2 =",(5*p+3)/2;

if Process then return Nmr; else return L; end if;

end function;
