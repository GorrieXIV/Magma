freeze;

import "misc.m": ProcessPresentation; 

Group6_269 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.269 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,c),f=(e,c),(c,b), (c,a,a), a^p=d*e*f^-1, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,c),f=(e,c),(c,b), (c,a,a), a^p=d*e*f^-1, 
                      b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
for x in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,c),f=(e,c),(c,b), (c,a,a), a^p=d*e*f^-1, 
                            b^p=f^x, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.269 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p + 5)/2 =",(p+5)/2;

if Process then return Nmr; else return L; end if;

end function;
