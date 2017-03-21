freeze;

import "misc.m": ProcessPresentation; 

Group6_144 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.144 valid only for p>3"; return false; end if;

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
count:=0;

for y in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e*f^w, (c,b), 
    a^p=e*f^w, b^p=d^w*f^-w, c^p=f^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if y^2 mod p eq (2*w^3) mod p then
    for x in [1..((p-1) div 2)] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e*f^w, (c,b), 
        a^p=e*f^w, b^p=d^w*f^(x-w), c^p=f^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
  end if;
end for;
for y in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e*f, (c,b),
    a^p=e^w*f^w, b^p=d^w*f^-w, c^p=f^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if (y^2) mod p eq (2*w^2) mod p then
    for x in [1..((p-1) div 2)] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(d,a),(c,a)=e*f, (c,b), 
        a^p=e^w*f^w, b^p=d^w*f^(x-w), c^p=f^y>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end for;
  end if;
end for;

vprint Orderp7, 1: "Groups 6.144 and 6.145 (between them) have",count,"descendants";
vprint Orderp7, 2:"of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (3p+1)/2 =",(3*p+1)/2;

if Process then return Nmr; else return L; end if;

end function;
