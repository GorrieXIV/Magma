freeze;

import "misc.m": ProcessPresentation; 

Group6_134 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.134 valid only for p>3"; return false; end if;

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

w2:=w^2 mod p;

L:=[]; Nmr := 0;
count:=0;

for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b), a^p=d, b^p, 
                              c^p=f^x>;  
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b), a^p=d, 
                              b^p=f, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b), 
                            a^p=d*f, b^p, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b), 
                              a^p=d*f^w, b^p, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b), 
                              a^p=d*f^w2, b^p, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(e,b),(c,a)=e*f^-1, (c,b), 
                   a^p=d*f^x, b^p=f, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.134 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 3p - 1 + gcd(p-1,3) =",
3*p-1+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
