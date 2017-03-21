freeze;

import "misc.m": ProcessPresentation; 

Group6_273 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.273 valid only for p>3"; return false; end if;
 
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
w3:=w^3 mod p;
r:=(p+1) div 2;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(e,a),(c,b), (c,a,c), a^p=d*f^r, 
                      b^p=e*f^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(e,a),(c,b), (c,a,c)=f, a^p=d*f^r,
                      b^p=e*f^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(e,a),(c,b), (c,a,c)=f^w, a^p=d*f^r,
                      b^p=e*f^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(e,a),(c,b), (c,a,c)=f^w2, 
               a^p=d*f^r, b^p=e*f^-1, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(e,a),(c,b), (c,a,c)=f^w3, 
               a^p=d*f^r, b^p=e*f^-1, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=5;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(e,a),(c,b)=f, (c,a,c), a^p=d*f^r,
                          b^p=e*f^-1, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(e,a),(c,b)=f^w, (c,a,c), a^p=d*f^r,
                              b^p=e*f^-1, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=(c,a,a),f=(e,a),(c,b)=f^w2, (c,a,c), 
                         a^p=d*f^r, b^p=e*f^-1, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.273 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 1 + gcd(p-1,3) + gcd(p-1,4) =",
1+Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
