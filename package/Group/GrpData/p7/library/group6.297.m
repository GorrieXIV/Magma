freeze;

import "misc.m": ProcessPresentation; 

Group6_297 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.297 valid only for p>3"; return false; end if;
 
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
  GR:=Group<a,b,c,d,e,f | d=(c,a),e=(b,a,b),f=(e,b),(c,b), (b,a,a), a^p, b^p=d*e*f^-1, 
                              c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(c,a),e=(b,a,b),f=(e,b),(c,b), (b,a,a), a^p=f, 
                              b^p=d*e*f^-1, c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
  if p mod 3 eq 1 then
    GR:=Group<a,b,c,d,e,f | d=(c,a),e=(b,a,b),f=(e,b),(c,b), (b,a,a), a^p=f^w, 
                                b^p=d*e*f^-1, c^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f | d=(c,a),e=(b,a,b),f=(e,b),(c,b), (b,a,a), a^p=f^w2, 
                                b^p=d*e*f^-1, c^p=f^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(c,a),e=(b,a,b),f=(e,b),(c,b), (b,a,a), a^p=f^x, b^p=d*e, 
                            c^p=f^-2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.297 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2p + pgcd(p-1,3) =",
2*p+p*Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
