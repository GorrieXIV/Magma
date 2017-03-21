freeze;

import "misc.m": ProcessPresentation; 

Group6_198 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.198 valid only for p>3"; return false; end if;

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

GR:=Group<a,b,c,d,e,f|d=a^p,e=(b,a,b),f=(e,b),(b,a,a), (c,a)=e*f^-1, (c,b), 
                      d^p=f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=1;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=a^p,e=(b,a,b),f=(e,b),(b,a,a), (c,a)=e*f^-1, (c,b), 
                        d^p=f^w, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=a^p,e=(b,a,b),f=(e,b),(b,a,a), (c,a)=e*f^-1, (c,b), 
                        d^p=f^w2, b^p, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=3;
end if;
GR:=Group<a,b,c,d,e,f|d=a^p,e=(b,a,b),f=(e,b),(b,a,a), (c,a)=e*f^-1, (c,b), d^p, b^p, 
                            c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=a^p,e=(b,a,b),f=(e,b),(b,a,a), (c,a)=e*f^-1, (c,b), d^p, b^p, 
                            c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=a^p,e=(b,a,b),f=(e,b),(b,a,a), (c,a)=e*f^-1, (c,b), d^p, 
                            b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=a^p,e=(b,a,b),f=(e,b),(b,a,a), (c,a)=e*f^-1, (c,b), d^p, 
                            b^p=f, c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;

vprint Orderp7, 1: "Group 6.198 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 4 + gcd(p-1,3) =",
4+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
