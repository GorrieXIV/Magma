freeze;

import "misc.m": ProcessPresentation; 

Group6_460 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.460 is valid only for p>5"; return false; end if;

class:=5;

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

r:=(F!7)*(F!6)^-1; r:=Integers()!r;

L:=[]; Nmr := 0;
count:=0;
if p mod 4 eq 3 then
  for x in [0..((p-1) div 2)] do
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, 
                              c^p=e^x, b^p=d>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, 
                              c^p=e^x, b^p=d^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
  for x in [1..p-1] do
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, c^p, 
                              b^p=d*e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, c^p, 
                              b^p=d^w*e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end for;
else;
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [0..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=p-x1;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, 
                              c^p=e^x, b^p=d>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, 
                              c^p=e^x, b^p=d^w>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, 
                              c^p=e^x, b^p=d^w2>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, 
                              c^p=e^x, b^p=d^w3>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+4;
    end if;
    if x ne 0 then
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, c^p, 
                                b^p=d*e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, c^p, 
                                b^p=d^w*e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, c^p, 
                                b^p=d^w2*e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,b,b),e=(d,a),(b,a,a)=d*e^r, c^p, 
                                b^p=d^w3*e^x>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+4;
    end if;
  end for;
end if;

vprint Orderp7, 1: "Groups 6.460 - 6.463 have",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 3p - 3 + gcd(p-1,4) =",
3*p-3+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
