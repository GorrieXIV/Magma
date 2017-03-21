freeze;

import "misc.m": ProcessPresentation; 

Group6_445 := function (p: Process:=true, Select:=func<x|true>)

if p lt 7 then "6.445 is valid only for p>5"; return false; end if;

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

r:=(p-3) div 2;
s:=(r*w) mod p;
t:=(s*w) mod p;

L:=[]; Nmr := 0;
count:=0;
if p mod 3 ne 1 then
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p=e^x, 
                            b^p=d*e^r>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p, 
                            b^p=d*e^(r+x)>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
else;
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p, 
                            b^p=d*e^r>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p, 
                            b^p=d^w*e^s>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p, 
                            b^p=d^w2*e^t>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p=e^x, 
                                b^p=d*e^r>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p, 
                                b^p=d*e^(r+x)>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p=e^x, 
                                b^p=d^w*e^s>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p, 
                                b^p=d^w*e^(s+x)>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p=e^x, 
                                b^p=d^w2*e^t>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e|c=a^p,d=(b,a,a,a),e=(d,a),(b,a,b)=d*e^-1, c^p, 
                                b^p=d^w2*e^(t+x)>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+6;
    end if;
  end for;
end if;

vprint Orderp7, 1: "Groups 6.445 - 6.447 have",count,"descendants of order p^7 and p-class 5";

vprint Orderp7, 2: "Total number of groups is 2p - 2 + gcd(p-1,3) =",
2*p-2+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;
