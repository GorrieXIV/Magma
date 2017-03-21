freeze;

import "misc.m": ProcessPresentation; 

Group6_222 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.222 valid only for p>3"; return false; end if;
 
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

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e*f^-1, a^p, b^p, 
                      d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|d=c^p,e=(b,a,a),(b,a,b), (c,a), (c,b)=e, a^p, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e*f^-1, a^p, b^p, 
                      d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e, a^p, b^p, 
                      d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                      a^p, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                      a^p, b^p, d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=6;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                              a^p, b^p, d^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                              a^p, b^p, d^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e*f^-1, a^p, 
                          b^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e*f^-1, a^p, 
                              b^p=f^w, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e*f^-1, a^p, 
                              b^p=f^w2, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e*f^-1, 
                          a^p=f, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e, a^p, b^p=f^x, 
                            d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b), (c,a), (c,b)=e, a^p=f, b^p, 
                            d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e, 
                            a^p=f, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                            a^p=f^w, b^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                              a^p=f^w2, b^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                              a^p=f^w3, b^p, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                          a^p, b^p=f, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                              a^p, b^p=f^w, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                              a^p, b^p=f^w2, d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
CU:=1;
if p mod 3 eq 2 then
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                              a^p=f^x, b^p=f, d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
else;
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
      GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                                  a^p=f^x, b^p=f, d^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                                  a^p=f^x, b^p=f^w, d^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e,f|d=c^p,e=(b,a,a),f=(e,a),(b,a,b)=f, (c,a), (c,b)=e*f^-1, 
                                  a^p=f^x, b^p=f^w2, d^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+3;
    end if;
  end for;
end if;

vprint Orderp7, 1: "Group 6.222 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is 2p + 5 + 3gcd(p-1,3) + gcd(p-1,4) =",
2*p+5+3*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
