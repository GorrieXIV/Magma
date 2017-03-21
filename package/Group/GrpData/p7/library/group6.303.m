freeze;

import "misc.m": ProcessPresentation; 

Group6_303 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.303 valid only for p>3"; return false; end if;
 
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

GR:=Group<a,b,c | (c,b), (b,a,b)=(b,a,a), a^p, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p, b^p=d*f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p, 
                        b^p=d*f^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p, 
                        b^p=d*f^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=4;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p=f, 
                            b^p=d*f^x, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  if p mod 3 eq 1 then
    GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p=f^w, 
                                b^p=d*f^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p=f^w2, 
                                b^p=d*f^x, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    count:=count+2;
  end if;
end for;
for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e*f, a^p=f^x, 
                            b^p=d*f^y, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p, b^p=d, 
                            c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p, b^p=d, 
                            c^p=f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p, b^p=d, 
                              c^p=f^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e, a^p, b^p=d, 
                              c^p=f^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|d=(c,a),e=(b,a,a),f=(e,a),(c,b), (b,a,b)=e*f, a^p, b^p=d, 
                            c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;

vprint Orderp7, 1: "Group 6.303 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is p^2 + p + (p+1)gcd(p-1,3) + gcd(p-1,4) =",
p^2+p+(p+1)*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
