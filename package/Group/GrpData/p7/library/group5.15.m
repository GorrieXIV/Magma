freeze;

import "misc.m": ProcessPresentation; 

Group5_15 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "5.15 valid only for p>3"; return false; end if;

class:=3;

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
QU:=1;

L:=[]; Nmr := 0;

GR:=Group<a,b,c | (c,b), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f^w, b^p, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=d*e*f^x,b^p,c^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
count:=p+7;
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d, b^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f, b^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f^w, b^p, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=d*e*f^x,b^p,c^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*e^x, b^p, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=d*e*f,b^p,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=d*e*f^w,b^p,c^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f^w, b^p=e, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+5;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f^w2, b^p=e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*f^w3, b^p=e, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b),a^p=d*f^x,b^p=e,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d*e, b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d, b^p=f, c^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d, b^p=f, c^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+4;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d, b^p=f, c^p=e^w2>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b), a^p=d, b^p=f, c^p=e^w3>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e, a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e, a^p=d*f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e, a^p=d*f^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e, a^p=d, b^p, c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=d*f,b^p,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=d*f^w,b^p,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=d*e*f^y,b^p,c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=d*f^x,b^p,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..((p-1) div 2)] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=d*f^y,b^p=e,c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e,a^p=d,b^p=f,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
if p mod 4 eq 3 then
  for x in [1..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e, a^p=d*e^x, b^p=f,c^p=e^-2>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
if p mod 4 eq 1 then
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for x in [1..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=(p-x1) mod p;
    if x le x1 and x le x2 then
      count:=count+1;
      GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e, a^p=d*e^x, b^p=f,c^p=e^-2>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+1;
      GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e, a^p=d*e^x, b^p=f^w,c^p=e^-2>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end if;
  end for;
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e, a^p=d, b^p=f^w, c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w, a^p=d, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w, a^p=d*f, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w, a^p=d*f^w, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [1..p-1] do
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w, a^p=d, b^p, c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w,a^p=d*f,b^p,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w,a^p=d*f^w,b^p,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+3;
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w, a^p=d*e*f^y, b^p,c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w,a^p=d*f^x,b^p,c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
for x in [0..((p-1) div 2)] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w,a^p=d*f^y,b^p=e,c^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w,a^p=d,b^p=f,c^p=e^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
end for;
if p mod 4 eq 3 then
  for x in [1..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w,a^p=d*e^x,b^p=f,c^p=e^-(2*w)>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;
if p mod 4 eq 1 then
  for x in [1..((p-1) div 2)] do
    x1:=(QU*x) mod p; x2:=(p-x1) mod p;
    if x le x1 and x le x2 then
      count:=count+1;
      GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w,a^p=d*e^x,b^p=f,c^p=e^-(2*w)>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+1;
      GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w,a^p=d*e^x,b^p=f^w,c^p=e^-(2*w)>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    end if;
  end for;
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f | d=(b,a),e=(c,a,a),f=(c,a,c),(c,b)=e^w, a^p=d, b^p=f^w, c^p=e^x>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  end for;
end if;

vprint Orderp7, 1: "Group 5.15 has",count,"descendants of order p^7 and class 3";

vprint Orderp7, 2: "Total number of groups is 3p^2 + 12p + 14 + (p+2)gcd(p-1,4) =",
3*p^2+12*p+14+(p+2)*Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;

Children32 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_15 (p: Process:=Process, Select:=Select);
end function;
