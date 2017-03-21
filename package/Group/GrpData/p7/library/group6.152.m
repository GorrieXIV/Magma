freeze;

import "misc.m": ProcessPresentation; 

Group6_152 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.152 valid only for p>3"; return false; end if;

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

r:=(p-1) div 2;
w2:=w^2 mod p;

L:=[]; Nmr := 0;

GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b), a^p=e, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b), a^p=e, 
                      b^p=f, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=2;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b), a^p=e, 
                        b^p=f^w, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b), a^p=e, 
                        b^p=f^w2, c^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=4;
end if;
QU:=1;
if p mod 4 eq 3 then
  for y in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b), 
                              a^p=e*f, b^p=f^y, c^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    for x in [0..p-1] do
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b)=f, 
                           a^p=e*f^x, b^p=f^y, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+1;
    end for;
  end for;
else;
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for y in [0..((p-1) div 2)] do
    y1:=(QU*y) mod p; y2:=p-y1;
    if y le y1 and y le y2 then
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b), 
                           a^p=e*f, b^p=f^y, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b), 
                           a^p=e*f^w, b^p=f^y, c^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
      count:=count+2;
      for x in [0..p-1] do
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b)=f, 
                             a^p=e*f^x, b^p=f^y, c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b)=f^w, 
                             a^p=e*f^x, b^p=f^y, c^p>;
        ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
        count:=count+2;
      end for;
    end if;
  end for;
end if;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b)=f^x, 
                              a^p=e, b^p, c^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a,a),e=(b,a,b),f=(b,a,a,a),(c,a)=d*f^r, (c,b)=f^x, 
                              a^p=e, b^p, c^p=f^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;

vprint Orderp7, 1: "Group 6.152 has",count,"descendants of order p^7 and p-class 4";

vprint Orderp7, 2: "Total number of groups is (p^2 + 2p + 3 + 2gcd(p-1,3) + (p+1)gcd(p-1,4))/2 =",
(p^2+2*p+3+2*Gcd(p-1,3)+(p+1)*Gcd(p-1,4))/2;

if Process then return Nmr; else return L; end if;

end function;
