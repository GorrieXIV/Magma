freeze;

import "misc.m": ProcessPresentation; 

Group6_94 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.94 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;

GR:=Group<a,b,c|(c,a,a),(c,a,c),(c,b),a^p,c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e | e=b^p,(c,a,a),(c,a,c),(c,b)=e^p,a^p,c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,e | e=b^p,(c,a,a),e^p,(c,b),a^p,c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(c,a,a),e^p,(c,b),a^p=f,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(c,a,a),e^p,(c,b),a^p=f^w,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(c,a,a),e^p,(c,b),a^p,c^p=d*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(c,a,a),e^p,(c,b),a^p=f,c^p=d*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(c,a,a),e^p,(c,b),a^p=f^w,c^p=d*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,c),(c,a,a),e^p=f,(c,b),a^p,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p,(c,b),a^p,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p,(c,b),a^p=f,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p,(c,b)=f,a^p,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p,(c,b)=f,a^p=f,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p,(c,b)=f,a^p=f^w,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=14;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p,(c,b)=f,a^p=f^w2,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p,(c,b)=f,a^p=f^w3,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=16;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p=f,(c,b),a^p,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p=f^w,(c,b),a^p,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p=f^w2,(c,b),a^p,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p=f,(c,b)=f,a^p,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p=f^w,(c,b)=f,a^p,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c),e^p=f^w2,(c,b)=f,a^p,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c)=f,e^p,(c,b),a^p,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c)=f,e^p,(c,b),a^p,c^p=d*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c)=f,e^p,(c,b),a^p,c^p=d*f^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
count:=count+3;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c)=f,e^p,(c,b),a^p=f,c^p=d*f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c)=f,e^p,(c,b),a^p=f^w,c^p=d*f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c)=f,e^p=f,(c,b),a^p,c^p=d>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c)=f,e^p=f^w,(c,b),a^p,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  GR:=Group<a,b,c,d,e,f|d=(b,a),e=b^p,f=(c,a,a),(c,a,c)=f,e^p=f^w2,(c,b),a^p,c^p=d>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
  count:=count+2;
end if;

vprint Orderp7, 1: "Group 6.94 has",count,"descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 2p + 15 + 3gcd(p-1,3) + gcd(p-1,4) =",
2*p+15+3*Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
