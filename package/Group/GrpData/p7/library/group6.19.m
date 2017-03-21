freeze;

import "misc.m": ProcessPresentation; 

Group6_19 := function (p: Process:=true, Select:=func<x|true>)

if p lt 5 then "6.19 valid only for p>3"; return false; end if;

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

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p=e^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p=e^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p=e,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p=e^w,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p=e^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p=e^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),
(d,a)=e,(d,b),(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),
(d,a)=e,(d,b),(d,c),a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),
(d,a)=e,(d,b),(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),
(d,a)=e,(d,b),(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),
(d,a)=e,(d,b),(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),
(d,a)=e,(d,b),(d,c),a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),
(d,a)=e,(d,b),(d,c),a^p=e^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c),
(d,a)=e,(d,b),(d,c),a^p=e^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c),a^p=e^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c)=e,a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c)=e,a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c)=e,a^p,b^p,c^p=e^w,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c)=e,a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c)=e,a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c)=e,a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a)=e,(c,a,c),
(d,a),(d,b),(d,c)=e,a^p=e^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),(d,a),
(d,b),(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),(d,a),
(d,b),(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),(d,a),
(d,b),(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),(d,a),
(d,b),(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),(d,a),
(d,b),(d,c),a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),(d,a),
(d,b),(d,c),a^p=e^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),(d,a),
(d,b),(d,c),a^p,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),(d,a),
(d,b),(d,c),a^p=e,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a),(d,b),(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a),(d,b),(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a),(d,b),(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a),(d,b),(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a),(d,b),(d,c),a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a),(d,b),(d,c),a^p=e^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),
(d,a)=e,(d,b),(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),
(d,a)=e,(d,b),(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),
(d,a)=e,(d,b),(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),
(d,a)=e,(d,b),(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),
(d,a)=e,(d,b),(d,c),a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),
(d,a)=e,(d,b),(d,c),a^p=e^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),
(d,a)=e,(d,b),(d,c),a^p,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b),
(d,a)=e,(d,b),(d,c),a^p=e,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a)=e,(d,b),(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a)=e,(d,b),(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a)=e,(d,b),(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a)=e,(d,b),(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a)=e,(d,b),(d,c),a^p=e,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,b),(c,b),(b,a,a),(b,a,c),(c,a,a),(c,a,c)*(b,a,b)^w,
(d,a)=e,(d,b),(d,c),a^p=e^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d|(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p=e^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c),a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),
(d,b)=e,(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),
(d,b)=e,(d,c),a^p,b^p,c^p=e,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),
(d,b)=e,(d,c),a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),
(d,b)=e,(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),
(d,b)=e,(d,c),a^p,b^p=e^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),
(d,b)=e,(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),
(d,b)=e,(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p=e,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p=e^w,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p=e^w,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p=e^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b),(b,a,b),(b,a,c),(c,a,a),(c,a,c),(d,a),(d,b),
(d,c)=e,a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b)=e,(b,a,b),(b,a,c),(c,a,a),(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b)=e,(b,a,b),(b,a,c),(c,a,a),(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b)=e,(b,a,b),(b,a,c),(c,a,a),(c,a,c),
(d,a),(d,b),(d,c),a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b)=e,(b,a,b),(b,a,c),(c,a,a),(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b)=e,(b,a,b),(b,a,c),(c,a,a),(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p=e^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,b)=e,(b,a,b),(b,a,c),(c,a,a),(c,a,c),
(d,a),(d,b),(d,c),a^p,b^p,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1: "Group 6.19 has 97 descendants of order p^7 and p-class 3";

vprint Orderp7, 2: "Total number of groups is 97";

if Process then return Nmr; else return L; end if;

end function;
