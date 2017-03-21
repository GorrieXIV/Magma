freeze;

import "misc.m": ProcessPresentation; 

Group4_1aa := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

class:=2;
limited := not Process and Limit ge 1;

//You need 4.1aa, 4.1a, 4.1b, 4.1c, 4.1d, 4.11, 4.12, 4.13, 4.14, 4.15, 4.16

//L^2 has order 1 or p

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
GR:=Group<a,b,c,d|(b,a),(c,a),(d,a),(c,b),(d,b),(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c),a^p=(b,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c),b^p,c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c),b^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c),b^p=(b,a),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c),c^p=(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c)=(b,a),a^p,c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c)=(b,a),a^p=(b,a),c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c)=(b,a),a^p,b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(c,b),(d,b),(d,c)=(b,a),a^p=(b,a),b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;

vprint Orderp7, 1: 
"Group 4.1aa has one abelian descendant of order p^7 and class 2,";
vprint Orderp7,1:
"and 11 descendants of order p^7 and class 2 with L^2 of order p";
vprint Orderp7, 2: "Total number of groups is 12";

if Process then return Nmr; else return L; end if;

end function;

Group4_1a := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//Descendants of 4.1 with L^2 of order p^2: Case 1
//[c,b]=[d,a]=[d,b]=[d,c]=1

class:=2;
limited := not Process and Limit ge 1;

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
vprint Orderp7, 2: "p equals",p;
vprint Orderp7, 2: "w equals",w;

INV:={1};
for x in [2..p-1] do
  y:=F!x;
  y:=y^-1;
  z:=Integers()!y;
  if x le z then
    Include(~INV,x);
  end if;
end for;

SQ:={};
for x in [0..p-1] do
  y:=F!x;
  Include(~SQ,y^2);
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p=(b,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p=(c,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, c^p=(b,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, c^p=(c,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(b,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(c,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=8;
for x in INV do
count:=count+1;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p=(b,a), c^p=(c,a)^x, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p=(b,a)*(c,a), c^p=(c,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p=(c,a)^w, c^p=(b,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for x in [1..p-1] do
y:=F!x;
if (1+4*y) notin SQ then
count:=count+1;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p=(c,a)^x, c^p=(b,a)*(c,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
end for;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(c,a), c^p=(b,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(b,a), c^p=(c,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(c,a), b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(b,a), b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+8;
for x in INV do
count:=count+1;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p=(b,a), c^p=(c,a)^x>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p=(b,a)*(c,a), c^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p=(c,a)^w, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for x in [1..p-1] do
y:=F!x;
if (1+4*y) notin SQ then
count:=count+1;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p=(c,a)^x, c^p=(b,a)*(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
end for;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p, d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, b^p=(b,a), d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(b,a), b^p, 
d^p*(c,a)^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, c^p, d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p, c^p=(b,a), d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), a^p=(b,a), c^p, d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p, c^p, d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p, c^p=(b,a), d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,b), (d,a), (d,b), (d,c), b^p=(b,a), c^p, d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;

vprint Orderp7, 2: "There are",count+9,"four generator p-class 2 groups satisfying";
vprint Orderp7, 2: "[c,b] = [d,a] = [d,b] = [d,c] = 1";

vprint Orderp7, 2: "Total number of groups is 2p + 29 =",2*p+29;

if Process then return Nmr; else return L; end if;

end function;

Group4_1b := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//Descendants of 4.1 with L^2 of order p^2: Case 2
//[c,a]=[c,b]=[d,a]=[d,b]=1

class:=2;
limited := not Process and Limit ge 1;

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
vprint Orderp7, 2: "p equals",p;
vprint Orderp7, 2: "w equals",w;

INV:={1};
for x in [2..p-1] do
  y:=F!x;
  y:=y^-1;
  z:=Integers()!y;
  if x le z then
    Include(~INV,x);
  end if;
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p, c^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p, c^p*(b,a)^-1*(d,c)^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(b,a), c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(b,a), c^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(b,a), c^p=(b,a)*(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(d,c), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(d,c), c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(d,c), c^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(d,c), c^p=(b,a)*(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(b,a)*(d,c), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(b,a)*(d,c), c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=14;
for x in [0..p-1] do
count:=count+1;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, b^p=(b,a)*(d,c), c^p=(b,a)^x*(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a), b^p=(d,c), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a), b^p=(d,c), c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a), b^p=(d,c), c^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a), b^p=(d,c), c^p=(b,a)*(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p, d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p, d^p=(b,a)^-1*b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p, d^p=(b,a)^-1*(d,c)^-1*b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p=(b,a), d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p=(b,a), d^p=(d,c)^-1*b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p=(d,c), d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p=(d,c), d^p=(b,a)^-1*b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p=(b,a)*(d,c), d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p, c^p=(b,a)*(d,c), d^p=(b,a)^-1*b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a), c^p=(b,a), d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a), c^p=(b,a), d^p=(d,c)^-1*b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+15;
for x in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a), c^p=(b,a)*(d,c)^x, d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in INV do
count:=count+1;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a), c^p=(d,c)^x, d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(d,c), c^p=(b,a), d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(d,c), c^p=(b,a)^w, d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for x in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(d,c), c^p=(b,a)^x*(d,c), d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in [1..p-1] do
for y in INV do
count:=count+1;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a)*(d,c), c^p=(b,a)^x*(d,c)^y, d^p=b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for y in INV do
count:=count+1;
GR:=Group<a,b,c,d | (c,a), (d,a), (c,b), (d,b), a^p=(b,a)*(d,c), c^p=(b,a)^y*(d,c)^y, d^p=(b,a)^-1*b^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;

vprint Orderp7, 2: "There are",count,"four generator p-class 2 groups satisfying";
vprint Orderp7, 2: "[c,a] = [c,b] = [d,a] = [d,b] = 1";
expect:=(p^2-1) div 2;
expect:=expect+4*p+30;

vprint Orderp7, 2:
   "Total number of groups is (p^2 - 1)/2 + 4p + 30 =",expect;

if Process then return Nmr; else return L; end if;

end function;

Group4_1c := function (p: Process:=true, Select:=func<x|true>, Limit:=0) 

//Descendants of 4.1 with L^2 of order p^2: Case 3
//[c,b]=[d,a]=[d,c]=1, [d,b]=[c,a]

class:=2;
limited := not Process and Limit ge 1;

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
vprint Orderp7, 2: "p equals",p;
vprint Orderp7, 2: "w equals",w;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p=(c,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p=(b,a), b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p=(c,a), b^p=(b,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p=(c,a), b^p, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p=(b,a), c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p=(c,a), b^p=(b,a), c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=11;
for x in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p=(b,a)*(c,a)^x, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p=(c,a), c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p=(c,a)^w, c^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p, c^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p=(b,a), b^p, c^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+4;
for x in [1..p-1] do
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p=(b,a)^x, c^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), a^p, b^p=(b,a)*(c,a), c^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p=(b,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p=(c,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p, c^p=(b,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p=(c,a), c^p=(b,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p=(c,a)^w, c^p=(b,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+7;
for x in [0..p-1] do
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p=(b,a)^x, c^p=(c,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p, c^p, d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p=(c,a), c^p, d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p, c^p, d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p=(b,a), c^p, d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p, c^p=(b,a), d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c), b^p, c^p=(c,a), d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;

vprint Orderp7, 2: "There are",count+6,"four generator p-class 2 groups satisfying";
vprint Orderp7, 2: "[c,b] = [d,a] = [d,c] = 1, [d,b]=[c,a]";
vprint Orderp7, 2: "Total number of groups is 3p + 26 =",3*p+26;

if Process then return Nmr; else return L; end if;

end function;

Group4_1d := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//Descendants of 4.1 with L^2 of order p^2: Case 4
//[d,a]=[c,b]=1, [d,b]=[c,a], [d,c]=[b,a]^w
/*
This program computes the orbits of the non-singular 2x2 matrices
needed for algebra 7.311

We let S be the set of non-singular 2x2 matrices and we let G be
the group of non-singular matrices of the form

                 [a      b   ]
                 [+/-wb  +/-a]

(Note that this matrix is non-singular unless a = b = 0, so that
G has order 2(p^2 - 1).)

We let G L (Z_p\{0}) act on S as follows: if P in G and c in Z_p\{0},
and A in S then (P,c) sends A to

            cPAP^-1.

We attach a numerical index to each matrix, and we
print out the matrix in each orbit of lowest index.

*/

class:=2;
limited := not Process and Limit ge 1;

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
vprint Orderp7, 2: "p equals",p;
vprint Orderp7, 2: "w equals",w;

range:={[0,1]};
for i in [0..p-1] do
  Include(~range,[1,i]);
end for;

Z:=Integers();
M:=MatrixAlgebra(F,2);
A:=M!0;
B:=M!0;
mats:=[];
for s in range do
x:=s[1]; y:=s[2];
A[1][1]:=F!x;
A[1][2]:=F!y;
for z in [0..p-1] do
A[2][1]:=F!z;
for t in [0..p-1] do
A[2][2]:=F!t;
if Rank(A) eq 2 then
index:=p^3*x+p^2*y+p*z+t;
new:=1;

for r in range do
a:=r[1]; b:=r[2];

B[1][1]:=F!a;
B[2][2]:=F!a;
B[1][2]:=F!b;
B[2][1]:=F!(w*b);
C:=B*A*B^-1;

u:=C[1][1];
if u eq 0 then u:=C[1][2]; end if;
C:=u^-1*C;
  
x1:=Z!(C[1][1]);
y1:=Z!(C[1][2]);
z1:=Z!(C[2][1]);
t1:=Z!(C[2][2]);
ind1:=p^3*x1+p^2*y1+p*z1+t1;

if ind1 lt index then new:=0; break; end if;

B[2][1]:=-B[2][1];
B[2][2]:=-B[2][2];
C:=B*A*B^-1;

u:=C[1][1];
if u eq 0 then u:=C[1][2]; end if;
C:=u^-1*C;
  
x1:=Z!(C[1][1]);
y1:=Z!(C[1][2]);
z1:=Z!(C[2][1]);
t1:=Z!(C[2][2]);
ind1:=p^3*x1+p^2*y1+p*z1+t1;

if ind1 lt index then new:=0; break; end if;

end for;

if new eq 1 then
  n:=#mats;
  mats[n+1]:=[x,y,z,t];
end if;

end if;
end for;
end for;
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c)=(b,a)^w, a^p, b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c)=(b,a)^w, a^p=(b,a), b^p, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=2;
xend:=(p-1) div 2;
for x in [0..xend] do
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c)=(b,a)^w, a^p, b^p=(b,a)*(c,a)^x, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c)=(b,a)^w, a^p=(c,a), b^p=(b,a)*(c,a)^x, c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c)=(b,a)^w, a^p, b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c)=(b,a)^w, a^p=(b,a), b^p=(c,a), c^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for s in mats do
x:=s[1];
y:=s[2];
z:=s[3];
t:=s[4];
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (c,b), (d,b)=(c,a), (d,c)=(b,a)^w, a^p, 
b^p=(b,a)^x*(c,a)^y, c^p=(b,a)^z*(c,a)^t>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;

vprint Orderp7, 2: "There are",count,"four generator p-class 2 groups satisfying";
vprint Orderp7, 2: "[c,b] = [d,a] = 1, [d,b] = [c,a], [d,c] = [b,a]^w";
expect:=(p^2-1) div 2;
expect:=expect+2*p+6;
vprint Orderp7, 2: 
   "Total number of groups is (p^2 - 1)/2 + 2p + 6 =",expect;

if Process then return Nmr; else return L; end if;

end function;

Group4_11 := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//Descendants of 4.1 with L^2 of order p^3: Case 1 - [d,a]=[d,b]=[d,c]=1

class:=2;

limited := not Process and Limit ge 1;
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

INV:={1};
for x in [2..p-1] do
  y:=F!x;
  y:=y^-1;
  z:=Integers()!y;
  if x le z then
    Include(~INV,x);
  end if;
end for;

SQ:={};
for x in [0..p-1] do
  y:=F!x;
  Include(~SQ,y^2);
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p, b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(c,b), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=3;
for x in INV do
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(c,a), b^p=(c,b)^x, c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(c,a)*(c,b), b^p=(c,b), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(c,b)^w, b^p=(c,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for x in [1..p-1] do
y:=F!x;
if (1+4*y) notin SQ then
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(c,b)^x, b^p=(c,a)*(c,b), c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
end for;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p=(c,a), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p=(c,b), c^p, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for x in [0..p-1] do
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p=(c,b), c^p=(b,a)^x*(c,a), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p=(c,a), c^p=(c,b), d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p=(c,a), c^p=(c,b)^-1, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p=(c,a), c^p=(b,a)^w*(c,b)^-1, d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p, b^p, c^p, d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p, c^p, d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p, b^p=(b,a), c^p, d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(c,a), b^p=(b,a), c^p, d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p, b^p=(c,a), c^p, d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p=(b,a), b^p=(c,a), c^p, d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+9;
for x in INV do
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p, b^p=(b,a), c^p=(c,a)^x, d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p, b^p=(b,a)*(c,a), c^p=(c,a), d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p, b^p=(c,a)^w, c^p=(b,a), d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for x in [1..p-1] do
y:=F!x;
if (1+4*y) notin SQ then
count:=count+1;
GR:=Group<a,b,c,d | (d,a), (d,b), (d,c), a^p, b^p=(c,a)^x, c^p=(b,a)*(c,a), d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
end for;

vprint Orderp7, 2:"There are",count,"four generator p-class 2 groups satisfying";
vprint Orderp7, 2:"[d,a] = [d,b] = [d,c] = 1";

vprint Orderp7, 2: "Total number of groups is 3p+18 =",3*p+18;

if Process then return Nmr; else return L; end if;

end function;

Group4_12 := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//Descendants of 4.1 with L^2 or order p^3, Case 2
//Four generator p-class 2 groups satisfying [c,a]=[d,a]=[d,b]=1

class:=2;
limited := not Process and Limit ge 1;

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
SQ:={};
for i in [1..((p-1) div 2)] do
  j:=i^2 mod p;
  Include(~SQ,j);
end for;
L:=[]; Nmr := 0;

//pa=pd=0

GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p,c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(d,c),c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a),c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a)*(d,c),c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b),c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b),c^p=(c,b)*(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b),c^p=(b,a)*(c,b)*(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p,c^p=(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p,c^p=(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p,c^p=(b,a)*(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(d,c),c^p=(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(d,c),c^p=(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(d,c),c^p=(b,a)*(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a),c^p=(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a),c^p=(b,a)*(d,c),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [1..p-1] do
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a)*(d,c),c^p=(b,a)*(d,c)^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
count:=p+15;
//print count,p+15;
count1:=count;

//pa=0, pd=dc

for v in [1..p-2] do
for x in [0,1] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^v,c^p=(b,a)^x*(c,b)^y,d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p,c^p,d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p,c^p=(b,a),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a),c^p,d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a),c^p=(b,a),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p,c^p=(c,b),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a),c^p=(c,b),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1,c^p,d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1,c^p=(c,b),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1,c^p=(b,a),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1,c^p=(b,a)*(c,b),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1*(d,c),c^p,d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1*(d,c),c^p=(c,b),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1*(d,c),c^p=(b,a),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1*(d,c),c^p=(b,a)*(c,b),d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+14;
//print count-count1,4*p+6;
count1:=count;

//pa=0, pd=cb

for t in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a)*(c,b)*(d,c)^t,c^p=(b,a)*(d,c)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for t in [0..p-1] do
for x in [0,1] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)*(d,c)^t,c^p=(b,a)^x*(d,c)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
for t in [0,1,w] do
for x in [0,1] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(d,c)^t,c^p=(b,a)^x*(d,c)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
for t in [0,1,w] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a)*(d,c)^t,c^p=(d,c)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for t in [1,w] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a)*(d,c)^t,c^p=(b,a)*(d,c)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for y in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a),c^p=(b,a)*(d,c)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for t in [0..p-1] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(b,a)*(c,b)*(d,c)^t,c^p=(d,c)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;

//print count-count1,p^2+8*p+21;
count1:=count;

//pa=0, pd=ba

GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b),c^p,d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b),c^p=(d,c),d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b),c^p=(c,b),d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b),c^p=(c,b)*(d,c),d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+4;
for y in [0,1] do
for z in [0,1] do
for t in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(d,c)^y,c^p=(c,b)^z*(d,c)^t,d^p=(b,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;

//print count-count1,12;
count1:=count;

//pa=0, pd=ba+dc

for x in [0..p-1] do
for t in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^x,c^p=(d,c)^t,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [0,-1] do
for t in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^x*(d,c),c^p=(d,c)^t,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [0..p-1] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^x*(d,c)^y,c^p=(c,b),d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p,b^p=(c,b)^-1*(d,c)^y,c^p=(c,b)*(d,c),d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
//print count-count1,5*p+4;
count1:=count;

//pa=pd=dc

for x in [0,1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(b,a)^x*(c,b)^y,c^p=(c,b),d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for z in [0,1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(c,b)^y,c^p=(b,a)^z,d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for z in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(b,a),c^p=(b,a)^z,d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
//print count-count1,4*p+2;
count1:=count;

//pa=dc, pd=cb

for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(b,a)^x*(c,b),c^p=(b,a)^y*(d,c),d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;

for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(b,a)*(c,b),c^p=(b,a)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;

for y in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(c,b),c^p=(b,a)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;

for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(b,a),c^p=(b,a)^y*(d,c),d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;

for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p,c^p=(b,a)^y*(d,c),d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;

for x in [0,1] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(b,a)^x,c^p=(b,a)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;

if p mod 3 eq 1 then
for y in [w,w2] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(b,a),c^p=(b,a)^y,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end if;

//print count-count1,p^2+2*p+8+Gcd(p-1,3);
count1:=count;

//pa=dc, pd=ba

GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p,c^p,d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(c,b),c^p=(c,b)*(d,c),d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for y in [0..p-1] do
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(c,b),c^p=(c,b)^y,d^p=(b,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
count:=count+p+2;
//print count-count1,p+2;
count1:=count;

//pa=dc, pd=ba+dc

for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(c,b)^x,c^p=(c,b)^y,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  if ((1+x)*y) mod p eq 1 then
    count:=count+1;
    GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(d,c),b^p=(c,b)^x,c^p=(c,b)^y*(d,c),d^p=(b,a)*(d,c)>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end if;
end for;
end for;

//print count-count1,p^2+p-1;
count1:=count;

//pa=cb, pd=dc

for y in [0,1] do
for z in [0..p-1] do
for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a)*(d,c)^y,c^p=(b,a)^z*(c,b)^t,d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
for y in [0,1] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c)^y,c^p=(b,a)^z*(c,b),d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for y in [0,1] do
for z in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c)^y,c^p=(b,a)^z,d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;

//print count-count1,2*(p^2+p+3);
count1:=count;

//pa=pd=cb

GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p,c^p,d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p,c^p=(b,a),d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p,c^p=(b,a)^w,d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c),c^p=(b,a),d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c),c^p=(b,a)^w,d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c)^w,c^p=(b,a)^w,d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+6;
for y in [1,w] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c)^y,c^p=(b,a)^z*(d,c),d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for z in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p,c^p=(b,a)^z*(d,c),d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for t in [1..p-1] do
u:=(F!t)^-1;
u:=Integers()!u;
if t lt u then
for y in [1,w] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a)*(d,c)^y,c^p=(b,a)^z*(d,c)^t,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for z in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a),c^p=(b,a)^z*(d,c)^t,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end if;
end for;
for t in [1,-1] do
for z in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a)*(d,c),c^p=(b,a)^z*(d,c)^t,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for z in SQ do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a)*(d,c)^w,c^p=(b,a)^(w*z)*(d,c)^t,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for z in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a),c^p=(b,a)^z*(d,c)^t,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
//print count-count1,p^2+(7*p+15)/2;
count1:=count;

//pa=cb, pd=cb+dc

for y in [0..p-1] do
for z in [0..p-1] do
for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a)*(d,c)^y,c^p=(b,a)^z*(d,c)^t,d^p=(c,b)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
for y in [0..p-1] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c)^y,c^p=(b,a)^z*(d,c),d^p=(c,b)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for y in [0..p-1] do
for z in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c)^y,c^p=(b,a)^z,d^p=(c,b)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
//print count-count1,p^3+p^2+3*p;
count1:=count;

//pa=cb, pd=ba+dc

for y in [0..p-1] do
for z in [0..p-1] do
for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a)*(d,c)^y,c^p=(c,b)^z*(d,c)^t,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
for z in [0..p-1] do
for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(d,c),c^p=(c,b)^z*(d,c)^t,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p,c^p=(c,b)*(d,c)^t,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for t in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p,c^p=(d,c)^t,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
//print count-count1,p^3+p^2+p+3;
count1:=count;

//pa=cb, pd=ba+cb+dc

for x in [0..p-1] do
for y in [0..p-1] do
for z in [0..p-1] do
for t in [0..p-1] do
if x lt ((1+t) mod p) or (x eq ((1+t) mod p) and y le ((z+1) mod p)) then
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(c,b),b^p=(b,a)^x*(d,c)^y,c^p=(b,a)^z*(d,c)^t,d^p=(b,a)*(c,b)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
end for;
end for;
end for;
end for;

//print count-count1,(p^4+p^2)/2;
count1:=count;

//pa=ba, pd=dc

for x in [0..p-1] do
for t in [x..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a),b^p=(c,b)^x,c^p=(c,b)^t,d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a),b^p=(c,b)^x,c^p=(b,a)*(c,b)^-1,d^p=(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
count:=count+1;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a),b^p=(c,b)^-1*(d,c),c^p=(b,a)*(c,b)^-1,d^p=(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
//print count-count1,(p+2)*(p+1)/2;
count1:=count;

//pa=ba, pd=ba+dc

for x in [0..p-1] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a),b^p=(c,b)^x,c^p=(c,b)^z,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a),b^p=(c,b)^-1*(d,c),c^p=(c,b)^z,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in [0..p-2] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a),b^p=(c,b)^x,c^p=(c,b)^-1*(d,c),d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
//print count-count1,p^2+2*p-1;
count1:=count;

//pa=ba+dc, pd=ba+kdc (k ne 0)

for k in [1..p-1] do
for x in [0..p-1] do
for z in [0..p-1] do
if x le (k*z) mod p then
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a)*(d,c),b^p=(c,b)^x,c^p=(c,b)^z,d^p=(b,a)*(d,c)^k>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
end for;
end for;
end for;
//k=1
for x in [1..p-1] do
for z in [x..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a)*(d,c),b^p=(c,b)^x,c^p=(c,b)^z*(d,c),d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for z in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a)*(d,c),b^p=(d,c),c^p=(c,b)^z,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
count:=count+1;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a)*(d,c),b^p,c^p=(d,c),d^p=(b,a)*(d,c)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for t in [1..p-1] do
  u:=(F!t)^-1; u:=Integers()!u;
  if t le u then
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a)*(d,c),b^p=(d,c),c^p=(d,c)^t,d^p=(b,a)*(d,c)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end if;
end for;
//k ne 1
for k in [2..p-1] do
for x in [0..p-1] do
for z in [0..p-1] do
if x le (k*z) mod p and ((x+k)*(1+z)) mod p eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,b),a^p=(b,a)*(d,c),b^p=(c,b)^x,c^p=(c,b)^z*(d,c),d^p=(b,a)*(d,c)^k>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
end for;
end for;
end for;
//print count-count1,(p^3+2*p^2-p)/2;

vprint Orderp7, 2:"There are",count,"four generator p-class 2 groups satisfying";
vprint Orderp7, 2:"[c,a] = [d,a] = [d,b] = 1";

vprint Orderp7, 2: "Total number of groups is (p^4 + 5p^3 + 22p^2 + 77p + 171)/2 + gcd(p-1,3) =",
(p^4+5*p^3+22*p^2+77*p+171)/2+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;

Group4_13 := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//Descendants of 4.1 with L^2 of order p^3: Case 3
//Four generator p-class 2 groups satisfying [c,b]=[d,b]=[d,c]=1

limited := not Process and Limit ge 1;
class:=2;
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

for x in [1..p-1] do
  GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(b,a),c^p=(c,a),d^p=(d,a)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(b,a)*(c,a),c^p=(c,a),d^p=(d,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=p;
for x in [1..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(d,a)^x,c^p=(b,a)*(d,a)^y,d^p=(c,a)*(d,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [1..((p-1) div 2)] do
for y in [1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(d,a)^x,c^p=(b,a)*(d,a)^y,d^p=(c,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
count:=count+1;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(d,a),c^p=(b,a),d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(d,a)^w,c^p=(b,a),d^p=(c,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(d,a)^w2,c^p=(b,a),d^p=(c,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(c,a),c^p=(d,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(b,a),b^p=(c,a),c^p=(d,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(b,a),c^p=(d,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(c,a),b^p=(b,a),c^p=(d,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(b,a),c^p=(c,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(d,a),b^p=(b,a),c^p=(c,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+6;
for x in [1..p-1] do
  GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(c,a)^x,c^p=(b,a)*(c,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(d,a),b^p=(c,a)^x,c^p=(b,a)*(c,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(c,a),c^p=(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(d,a),b^p=(c,a),c^p=(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(c,a)^w,c^p=(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(d,a),b^p=(c,a)^w,c^p=(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(c,a),b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(b,a),b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(d,a),b^p=(c,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,b),(d,b),(d,c),a^p=(b,a),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+11;

vprint Orderp7, 2:"There are",count,"four generator p-class 2 groups satisfying";
vprint Orderp7, 2:"[c,b] = [d,b] = [d,c] = 1";

vprint Orderp7, 2: "Total number of groups is p^2 + 3p + 14 + gcd(p-1,3) =",
p^2+3*p+14+Gcd(p-1,3);

if Process then return Nmr; else return L; end if;

end function;

Group4_14 := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//Descendants of 4.1 with L^2 of order p^3: Case 4
//Four generator p-class 2 groups satisfying [c,a]=[d,a]=1, [d,c]=[b,a]

class:=2;
limited := not Process and Limit ge 1;

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
SQ:={};
for i in [0..((p-1) div 2)] do
  j:=i^2 mod p;
  Include(~SQ,j);
end for;
L:=[]; Nmr := 0;

GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(c,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(c,b),c^p=(b,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(d,b)^x,c^p=(b,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a),c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(d,b),c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p=(d,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a),c^p=(d,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a)^w,c^p=(d,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(c,b),c^p=(d,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=p+11;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(d,b)^x,c^p=(b,a),d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p=(b,a),d^p=(d,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(c,b),c^p=(b,a),d^p=(d,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p=(c,b),d^p=(d,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a),c^p=(c,b),d^p=(d,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p=(c,b)*(d,b),d^p=(d,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a),c^p=(c,b)*(d,b),d^p=(d,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a)^w,c^p=(c,b)*(d,b),d^p=(d,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+7;
for x in [1..p-1] do
if (4*x+1) mod p ne 0 then
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p=(d,b)^x,d^p=(c,b)*(d,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a),c^p=(d,b)^x,d^p=(c,b)*(d,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end if;
end for;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p=(d,b),d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a),c^p=(d,b),d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p,c^p=(d,b)^w,d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p,b^p=(b,a),c^p=(d,b)^w,d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p=(c,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+6;
for x in [1..p-1] do
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p=(c,b)^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p=(d,b),c^p=(c,b)^x,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p,d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p=(d,b),c^p,d^p=(c,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p=(c,b)^x,d^p=(d,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
count:=count+1;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p=(b,a)*(c,b)^-1,d^p=(d,b)^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [1..p-2] do
for y in [x+1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p=(c,b)^x,d^p=(d,b)^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [1..p-2] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p=(c,b)^x,d^p=(b,a)*(d,b)^-1>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p=(c,b)^x,d^p=(c,b)*(d,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
count:=count+1;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p=(b,a)*(c,b)^-1,d^p=(c,b)*(d,b)^-1>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [1..p-1] do
for y in [0..p-1] do
if (4*x+y^2) mod p notin SQ then
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(b,a),b^p,c^p=(d,b)^x,d^p=(c,b)*(d,b)^y>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
end for;
end for;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(d,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(d,b)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p,c^p,d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a),c^p,d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(d,b),c^p,d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(d,b)^w,c^p,d^p=(b,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+8;
for x in [0,1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)^x*(d,b)^y,c^p,d^p=(d,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [0..((p-1) div 2)] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(d,b)^y,c^p=(b,a),d^p=(d,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(d,b)^y,c^p=(b,a)^w,d^p=(d,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
end for;
for x in [0..((p-1) div 2)] do
  y:=(x^2+1) mod p; z:=(x^2+w) mod p;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)*(d,b)^y,c^p=(b,a),d^p=(d,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)*(d,b)^z,c^p=(b,a)^w,d^p=(d,b)^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
for x in [0..p-1] do
for z in [1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)^x*(d,b)^z,c^p=(d,b),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p,c^p=(d,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a),c^p=(d,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)^w,c^p=(d,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)^w2,c^p=(d,b),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)^w3,c^p=(d,b),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end if;
if p mod 3 eq 1 then
 for i in [2..p-2] do
  if i^3 mod p eq 1 then CU:=i; break; end if;
 end for;
 for k in [1,w,w2] do
 for x in [0..p-1] do
 for z in [0..p-1] do
  x1:=(CU*x) mod p; z1:=(CU*z) mod p; x2:=(CU*x1) mod p; z2:=(CU*z1) mod p;
  if (x lt x1 or (x eq x1 and z le z1)) and (x lt x2 or (x eq x2 and z le z2)) then
   count:=count+1;
   GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)^x*(d,b)^z,c^p=(d,b),d^p=(b,a)^k>;
   ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end if;
 end for;
 end for;
 end for;
else;
 for x in [0..p-1] do
 for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(d,a),(d,c)=(b,a),a^p=(c,b),b^p=(b,a)^x*(d,b)^z,c^p=(d,b),d^p=(b,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
 end for;
 end for;
end if;

vprint Orderp7, 2:"There are",count,"four generator p-class 2 groups satisfying";
vprint Orderp7, 2:"[c,a] = [d,a] = 1, [d,c] = [b,a]";

vprint Orderp7, 2: "Total number of groups is 3p^2 + 13p + 28 + gcd(p-1,3) + gcd(p-1,4) =",
3*p^2+13*p+28+Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;
// generic presentation here where seq records exponents 
// <a,b,c,d|(d,a),(c,b),(d,b)=(c,a),
//           a^p=(b,a)^s1*(c,a)^s2*(d,c)^s3,
//           b^p=(b,a)^s4*(c,a)^s5*(d,c)^s6,
//           c^p=(b,a)^s7*(c,a)^s8*(d,c)^s9,
//           d^p=(b,a)^s10*(c,a)^s11*(d,c)^s12>
//  where seq=[s1,s2,...,s12]. (Class is 2)

Group4_15 := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

/*
This program computes the orbits of the 4x3 matrices
needed for Case 5 in the descendants of 4.1 with
L^2 of order p^3.

Program written by Michael Vaughan-Lee in June 2003.

The orbit representatives appear in 11 commented out print
statements of the form "//print 0,0,1,0,1,0,y1,y2,y3,y4,y5,y6",
where the first 6 numbers run through 11 different possibilities.
You can modify these statements to save the representatives to
a file, or produce actual group presentations or whatever!
The index of each representative is stored in the variable
"count", which is updated in the line immediately above each
print statement.

For small primes it takes the following times (approximately)
on my PC running Magma in DOS to generate the orbit representatives.

           p=3: 550 reps in 2 seconds
           p=5: 4497 reps in 18 seconds
           p=7: 21019 reps in 112 seconds
           p=11: 181935 reps in 30 minutes
           p=13: 409909 reps in 81 minutes
           p=17: 1525053 reps in 6 hours and 16 minutes

We are considering four generator p-class 2 Lie rings, with 
generators a,b,c,d and commutator relations da=cb=0, db=ca.
The derived algebra has order p^3, and is generated by ba,ca,dc.
We have 4x3 matrices A over GF(p) with rows representing pa,pb,pc,pd
so that

         [pa] = A[ba]
         [pb]    [ca]
         [pc]    [dc]
         [pd]

We get the isomorphism classes of algebras satisfying these
commutator relations by considering the orbits of matrices A
under the action A -> BAC^-1 where

  B = [al,bl,bm,-am]
      [cl,dl,dm,-cm]
      [cn,dn,dx,-cx]
      [-an,-bn,-bx,ax]

  C =  (ad-bc)[l^2,2lm,m^2]
              [ln,lx+mn,mx]
              [n^2,2nx,x^2]

with ad-bc ne 0, lx-mn ne 0.

We get a complete set of orbit reps taking a=0,b=1 or a=1.
We ignore the factor (ad-bc) in C, as this makes no difference
to the orbits

The group G of these transformations has order (p+1)(p^2-1)(p^2-p)^2.
We consider the subgroup H of G consisting of elements with m=0.
H has index p+1 in G. The subspace spanned by a,b is invariant under the
action of H, and the pair (pa,pb) has 11 H-orbits. We compute 11
H-orbit representatives for (pa,pb), and for each distinct pair
(pa,pb) we store two pieces of information: (1) its orbit number, and
(2) an element of H which maps it to its orbit representative. [In
practice we only do this for pairs (pa,pb) such that the 2x3 matrix
representing (pa,pb) is in reduced row echelon form when read from the 
bottom up.]
We then (in effect) go on to compute the orbits of matrices A
under the action of H. Let the 11 H-orbit representatives for (pa,pb)
be v1,v2,...,v11. For each vi we compute the subgroup Ki of H which
fixes this vi, and compute the orbits of pc,pd under Ki. In practice, 
we do not actually compute the full orbits, but have a collection of 
functions which for any given vi and any given pc,pd compute the 
orbit representative for pc,pd under the action of Ki. (These are 
functions papb1, papb2 etc defined below.) Then for any given matrix
A we can compute its H-orbit representative as follows. First we look
at the first two rows which correspond to a pair (pa,pb). We then look
up the element h of H which maps (pa,pb) to one of the H-orbit
representatives v1,v2,...,v11, and apply h to A. This gives us a
matrix B whose first two rows correspond to vi (say). We then compute
the orbit representative for rows 3 and 4 of B under the action of Ki.
[In practice, given a matrix A we first apply an element of H which
puts its first two rows into reverse row echelon form. In other words,
we apply an element of H to obtain a matrix B with first two rows in 
row echelon form when read second row and then first row. This
ensures that the first two rows of B correspond to one of the pairs
(pa,pb) for which we have stored H-orbit information, and we can then 
look up the element h of H which maps the first two rows of B to an
H orbit representative vi.]

The G-orbit representatives for the matrices A form a subset of the
H-orbit representatives, and we compute the G-orbit representatives
as follows.

The H-orbit representatives for the matrices A form a sequence S of size
         p^6+2p^5+4p^4+8p^3+15p^2+29p+27+(2p+3)gcd(p-1,3)
We run through the elements of S in turn.
For each element A in S we apply the p+1 elements from a right
transversal for H in G. Let the images of A under the right transversal
be A,A1,A2,...,Ap. Let the H-orbit representatives of A,A1,A2,...,Ap
be A,B1,B2,...,Bp in S. Then A,B1,B2,...,Bp lie in the same G-orbit,
and the G-orbit of A is the union of the H-orbits of A,B1,B2,...,Bp.
We add A to the list of G-orbit representatives if A <= B1,B2,...,Bp
in the ordering on S.

The fact that the H-orbit representatives come in 11 H-invariant blocks
corresponding to v1,v2,...,v11 allows for huge shortcuts in the procedure
described above. Almost all the time is spent on determining whether
the elements Bi (defined 7 lines above) occur earlier or later than A
in S. In most cases we can do this without actually computing Bi.
Suppose that A lies in the block corresponding to vj, and suppose that
the image Ai of A under an element from our right transversal lies in
the block corresponding vk. Then Bi is earlier than A if k<j, and Bi
is later than A if k>j. So we only need to compute Bi when k=j.
*/

class:=2;
limited := not Process and Limit ge 1;

t:=Cputime();

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
vprint Orderp7, 2: "p equals",p;
vprint Orderp7, 2: "w equals",w;

L:=[]; Nmr := 0;

//Compute a transversal for the set of cubes
trancu:=[0,1];
if p mod 3 eq 1 then
  CU:={};
  for i in [1..p-1] do
    Include(~CU,i^3 mod p);
  end for;
  for i in [2..p-1] do
    if i notin CU then x:=i; break; end if;
  end for;
  Append(~trancu,x);
  S:=CU;
  for i in S do
    Include(~CU,(x*i) mod p);
  end for;
  for i in [x..p-1] do
    if i notin CU then y:=i; break; end if;
  end for;
  Append(~trancu,y);
end if;

p2:=p^2; p3:=p^3; p4:=p^4; p5:=p^5; p6:=p^6;

Z:=Integers();
V2:=VectorSpace(F,2);
V3:=VectorSpace(F,3);
V4:=VectorSpace(F,4);
H22:=Hom(V2,V2);
H23:=Hom(V2,V3);
H33:=Hom(V3,V3);
H43:=Hom(V4,V3);
H44:=Hom(V4,V4);

/*

Case 1 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,0]
                     [0,0,1]
and pc,pd represented by [u,v,w] with this equivalent to
                         [x,y,z]

           [t^3u-ctx,t^2v-cy,tw-t^-1cz]
           [atx,ay,at^-1z]
*/

//Function to compute index of orbit rep of pc,pd matrix

papb1:=function(p,F,Z,A)
y1:=Z!(A[1][1]); y2:=Z!(A[1][2]); y3:=Z!(A[1][3]);
y4:=Z!(A[2][1]); y5:=Z!(A[2][2]); y6:=Z!(A[2][3]); 

if y4 ne 0 then
  y5:=(F!y4)^-1*(F!y5); y5:=Z!y5;
  y6:=(F!y4)^-1*(F!y6); y6:=Z!y6;
  y2:=F!(y2-y1*y5); y2:=Z!(y2);
  y3:=F!(y3-y1*y6); y3:=Z!(y3);
  index:=p^4*y2+p^3*y3+p^2+p*y5+y6;
  for t in [2..p-1] do
    z2:=(t^2*y2) mod p; z3:=(t*y3) mod p;
    z5:=(F!t)^-1*(F!y5); z5:=Z!z5; z6:=(F!t)^-2*(F!y6); z6:=Z!z6;
    index:=Minimum(index,p^4*z2+p^3*z3+p^2+p*z5+z6);
  end for;
  return index;
end if;

if y4 eq 0 and y5 ne 0 then
  y6:=(F!y5)^-1*(F!y6); y6:=Z!y6; y3:=F!(y3-y2*y6); y3:=Z!y3;
  index:=p^5*y1+p^3*y3+p+y6;
  for t in [2..p-1] do
    z1:=(t^3*y1) mod p; z3:=(t*y3) mod p;
    z6:=(F!t)^-1*(F!y6); z6:=Z!z6;
    index:=Minimum(index,p^5*z1+p^3*z3+p+z6);
  end for;
  return index;
end if;

if y4 eq 0 and y5 eq 0 and y6 ne 0 then
  index:=p^5*y1+p^4*y2+1;
  for t in [2..p-1] do
    z1:=(t^3*y1) mod p; z2:=(t^2*y2) mod p;
    index:=Minimum(index,p^5*z1+p^4*z2+1);
  end for;
  return index;
end if;

if y4+y5+y6 eq 0 then
  index:=p^5*y1+p^4*y2+p^3*y3;
  for t in [2..p-1] do
    z1:=(t^3*y1) mod p; z2:=(t^2*y2) mod p; z3:=(t*y3) mod p;
    index:=Minimum(index,p^5*z1+p^4*z2+p^3*z3);
  end for;
  return index;
end if;

end function;

/*

Case 2 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,0]
                     [0,1,0]
and pc,pd represented by [u,v,w] with this equivalent to
                         [x,y,z]

           [t^2u-ctx,tv-cy,w-t^-1cz]
           [atx,ay,at^-1z]
*/

//Function to compute index of orbit rep of pc,pd matrix

papb2:=function(p,F,Z,A)
y1:=Z!(A[1][1]); y2:=Z!(A[1][2]); y3:=Z!(A[1][3]);
y4:=Z!(A[2][1]); y5:=Z!(A[2][2]); y6:=Z!(A[2][3]); 

if y4 ne 0 then
  y5:=(F!y4)^-1*(F!y5); y5:=Z!y5;
  y6:=(F!y4)^-1*(F!y6); y6:=Z!y6;
  y2:=F!(y2-y1*y5); y2:=Z!(y2);
  y3:=F!(y3-y1*y6); y3:=Z!(y3);
  index:=p^4*y2+p^3*y3+p^2+p*y5+y6;
  for t in [2..p-1] do
    z2:=(t*y2) mod p; z3:=y3;
    z5:=(F!t)^-1*(F!y5); z5:=Z!z5; z6:=(F!t)^-2*(F!y6); z6:=Z!z6;
    index:=Minimum(index,p^4*z2+p^3*z3+p^2+p*z5+z6);
  end for;
  return index;
end if;

if y4 eq 0 and y5 ne 0 then
  y6:=(F!y5)^-1*(F!y6); y6:=Z!y6; y3:=F!(y3-y2*y6); y3:=Z!y3;
  index:=p^5*y1+p^3*y3+p+y6;
  for t in [2..p-1] do
    z1:=(t^2*y1) mod p; z3:=y3;
    z6:=(F!t)^-1*(F!y6); z6:=Z!z6;
    index:=Minimum(index,p^5*z1+p^3*z3+p+z6);
  end for;
  return index;
end if;

if y4 eq 0 and y5 eq 0 and y6 ne 0 then
  index:=p^5*y1+p^4*y2+1;
  for t in [2..p-1] do
    z1:=(t^2*y1) mod p; z2:=(t*y2) mod p;
    index:=Minimum(index,p^5*z1+p^4*z2+1);
  end for;
  return index;
end if;

if y4+y5+y6 eq 0 then
  index:=p^5*y1+p^4*y2+p^3*y3;
  for t in [2..p-1] do
    z1:=(t^2*y1) mod p; z2:=(t*y2) mod p; z3:=y3;
    index:=Minimum(index,p^5*z1+p^4*z2+p^3*z3);
  end for;
  return index;
end if;

end function;

/*

Case 3 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,0]
                     [0,1,1]
and pc,pd represented by [u,v,w] with this equivalent to
                         [x,y,z]

         [u-cx,v-cy,w-cz]
         [ax,ay,az]

or

         [-u+cx+v-cy-w+cz,-1+v-cy-2w+2cz,-1-w+cz]
         [-ax+ay-az,ay-2az,-az]
*/

//Function to compute index of orbit rep of pc,pd matrix

papb3:=function(p,F,Z,A)
y1:=Z!(A[1][1]); y2:=Z!(A[1][2]); y3:=Z!(A[1][3]);
y4:=Z!(A[2][1]); y5:=Z!(A[2][2]); y6:=Z!(A[2][3]); 

if y4 ne 0 then
  y5:=(F!y4)^-1*(F!y5); y5:=Z!y5;
  y6:=(F!y4)^-1*(F!y6); y6:=Z!y6;
  y2:=F!(y2-y1*y5); y2:=Z!(y2);
  y3:=F!(y3-y1*y6); y3:=Z!(y3);
  index:=p^4*y2+p^3*y3+p^2+p*y5+y6;
  return index;
end if;

if y4 eq 0 and y5 ne 0 then
  y6:=(F!y5)^-1*(F!y6); y6:=Z!y6; y3:=F!(y3-y2*y6); y3:=Z!y3;
  index:=p^5*y1+p^3*y3+p+y6;
  return index;
end if;

if y4 eq 0 and y5 eq 0 and y6 ne 0 then
  index:=p^5*y1+p^4*y2+1;
  return index;
end if;

if y4+y5+y6 eq 0 then
  index:=p^5*y1+p^4*y2+p^3*y3;
  return index;
end if;

end function;

/*

Case 4 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,0]
                     [1,0,0]
and pb,pc,pd represented by [1,0,0]
                            [u,v,w]
                            [x,y,z]

This 3x3 matrix is equivalent to what you get by premultipling by
         [1,0,0]
         [n,t,-ct]
         [0,0,at]

and post multiplying by the inverse of [1,0,0]
                                       [n,t,0]
                                       [n^2,2nt,t^2]
(Here a,t ne 0)

Replacing n by nt we have
    [t(n+u-nv+n^2w-c(x-ny+n^2z)),v-2nw-c(y-2nz),t^-1(w-cz)]
    [at(x-ny+n^2z),a(y-2nz),at^-1z]
*/

//Function to compute index of orbit rep of pc,pd matrix

papb4:=function(p,F,Z,A)
y1:=Z!(A[1][1]); y2:=Z!(A[1][2]); y3:=Z!(A[1][3]);
y4:=Z!(A[2][1]); y5:=Z!(A[2][2]); y6:=Z!(A[2][3]); 

index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

if y4+y5+y6 eq 0 then
 for n in [0..p-1] do
  z1:=F!(n+y1-n*y2+n^2*y3);
  z2:=F!(y2-2*n*y3);
  z3:=F!y3;
  if z1 ne 0 then
    z3:=z1*z3; z1:=1;
  else;
    if z3 ne 0 then z3:=1; end if;
  end if;
  z1:=Z!z1; z2:=Z!z2; z3:=Z!z3;
  ind1:=p^5*z1+p^4*z2+p^3*z3;
  index:=Minimum(index,ind1);
 end for;
else;
 for n in [0..p-1] do
  z1:=F!(n+y1-n*y2+n^2*y3);
  z4:=F!(y4-n*y5+n^2*y6);
  if z1 ne 0 and z4 eq 0 then continue; end if;
  z2:=F!(y2-2*n*y3);
  z3:=F!y3;
  z5:=F!(y5-2*n*y6);
  z6:=F!y6;
  if z4 ne 0 then
    z5:=z4^-1*z5; z6:=z4^-1*z6; z4:=1;
    z2:=z2-z1*z5; z3:=z3-z1*z6; z1:=0;
    if z3 ne 0 then
      z5:=z3^-1*z5; z6:=z3^-2*z6; z3:=1;
    end if;
    if z3 eq 0 and z5 ne 0 then
      z6:=z5^-2*z6; z5:=1;
    end if;
    if z3 eq 0 and z5 eq 0 and z6 ne 0 then
      t6:=Z!z6; min:=t6;
      for t in [2..((p-1) div 2)] do
        min:=Minimum(min,(t^2*t6) mod p);
      end for;
      z6:=min;
    end if;
  end if;
  if z4 eq 0 and z5 ne 0 then
    z6:=z5^-1*z6; z5:=1;
    z3:=z3-z2*z6; z2:=0;
    if z3 ne 0 then
      z6:=z3^-1*z6; z3:=1;
    end if;
    if z3 eq 0 and z6 ne 0 then
      z6:=1;
    end if;
  end if;
  if z4 eq 0 and z5 eq 0 and z6 ne 0 then
    z6:=1; z3:=0;
  end if;
  z1:=Z!z1; z2:=Z!z2; z3:=Z!z3; z4:=Z!z4; z5:=Z!z5; z6:=Z!z6;
  ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;
  index:=Minimum(index,ind1);
 end for;
end if;

return index;

end function;


/*
Case 5 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,0] where k=1 if p ne 1 mod 4,
                     [1,0,k]
and k is the least non-square if p = 1 mod 4.
and pc,pd represented by [u,v,w] with this equivalent to
                         [x,y,z]

         [u-cx,v-cy,w-cz]
         [ax,ay,az]

or

         [-u+cx,v-cy,-w+cz]
         [-ax,ay,-az]
        
*/

//Function to compute index of orbit rep of pc,pd matrix
//function papb3 will do for papb5

/*

Case 6 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,1],
                     [0,1,0]
and pc,pd represented by [u,v,w] with this equivalent to [a^2u,av,w]
                         [x,y,z]                         [a^3x,a^2y,az]
*/

//Function to compute index of orbit rep of pc,pd matrix

papb6:=function(p,F,Z,A)
y1:=Z!(A[1][1]); y2:=Z!(A[1][2]); y3:=Z!(A[1][3]);
y4:=Z!(A[2][1]); y5:=Z!(A[2][2]); y6:=Z!(A[2][3]); 

index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [2..p-1] do
  z1:=(a^2*y1) mod p;
  z2:=(a*y2) mod p;
  z3:=y3;
  z4:=(a^3*y4) mod p;
  z5:=(a^2*y5) mod p;
  z6:=(a*y6) mod p;
  ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;
  index:=Minimum(index,ind1);
end for;

return index;

end function;


/*

Case 7 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,1],
                     [1,0,0]
and pc,pd represented by [u,v,w] with this equivalent to [au,v,a^-1w]
                         [x,y,z]                         [a^3x,a^2y,az]
*/

//Function to compute index of orbit rep of pc,pd matrix

papb7:=function(p,F,Z,A)
y1:=Z!(A[1][1]); y2:=Z!(A[1][2]); y3:=Z!(A[1][3]);
y4:=Z!(A[2][1]); y5:=Z!(A[2][2]); y6:=Z!(A[2][3]); 

index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

for a in [2..p-1] do
  z1:=(a*y1) mod p;
  z2:=y2;
  z3:=(F!a)^-1*(F!y3); z3:=Z!z3;
  z4:=(a^3*y4) mod p;
  z5:=(a^2*y5) mod p;
  z6:=(a*y6) mod p;
  ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;
  index:=Minimum(index,ind1);
end for;

return index;

end function;


/*

Case 8 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,1],
                     [1,1,0]
and pc,pd represented by [u,v,w] with this equivalent to
                         [x,y,z]

  [-2+u-2v+4w,-2-v+4w,w]
  [4u-x-8v+2y+16w-4z,-4v+y+16w-4z,2+4w-z]
*/


/*

Case 9 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,0,0]
                     [1,0,0]
and pa,pb,pc,pd represented by [0,1,0]
                               [1,0,0]
                               [u,v,w]
                               [x,y,z]

This 4x4 matrix is equivalent to what you get by premultipling by
        
         [t,n,0,0]
         [0,1,0,0]
         [0,n,t,0]
         [-nt,-n^2,-nt,t^2]

and post multiplying by the inverse of [1,0,0]
                                       [n,t,0]
                                       [n^2,2nt,t^2]
(Here t ne 0)

Replacing n by nt we get [t(n+u-vn+wn^2),v-2wn,t^-1w]
          [t^2(-nu+x+n^2v-ny-n^3w+n^2z),-t(n+nv-y-2wn^2+2nz),-wn+z]
*/

//Function to compute index of orbit rep of pc,pd matrix

papb9:=function(p,F,Z,A)
y1:=Z!(A[1][1]); y2:=Z!(A[1][2]); y3:=Z!(A[1][3]);
y4:=Z!(A[2][1]); y5:=Z!(A[2][2]); y6:=Z!(A[2][3]); 

index:=p^5*y1+p^4*y2+p^3*y3+p^2*y4+p*y5+y6;

//Try to get u=0.
nus:={};
for n in [0..p-1] do
  if F!(n+y1-y2*n+y3*n^2) eq 0 then Include(~nus,n); end if;
end for;
if IsEmpty(nus) then
  //Can't get u=0, so choose t so that u=1
  range:=[i:i in [0..p-1]];
  if y3 ne 0 then n:=(F!(2*y3))^-1*(F!y2); n:=Z!n; range:=[n]; end if;
  for n in range do
    t:=(F!(n+y1-y2*n+y3*n^2))^-1; t:=Z!t;
    z1:=1;
    z2:=F!(y2-2*y3*n); z2:=Z!z2;
    z3:=(F!t)^-1*(F!y3); z3:=Z!z3;
    z4:=F!(t^2*(-n*y1+y4+n^2*y2-n*y5-n^3*y3+n^2*y6)); z4:=Z!z4;
    z5:=F!(-t*(n+n*y2-y5-2*y3*n^2+2*n*y6)); z5:=Z!z5;
    z6:=F!(-y3*n+y6); z6:=Z!z6;
    ind1:=p^5*z1+p^4*z2+p^3*z3+p^2*z4+p*z5+z6;
    index:=Minimum(index,ind1);
  end for;
else;
  //Have some values of n which give u=0.
  range:=[i:i in [1..p-1]];
  if y3 ne 0 then range:=[y3]; end if;
  for n in nus do
  for t in range do
    z2:=F!(y2-2*y3*n); z2:=Z!z2;
    z3:=(F!t)^-1*(F!y3); z3:=Z!z3;
    z4:=F!(t^2*(-n*y1+y4+n^2*y2-n*y5-n^3*y3+n^2*y6)); z4:=Z!z4;
    z5:=F!(-t*(n+n*y2-y5-2*y3*n^2+2*n*y6)); z5:=Z!z5;
    z6:=F!(-y3*n+y6); z6:=Z!z6;
    ind1:=p^4*z2+p^3*z3+p^2*z4+p*z5+z6;
    index:=Minimum(index,ind1);
  end for;
  end for;
end if;

return index;

end function;

/*

Case 10 in the non-zero orbits of pa,pb in case 5
of the descendants of 4.1

pa,pb represented by [0,1,0] where k is the least non-square,
                     [1,0,k]
and pc,pd represented by [u,v,w] with this equivalent to [-u,v,-w]
                         [x,y,z]                         [x,-y,z]
*/

/*
Work out orbits of pa,pb under the subgroup H with m=0.

Represent pa,pb by 2x3 matrix A = [y1,y2,y3]
                                  [y4,y5,y6]

The group H sends A -> BAC^-1 where B = [a,b] and C = [1,  0,  0]
                                        [c,d]         [n,  x,  0]
                                                      [n^2,2*n*x,x^2]

We only need matrices [y1,y2,y3] with [y4,y5,y6] in echelon form
                      [y4,y5,y6]      [y1,y2,y3]
since whatever the value of AC^-1 we can always choose B so that
BAC^-1 is in echelon form when read from the bottom up - call this
reverse echelon form.

For each pair (pa,pb) with matrix A in reverse echelon form
we store the orbit number of A in orb0, and we store the group element 
which maps A to its orbit rep in norm.  Store this group element as
a sequence [a,b,c,d,n,x] with l=1, m=0.

This computation also gives the orbits for pc,pd when pa=pb=0
*/


//We already know the 11 orbit representatives!
//Set up mats to hold them.
SQ:={};
for i in [1..((p-1) div 2)] do
  Include(~SQ,i^2 mod p);
end for;
for i in [2..p-1] do
  if i notin SQ then ns:=i; break; end if;
end for;

if p mod 4 eq 3 then
  mns:=1;
else;
  mns:=ns;
end if;

//These are the 11 H-orbit representatives for 2x3
//matrices representing pa,pb.
A1:=H23![0,0,0,0,0,0];
A2:=H23![0,0,0,0,0,1];
A3:=H23![0,0,0,0,1,0];
A4:=H23![0,0,0,0,1,1];
A5:=H23![0,0,0,1,0,0];
A6:=H23![0,0,0,1,0,mns];
A7:=H23![0,0,1,0,1,0];
A8:=H23![0,0,1,1,0,0];
A9:=H23![0,0,1,1,1,0];
A10:=H23![0,1,0,1,0,0];
A11:=H23![0,1,0,1,0,ns];

mats:=[A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11];
orb0:=[];
norm:=[];

//Identity group element
I:=[1,0,0,1,0,1];

//This variable keeps track of number of G-orbit representatives
count:=0;

y1:=0;
for y2 in [0,1] do
for y3 in [0..p-1] do
for y4 in [0,1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
index:=p4*y2+p3*y3+p2*y4+p*y5+y6;
A:=H23![y1,y2,y3,y4,y5,y6];

if A in mats then
  count:=count+1;
  //print 0,0,0,0,0,0,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p, b^p,
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  orb0[index+1]:=count;
  norm[index+1]:=I;
  continue;
end if;

//We only need to deal with A in reverse row echelon form
E:=EchelonForm(A);
if E[1] ne A[2] or E[2] ne A[1] then continue; end if;

for n in [0..p-1] do
for x in [1..p-1] do

C:=H33![1,0,0,n,x,0,n^2,2*n*x,x^2];
D:=A*C^-1;
E,g:=EchelonForm(D);

z2:=Z!(E[2][2]);
z3:=Z!(E[2][3]);
z4:=Z!(E[1][1]);
z5:=Z!(E[1][2]);
z6:=Z!(E[1][3]);

ind1:=p4*z2+p3*z3+p2*z4+p*z5+z6;

if ind1 lt index then
  new:=0;
  orb0[index+1]:=orb0[ind1+1];
  //get a,b,c,d,n,x
  a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
  B1:=H22![a,b,c,d];
  C1:=H22![1,0,n,x];
  g:=norm[ind1+1];
  B2:=H22![g[1],g[2],g[3],g[4]];
  C2:=H22![1,0,g[5],g[6]];
  B:=B2*B1; C:=C2*C1;
  g:=[Z!(B[1][1]),Z!(B[1][2]),Z!(B[2][1]),Z!(B[2][2]),Z!(C[2][1]),Z!(C[2][2])];
  norm[index+1]:=g;
  //norm now stores element in H which maps A to its H-orbit representative.
end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[2];

papb:=2;
M:=mats[2];

for y1 in trancu do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0,1] do
if y1 ne 0 and y4 eq 1 then continue; end if;
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if A eq 0 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

//Check if (for this pa,pb) the pc,pd given by A correspond
//to an H-orbit representative: if not go on to next A
if papb1(p,F,Z,A) lt index then continue; end if;

AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];
//AB is a 4x3 matrix representing pa,pb,pc,pd for some
//H-orbit representative.

//Hit AB with a transversal in G for the subgroup H

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb1(p,F,Z,E) lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; break; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb1(p,F,Z,E) lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,0,0,0,0,1,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p, b^p=(d,c),
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[3];

papb:=3;
M:=mats[3];

for y1 in [0,1,ns] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0,1] do
if y1 ne 0 and y4 eq 1 then continue; end if;
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if A eq 0 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

if papb2(p,F,Z,A) lt index then continue; end if;

AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb2(p,F,Z,E) lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; break; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb2(p,F,Z,E) lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,0,0,0,1,0,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p, b^p=(c,a),
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[4];

papb:=4;
M:=mats[4];

for y1 in [0..p-1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0,1] do
if y1 ne 0 and y4 eq 1 then continue; end if;
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if A eq 0 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

if papb3(p,F,Z,A) lt index then continue; end if;
A2:=H23![-y1+y2-y3,-1+y2-2*y3,-1-y3,-y4+y5-y6,y5-2*y6,-y6];
if papb3(p,F,Z,A2) lt index then continue; end if;


AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb3(p,F,Z,E) lt index then new:=0; end if;
      E2:=E;
      E2[1][1]:=-E[1][1]+E[1][2]-E[1][3];
      E2[1][2]:=-1+E[1][2]-2*E[1][3];
      E2[1][3]:=-1-E[1][3];
      E2[2][1]:=-E[2][1]+E[2][2]-E[2][3];
      E2[2][2]:=E[2][2]-2*E[2][3];
      E2[2][3]:=-E[2][3];
      if papb3(p,F,Z,E2) lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; break; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb3(p,F,Z,E) lt index then new:=0; break; end if;
      E2:=E;
      E2[1][1]:=-E[1][1]+E[1][2]-E[1][3];
      E2[1][2]:=-1+E[1][2]-2*E[1][3];
      E2[1][3]:=-1-E[1][3];
      E2[2][1]:=-E[2][1]+E[2][2]-E[2][3];
      E2[2][2]:=E[2][2]-2*E[2][3];
      E2[2][3]:=-E[2][3];
      if papb3(p,F,Z,E2) lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,0,0,0,1,1,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p, b^p=(c,a)*(d,c),
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[5];

papb:=5;
M:=mats[5];

for y1 in [0,1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0,1] do
if y1 ne 0 and y4 ne 0 then continue; end if;
for y5 in [0..p-1] do
if y1 ne 0 and y5 ne 0 then continue; end if;
for y6 in [0..p-1] do
if y1 ne 0 and y6 ne 0 then continue; end if;

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if A eq 0 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

if papb4(p,F,Z,A) lt index then continue; end if;

AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb4(p,F,Z,E) lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; break; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb4(p,F,Z,E) lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,0,0,1,0,0,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p, b^p=(b,a),
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[6];

papb:=6;
M:=mats[6];

for y1 in [0..((p-1) div 2)] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0,1] do
if y1 ne 0 and y4 eq 1 then continue; end if;
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if A eq 0 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

if papb3(p,F,Z,A) lt index then continue; end if;
A2:=H23![-y1,y2,-y3,-y4,y5,-y6];
if papb3(p,F,Z,A2) lt index then continue; end if;


AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb3(p,F,Z,E) lt index then new:=0; end if;
      E2:=E;
      E2[1][1]:=-E[1][1];
      E2[1][3]:=-E[1][3];
      E2[2][1]:=-E[2][1];
      E2[2][3]:=-E[2][3];
      if papb3(p,F,Z,E2) lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if E eq 0 then new:=0; break; end if;
  if Rank(E) eq 1 then
    E,g:=EchelonForm(E);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb3(p,F,Z,E) lt index then new:=0; break; end if;
      E2:=E;
      E2[1][1]:=-E[1][1];
      E2[1][3]:=-E[1][3];
      E2[2][1]:=-E[2][1];
      E2[2][3]:=-E[2][3];
      if papb3(p,F,Z,E2) lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,0,0,1,0,mns,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p, b^p=(b,a)*(d,c)^mns,
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[7];

papb:=7;
M:=mats[7];

for y1 in [0,1,ns] do
for y2 in [0..((p-1) div 2)] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if Rank(A) lt 2 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

if papb6(p,F,Z,A) lt index then continue; end if;

AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb6(p,F,Z,E) lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; break; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb6(p,F,Z,E) lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,0,1,0,1,0,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p=(d,c), b^p=(c,a),
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[8];

papb:=8;
M:=mats[8];

for y1 in [0,1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
if y1 eq 0 and y3 gt 1 then continue; end if;
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if Rank(A) lt 2 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

if papb7(p,F,Z,A) lt index then continue; end if;

AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb7(p,F,Z,E) lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; break; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb7(p,F,Z,E) lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,0,1,1,0,0,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p=(d,c), b^p=(b,a),
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[9];

papb:=9;
M:=mats[9];

for y1 in [0..p-1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
z1:=F!(-2+y1-2*y2+4*y3); z1:=Z!z1;
z2:=F!(-2-y2+4*y3); z2:=Z!z2;
if p*z1+z2 lt p*y1+y2 then continue; end if;
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if Rank(A) lt 2 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

z1:=F!(-2+y1-2*y2+4*y3); z1:=Z!z1;
z2:=F!(-2-y2+4*y3); z2:=Z!z2;
z4:=F!(4*y1-y4-8*y2+2*y5+16*y3-4*y6); z4:=Z!z4;
z5:=F!(-4*y2+y5+16*y3-4*y6); z5:=Z!z5;
z6:=F!(2+4*y3-y6); z6:=Z!z6;

if p5*z1+p4*z2+p3*y3+p2*z4+p*z5+z6 lt index then continue; end if;

AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      t1:=Z!(D[3][1]); t2:=Z!(D[3][2]); t3:=Z!(D[3][3]);
      t4:=Z!(D[4][1]); t5:=Z!(D[4][2]); t6:=Z!(D[4][3]);
      ind2:=p5*t1+p4*t2+p3*t3+p2*t4+p*t5+t6;
      if ind2 lt index then new:=0; end if;
      z1:=F!(-2+t1-2*t2+4*t3); z1:=Z!z1;
      z2:=F!(-2-t2+4*t3); z2:=Z!z2;
      z4:=F!(4*t1-t4-8*t2+2*t5+16*t3-4*t6); z4:=Z!z4;
      z5:=F!(-4*t2+t5+16*t3-4*t6); z5:=Z!z5;
      z6:=F!(2+4*t3-t6); z6:=Z!z6;
      ind2:=p5*z1+p4*z2+p3*t3+p2*z4+p*z5+z6;
      if ind2 lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; break; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      t1:=Z!(D[3][1]); t2:=Z!(D[3][2]); t3:=Z!(D[3][3]);
      t4:=Z!(D[4][1]); t5:=Z!(D[4][2]); t6:=Z!(D[4][3]);
      ind2:=p5*t1+p4*t2+p3*t3+p2*t4+p*t5+t6;
      if ind2 lt index then new:=0; break; end if;
      z1:=F!(-2+t1-2*t2+4*t3); z1:=Z!z1;
      z2:=F!(-2-t2+4*t3); z2:=Z!z2;
      z4:=F!(4*t1-t4-8*t2+2*t5+16*t3-4*t6); z4:=Z!z4;
      z5:=F!(-4*t2+t5+16*t3-4*t6); z5:=Z!z5;
      z6:=F!(2+4*t3-t6); z6:=Z!z6;
      ind2:=p5*z1+p4*z2+p3*t3+p2*z4+p*z5+z6;
      if ind2 lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,0,1,1,1,0,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p=(d,c), b^p=(b,a)*(c,a),
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[10];

papb:=10;
M:=mats[10];

for y1 in [0,1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
if y1 eq 0 and y3 gt 1 then continue; end if;
for y4 in [0..p-1] do
for y5 in [0..p-1] do
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if Rank(A) lt 2 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

if papb9(p,F,Z,A) lt index then continue; end if;

AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb9(p,F,Z,E) lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; break; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      E[1]:=D[3]; E[2]:=D[4];
      if papb9(p,F,Z,E) lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,1,0,1,0,0,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p=(c,a), b^p=(b,a),
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

//print count;
//print Cputime(t);

//Get orbits with pa,pb given by mats[11];

papb:=11;
M:=mats[11];

for y1 in [0..((p-1) div 2)] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
if y1 eq 0 and y3 gt ((p-1) div 2) then continue; end if;
for y4 in [0..p-1] do
for y5 in [0..p-1] do
if y1+y3 eq 0 and y5 gt ((p-1) div 2) then continue; end if;
for y6 in [0..p-1] do

new:=1;
A:=H23![y1,y2,y3,y4,y5,y6];
if Rank(A) lt 2 then continue; end if;
index:=p5*y1+p4*y2+p3*y3+p2*y4+p*y5+y6;

AB:=H43!0;
AB[1]:=M[1]; AB[2]:=M[2]; AB[3]:=A[1]; AB[4]:=A[2];

//We have an orbit rep for the orbits under m=0 subgroup
//Hit it with a transversal for m=0 subgroup

  //First element of transversal
  B:=H44![0,0,0,-1,
          0,0,1,0,
          0,1,0,0,
          -1,0,0,0];

  C:=H33![0,0,1,
          0,1,0,
          1,0,0];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      t1:=Z!(D[3][1]); t2:=Z!(D[3][2]); t3:=Z!(D[3][3]);
      t4:=Z!(D[4][1]); t5:=Z!(D[4][2]); t6:=Z!(D[4][3]);
      ind2:=p5*t1+p4*t2+p3*t3+p2*t4+p*t5+t6;
      if ind2 lt index then new:=0; end if;
      z1:=(p-t1) mod p; z3:=(p-t3) mod p; z5:=(p-t5) mod p;
      ind2:=p5*z1+p4*t2+p3*z3+p2*t4+p*z5+t6;
      if ind2 lt index then new:=0; end if;
    end if;
  end if;

  //Now hit with rest of transversal for m=0 subgroup
if new eq 1 then
 for m1 in [1..p-1] do
  B:=H44![1,0,0,-m1,
          0,1,m1,0,
          0,0,1,0,
          0,0,0,1];

  C:=H33![1,2*m1,m1^2,
          0,1,m1,
          0,0,1];

  D:=B*AB*C^-1;
  //Get index for first two rows of D
  E:=H23!0; E[1]:=D[1]; E[2]:=D[2];
  if Rank(E) le 1 then new:=0; break; end if;
  if Rank(E) eq 2 then
    E,g:=EchelonForm(E);
    z1:=Z!(E[2][1]); z2:=Z!(E[2][2]); z3:=Z!(E[2][3]);
    z4:=Z!(E[1][1]); z5:=Z!(E[1][2]); z6:=Z!(E[1][3]);
    ind1:=p5*z1+p4*z2+p3*z3+p2*z4+p*z5+z6;
    orb:=orb0[ind1+1];
    if orb lt papb then new:=0; break; end if;
    if orb eq papb then
      //Apply g to D to get first two rows in reverse echelon form
      a:=g[2][1]; b:=g[2][2]; c:=g[1][1]; d:=g[1][2];
      B:=H44![a,b,0,0,
              c,d,0,0,
              0,0,d,-c,
              0,0,-b,a];
      D:=B*D;
      //Now apply normalizing element to D
      g:=norm[ind1+1];
      a:=g[1]; b:=g[2]; c:=g[3]; d:=g[4]; n:=g[5]; x:=g[6];
      B:=H44![a,b,0,0,
              c,d,0,0,
              c*n,d*n,d*x,-c*x,
              -a*n,-b*n,-b*x,a*x];

      C:=H33![1,0,0,
              n,x,0,
              n^2,2*n*x,x^2];

      D:=B*D*C^-1;
      //Get index for last two rows of D
      t1:=Z!(D[3][1]); t2:=Z!(D[3][2]); t3:=Z!(D[3][3]);
      t4:=Z!(D[4][1]); t5:=Z!(D[4][2]); t6:=Z!(D[4][3]);
      ind2:=p5*t1+p4*t2+p3*t3+p2*t4+p*t5+t6;
      if ind2 lt index then new:=0; break; end if;
      z1:=(p-t1) mod p; z3:=(p-t3) mod p; z5:=(p-t5) mod p;
      ind2:=p5*z1+p4*t2+p3*z3+p2*t4+p*z5+t6;
      if ind2 lt index then new:=0; break; end if;
    end if;
  end if;
 end for;
end if;

if new eq 1 then
  count:=count+1;
  //print 0,1,0,1,0,ns,y1,y2,y3,y4,y5,y6;
  GR:=Group<a,b,c,d|(d,a),(c,b),(d,b)=(c,a), a^p=(c,a), b^p=(b,a)*(d,c)^ns,
                     c^p=(b,a)^y1*(c,a)^y2*(d,c)^y3,
                     d^p=(b,a)^y4*(c,a)^y5*(d,c)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;
end for;
end for;

vprint Orderp7, 2: "The number of orbits is",count;

if p eq 3 then 
   vprint Orderp7, 2: "Total number of groups is ", 550; 
elif p mod 3 eq 1 then 
   vprint Orderp7, 2: "Total number of groups is p^5+p^4+4p^3+6p^2+18p+19 = ",  
       p^5+p^4+4*p^3+6*p^2+18*p+19; 
elif p mod 3 eq 2 then 
   vprint Orderp7, 2: "Total number of groups is p^5+p^4+4p^3+6p^2+16p+17 = ",  
       p^5+p^4+4*p^3+6*p^2+16*p+17; 
end if;

// "Cputime to setup is ", Cputime(t);

if Process then return Nmr; else return L; end if;

end function;

Group4_16 := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//This program computes presentations for groups from
//Case 6 in the descendants of 4.1 with L^2 of order p^3.
// [d,a]=0, [d,b]=[c,a]^w, [d,c]=[b,a]

class:=2;
limited := not Process and Limit ge 1;

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
vprint Orderp7, 2: "p equals",p;
vprint Orderp7, 2: "w equals",w;

Z:=Integers();
V2:=VectorSpace(F,2);
V3:=VectorSpace(F,3);
V4:=VectorSpace(F,4);
H22:=Hom(V2,V2);
H43:=Hom(V4,V3);
H33:=Hom(V3,V3);
H44:=Hom(V4,V4);

range:={[0,1]};
for i in [0..p-1] do
  Include(~range,[1,i]);
end for;

L:=[]; Nmr := 0;
count:=0;
pow416:={};

//Get pb,pc when pa=pd=0.

//If pb,pc notin <ba,ca> then we can assume that
//pc=cb and pb=0 or ca
GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),a^p,b^p,c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),a^p,b^p=(c,a),c^p=(c,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=2;

//Get pb,pc when pa=pd=0 and pb,pc in <ba,ca>
//Can assume that pb=0 or ca
y1:=0;
for y2 in [0..1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A:=H22![y1,y2,y3,y4];

for a in [0..p-1] do
for d in [0..p-1] do
if a+d ne 0 then
for r in range do
b:=r[1];
c:=r[2];

B:=H22![c,w*b,b,c];
C:=H22![a*c-w*b*d,w*a*b-w*c*d,
        a*b-c*d,a*c-w*b*d];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

B[1]:=-B[1];
C[1]:=-C[1];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;

end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),a^p,b^p=(c,a)^y2,c^p=(b,a)^y3*(c,a)^y4,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;

//vprint Orderp7, 2: count,p+4;
//count1:=count;

//Get pb,pc when pa=0, pd=ca

for z in [1..((p-1) div 2)] do
for u in [0,1] do
for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),a^p,b^p=(c,b)^z,c^p=(b,a)^u*(c,b)^t,d^p=(c,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;

for t in [1..p-1] do
for x in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),a^p,b^p=(b,a)^x,c^p=(c,b)^t,d^p=(c,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;

GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),a^p,b^p,c^p,d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),a^p,b^p,c^p=(b,a),d^p=(c,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;

for u in [0..((p-1) div 2)] do
  count:=count+1;
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),a^p,b^p=(b,a),c^p=(b,a)^u,d^p=(c,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;

//vprint Orderp7, 2: count-count1,p^2+(3*p+1)/2;
//count1:=count;

//Get pb,pc when pa=0, pd=cb

for y1 in [0..p-1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A:=H22![y1,y2,y3,y4];

for b in [0..p-1] do
for c in [0..p-1] do
if b+c ne 0 then

B:=H22![c,w*b,b,c];

C:=H22![c*(c^2-w*b^2),w*b*(c^2-w*b^2),
        b*(c^2-w*b^2),c*(c^2-w*b^2)];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

B:=H22![-c,-w*b,b,c];

C:=H22![-c*(c^2-w*b^2),-w*b*(c^2-w*b^2),
        b*(c^2-w*b^2),c*(c^2-w*b^2)];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),
                     a^p,b^p=(b,a)^y1*(c,a)^y2,c^p=(b,a)^y3*(c,a)^y4,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;

//vprint Orderp7, 2: count-count1;
//count1:=count;

//Get pb,pc when pa=ca, pd=cb

for x in [0..p-1] do
for u in [0..((p-1) div 2)] do
for v in [0..p-1] do
lastt:=p-1;
if u eq 0 then lastt:=(p-1) div 2; end if;
for t in [0..lastt] do
  count:=count+1;
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),
                     a^p=(c,a),b^p=(b,a)^x,c^p=(b,a)^u*(c,a)^v*(c,b)^t,d^p=(c,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
end for;

//vprint Orderp7, 2: count-count1,p^2*(p^2+1)/2;
//count1:=count;

//Get pa,pd when pa,pd span <ba,ca> and pb=pc=0

y1:=0;
y2:=1;
for y3 in [1..p-1] do
for y4 in [0..(p-1) div 2] do

new:=1;
index:=p*y3+y4;

A:=H22![y1,y2,y3,y4];

for r in range do
a:=r[1];
d:=r[2];
for s in range do
b1:=s[1];
c1:=s[2];
if F!(b1*w*y3*d^2+b1*a*y4*d+b1*a^2-y4*c1*d^2-d*a*c1-d*y3*a*c1) eq 0 then
k1:=F!(-b1*w*d*(y4*d+a+a*y3)+c1*(w*y3*d^2+y4*a*d+a^2));
k2:=F!((a^2-w*d^2)*(c1^2-w*b1^2));
k:=Z!(k1*k2^-1);
b:=k*b1;
c:=k*c1;

B:=H22![a,d,w*d,a];
C:=H22![a*c-w*b*d,w*a*b-w*c*d,
        a*b-c*d,a*c-w*b*d];

D:=B*A*C^-1;

z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;
if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  Include(~pow416,[0,1,0,0,0,0,0,0,0,y3,y4,0]);
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),
                     a^p=(c,a),b^p,c^p,d^p=(b,a)^y3*(c,a)^y4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;

//vprint Orderp7, 2: count-count1,p;
//count1:=count;

//Get pa,pd when pa,pd span <ba,ca>, pb=0 and pc notin <ba,ca>

//First get possibilities for pa,pd with pb=0, pc=cb
mats:={};

for y1 in [0..p-1] do
for y2 in [0..((p-1) div 2)] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A:=H22![y1,y2,y3,y4];
if Rank(A) eq 2 then

for r in range do
a:=r[1];
d:=r[2];

B:=H22![a,d,w*d,a];
C:=H22![a,-w*d,-d,a];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

B[2]:=-B[2];
C[2]:=-C[2];

D:=B*A*C^-1;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),
                     a^p=(b,a)^y1*(c,a)^y2,b^p,c^p=(c,b),d^p=(b,a)^y3*(c,a)^y4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  Include(~mats,A);
end if;

end if;

end for;
end for;
end for;
end for;

//For the pa,pd just found, see which go with pb=0, pc=ca+cb
for A in mats do
y1:=Z!(A[1][1]);
y2:=Z!(A[1][2]);
y5:=Z!(A[2][1]);
y6:=Z!(A[2][2]);

y3:=0; y4:=1;

A2:=H43![y1,y2,0,0,0,0,y3,y4,1,y5,y6,0];
new:=1;

for r in range do
a:=r[1];
d:=r[2];

B:=H22![a,d,w*d,a];
C:=H22![a,-w*d,-d,a];
D:=B*A*C^-1;

B[2]:=-B[2];
C[2]:=-C[2];
D2:=B*A*C^-1;

if D eq A or D2 eq A then

for n in [0..p-1] do
for x in [0..p-1] do

if D eq A then

B:=H44![a,0,0,d,
        0,1,0,0,
        n,0,1,x,
        w*d,0,0,a];

C:=H33![a,-w*d,0,
        -d,a,0,
        -n,w*x,1];
D3:=B*A2*C^-1;

z1:=Z!(D3[3][1]);
z2:=Z!(D3[3][2]);

if z1+z2 eq 0 then new:=0; end if;

end if;

if D2 eq A then

B:=H44![a,0,0,d,
        0,1,0,0,
        n,0,-1,x,
        -w*d,0,0,-a];

C:=H33![a,-w*d,0,
        d,-a,0,
       -n,w*x,-1];

D3:=B*A2*C^-1;

z1:=Z!(D3[3][1]);
z2:=Z!(D3[3][2]);

if z1+z2 eq 0 then new:=0; end if;

end if;

if new eq 0 then break; end if;
end for;
if new eq 0 then break; end if;
end for;

end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|(d,a),(d,b)=(c,a)^w,(d,c)=(b,a),
                     a^p=(b,a)^y1*(c,a)^y2,b^p,c^p=(c,a)*(c,b),d^p=(b,a)^y5*(c,a)^y6>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;

//vprint Orderp7, 2: count-count1;

vprint Orderp7, 2: "There are",count,"four generator p-class 2 groups with";
vprint Orderp7, 2: "[d,a]=1,[d,b]=[c,a]^w,[d,c]=[b,a]";

vprint Orderp7, 2:
   "Total number of groups is (p^4 + p^3 + 6p^2 + 9p + 13)/2 =",(p^4+p^3+6*p^2+9*p+13)/2;

if Process then return Nmr; else return L; end if;

end function;

//Descendants of 4.1
Group4_1 := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

   if p lt 3 then print "Only valid for p>2"; end if;

   lim := 0;
   limited := not Process and Limit ge 1;
   L := [];
   count := 0;
   M := Group4_1aa (p: Process:=Process, Select:=Select,Limit:=Limit);
   Append (~L, M); 
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_1a (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M); 
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_1b (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M); 
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_1c (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M); 
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_1d (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_11 (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_12 (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M); 
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_13 (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_14 (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M); 
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_15 (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;
   M := Group4_16 (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M); 
   if limited then count +:= #L; if count ge Limit then return &cat L; end if;
       lim := Limit - count;
   end if;

   if Process eq true then L := &+L; end if;

   if Process eq false then 
      L := &cat (L); 
      if p eq 3 then 
         vprint Orderp7, 2: "Sequence of groups has length",#L;
      else 
         vprint Orderp7, 2: "Total number of groups is p^5+2p^4+7p^3+25p^2+88p+270+(p+4)gcd(p-1,3)+gcd(p-1,4) =",#L;
      end if;
   end if;

   if p eq 3 then
      vprint Orderp7, 1:"Group 4.1 has 1361 immediate descendants of order 3^7";
   else 
      vprint Orderp7, 1: "Group 4.1 has ", 
      p^5+2*p^4+7*p^3+25*p^2+88*p+270+(p+4)*Gcd(p-1,3)+Gcd(p-1,4),
      "immediate descendants of order p^7";
   end if;

   return L;
end function;

Children39 := function (p: Process:=true, Select:=func<x|true>)
   return Group4_1 (p: Process := Process, Select := Select);
end function;
