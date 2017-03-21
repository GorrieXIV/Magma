freeze;

import "misc.m": ProcessPresentation; 

//Descendants of 5.3.  You need 5.3a, 5.3b, ..., 5.3i

Group5_3a := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//This program computes presentations for groups from
//Case 1 in the descendants of 5.3
//[c,a]=[c,b]=[d,a]=[d,b]=[d,c]=1

class:=3;
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

SQ:={};
for i in [0..((p-1) div 2)] do
  j:=i^2 mod p;
  Include(~SQ,j);
end for;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p,b^p,c^p=(b,a,a),d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p,b^p,c^p=(b,a,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,a),b^p,c^p=(b,a,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p,b^p=(b,a,a),c^p=(b,a,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p,b^p=(b,a,a)^w,c^p=(b,a,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,b),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,b)^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,a),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=9;
for x in [1..p-1] do
  y:=(F!x)^-1; y:=Integers()!y;
  if x le y then
    count:=count+1;
    GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,a),b^p=(b,a,b)^x,c^p,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end if;
end for;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a)*(b,a,b),b^p=(b,a,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a)*(b,a,b)^w,b^p=(b,a,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^w,b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [1..p-1] do
  if (1+4*x) mod p notin SQ then
    count:=count+1;
    GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,b)^x,b^p=(b,a,a)*(b,a,b),c^p,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end if;
end for;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of";
vprint Orderp7, 2:"order p^7 satisfying [c,a]=[c,b]=[d,a]=[d,b]=[d,c]=1";

vprint Orderp7, 2: "Total number of groups is p + 12 =",p+12;

if Process then return Nmr; else return L; end if;

end function;

Group5_3b := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//This program computes presentations for groups from
//Case 2 in the descendants of 5.3
//[c,b]=[d,a]=[d,b]=[d,c]=1, [c,a]=[b,a,b]

class:=3;
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

SQ:={};
for i in [0..((p-1) div 2)] do
  j:=i^2 mod p;
  Include(~SQ,j);
end for;

w2:=w^2 mod p;
w3:=w^3 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
             a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,b),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,b)^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,a),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                 a^p=(b,a,a)^x,b^p=(b,a,b),c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
               a^p=(b,a,a)*(b,a,b),b^p=(b,a,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
               a^p=(b,a,a)*(b,a,b)^w,b^p=(b,a,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=p+6;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a)*(b,a,b)^x,b^p=(b,a,a),c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b),b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^w,b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a)*(b,a,b)^x,b^p=(b,a,a)^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b),b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^w,b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p=(b,a,a)^x,c^p=(b,a,b),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a),b^p,c^p=(b,a,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b),b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^w,b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+4;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,b)^w2,b^p,c^p=(b,a,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,b)^w3,b^p,c^p=(b,a,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end if;
if p mod 3 eq 1 then
  for i in [2..p-2] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [0..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
    for y in [1,w,w2] do
      count:=count+1;
      GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                       a^p=(b,a,b)^x,b^p=(b,a,b)^y,c^p=(b,a,a),d^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    end for;
    end if;
  end for;
else;
  for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,b)^x,b^p=(b,a,b),c^p=(b,a,a),d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
end if;
count:=count+1;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                 a^p,b^p,c^p=(b,a,b),d^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0,1,w] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^x,b^p=(b,a,b)^y,c^p,d^p=(b,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p,c^p=(b,a,a),d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p=(b,a,a),c^p,d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p=(b,a,a)^w,c^p,d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p,c^p,d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a),b^p,c^p,d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+5;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of";
vprint Orderp7, 2:"order p^7 satisfying [c,b]=[d,a]=[d,b]=[d,c]=1,[c,a]=[b,a,b]";

vprint Orderp7, 2: "Total number of groups is 5p + 25 + gcd(p-1,3) + gcd(p-1,4) =",
5*p+25+Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;

Group5_3c := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//This program computes presentations for groups from
//Case 3 in the descendants of 5.3
//[c,b]=[d,a]=[d,b]=[d,c]=1, [c,a]=[b,a,a]

class:=3;
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

SQ:={};
for i in [0..((p-1) div 2)] do
  j:=i^2 mod p;
  Include(~SQ,j);
end for;

w2:=w^2 mod p;
w3:=w^3 mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
             a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,a),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,b),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,a)*(b,a,b),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,b)^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,a)*(b,a,b)^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,b),b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
             a^p=(b,a,b),b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
               a^p=(b,a,b)^w,b^p=(b,a,a)^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
else;
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
               a^p=(b,a,b)^w,b^p=(b,a,a),c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
count:=9;
for x in [0..p-1] do
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,a)*(b,a,b)^x,b^p=(b,a,a),c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,a)*(b,a,b)^x,b^p=(b,a,a)^w,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
for x in [1..p-1] do
  y:=(F!x)^-1; y:=Integers()!y;
  if x le y then
    count:=count+1;
    GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,a),b^p=(b,a,b)^x,c^p,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end if;
end for;
for x in [1..p-1] do
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,a)*(b,a,b),b^p=(b,a,b)^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                     a^p=(b,a,a)*(b,a,b)^w,b^p=(b,a,b)^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
for y in [2..p-2] do
  z:=(F!y)^-1; z:=Integers()!z;
  if y le z then
  for x in [1..p-1] do
    GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                       a^p=(b,a,a)*(b,a,b),b^p=(b,a,a)^x*(b,a,b)^y,c^p,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                       a^p=(b,a,a)*(b,a,b)^w,b^p=(b,a,a)^x*(b,a,b)^y,c^p,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    count:=count+2;
  end for;
  end if;
end for;
for x in [1..((p-1) div 2)] do
  x2:=x^2 mod p; wx2:=(w*x2) mod p;
  for y in [1,-1] do
    GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                       a^p=(b,a,a)*(b,a,b),b^p=(b,a,a)^x2*(b,a,b)^y,c^p,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                       a^p=(b,a,a)*(b,a,b),b^p=(b,a,a)^(wx2)*(b,a,b)^y,c^p,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    if p mod 4 eq 1 then
      GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                         a^p=(b,a,a)*(b,a,b)^w,b^p=(b,a,a)^wx2*(b,a,b)^y,c^p,d^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    else;
      GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                         a^p=(b,a,a)*(b,a,b)^w,b^p=(b,a,a)^x2*(b,a,b)^y,c^p,d^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    end if;
    count:=count+3;
  end for;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b),b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^w,b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^x,b^p=(b,a,b),c^p=(b,a,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in [0..p-1] do
for y in [x..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^x,b^p=(b,a,b)^y,c^p=(b,a,a)*(b,a,b),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
count:=count+1;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                 a^p,b^p,c^p=(b,a,b),d^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0,1,w] do
for y in [0,1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,b)^x,b^p=(b,a,b)^y,c^p,d^p=(b,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p,c^p=(b,a,a),d^p=(b,a,a)*(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p,b^p,c^p,d^p=(b,a,a)*(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a),b^p,c^p,d^p=(b,a,a)*(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a)^w,b^p,c^p,d^p=(b,a,a)*(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+4;
for x in [1..((p-1) div 2)] do
  wx2:=(w*x^2) mod p;
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                   a^p=(b,a,a),b^p=(b,a,a)^wx2,c^p,d^p=(b,a,a)*(b,a,b)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in [1..((p-1) div 2)] do
  x2:=x^2 mod p; xm2:=(F!x2)^-1; xm2:=Integers()!xm2; wx2:=(w*x2) mod p;
  if x2 le xm2 then
    GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                       a^p=(b,a,a),b^p=(b,a,a)^x2,c^p,d^p=(b,a,a)*(b,a,b)>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    GR:=Group<a,b,c,d|(c,a)=(b,a,a),(c,b),(d,a),(d,b),(d,c),
                       a^p=(b,a,a)^w,b^p=(b,a,a)^wx2,c^p,d^p=(b,a,a)*(b,a,b)>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    count:=count+2;
  end if;
end for;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of";
vprint Orderp7, 2:"order p^7 satisfying [c,b]=[d,a]=[d,b]=[d,c]=1,[c,a]=[b,a,a]";

vprint Orderp7, 2: "Total number of groups is (3p^2 + 12p + 41 + gcd(p-1,4))/2 =",
(3*p^2+12*p+41+Gcd(p-1,4))/2;

if Process then return Nmr; else return L; end if;

end function;

Group5_3d := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//This program computes presentations for groups from
//Case 4 in the descendants of 5.3
//[d,a]=[d,b]=[d,c]=1, [c,a]=[b,a,b], [c,b]=[b,a,a]^w

class:=3;
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

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b)=(b,a,a)^w,(d,a),(d,b),(d,c),
             a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=1;
for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b),(d,c),
                     a^p=e^x*f,b^p,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b),(d,c),
                     a^p=e^x*f^w,b^p,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b),(d,c),
                 a^p=e,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b)=(b,a,a)^w,(d,a),(d,b),(d,c),
                   a^p=(b,a,a)^w,b^p,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;
/*
Case 4 in the descendants of 5.3

We have a 2x2 matrix A representing pa,pb and we
map it to (det P)^-1.PAP^-1 where

  P =   [a ,b]
     +/-[wb,a]

Get orbits of rank two matrices A
*/

Z:=Integers();
V2:=VectorSpace(F,2);
H22:=Hom(V2,V2);

range:={[0,1]};
for i in [0..p-1] do
  Include(~range,[1,i]);
end for;

SQ:={};
for i in [1..((p-1) div 2)] do
  Include(~SQ,F!(i^2));
end for;

for i in [2..p-1] do
  if F!i notin SQ then
    lnsq:=F!i;
    zlnsq:=i;
    break;
  end if;
end for;

for y1 in [0,1,zlnsq] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

//A represents pa,pb
A:=H22![y1,y2,y3,y4];

if Rank(A) eq 2 then

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

//Find first non-zero entry in A
nza:=1;
u:=A[1][1];
if u eq 0 then
  nza:=2;
  u:=A[1][2];
end if;

if u eq 1 or u eq lnsq then

for r in range do
a:=r[1]; b:=r[2];

P:=H22![a,b,w*b,a];
c:=F!(a^2-w*b^2);

//D is the image of A under the action of the group element
D:=c^-1*P*A*P^-1;

//Find first non-zero entry in D
nzd:=1;
u:=D[1][1];
if u eq 0 then
  nzd:=2;
  u:=D[1][2];
end if;

if nza lt nzd then new:=0; end if;

if nza eq nzd then

D:=u^-1*D;
if u notin SQ then D:=lnsq*D; end if;

//Get entries in image of A
z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

P[2]:=-P[2];
c:=-c;

//D is the image of A under the action of the group element
D:=c^-1*P*A*P^-1;

//Find first non-zero entry in D
nzd:=1;
u:=D[1][1];
if u eq 0 then
  nzd:=2;
  u:=D[1][2];
end if;

if nza lt nzd then new:=0; end if;

if nza eq nzd then

D:=u^-1*D;
if u notin SQ then D:=lnsq*D; end if;

//Get entries in image of A
z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  //We have a new orbit representative
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b),(d,c),
                   a^p=e^y1*f^y2,b^p=e^y3*f^y4,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end if;
end if;

end for;
end for;
end for;
end for;

for x in [0..((p-1) div 2)] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b),(d,c),
                            a^p=e^x,b^p=e^y,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b),(d,c),
                          a^p,b^p,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;

for x in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b),(d,c),
                              a^p=f,b^p=f^x,c^p,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;

  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b),(d,c),
                              a^p=f^w,b^p=f^x,c^p,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b)=(b,a,a)^w,(d,a),(d,b),(d,c),
                            a^p,b^p,c^p,d^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;

GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b)=(b,a,a)^w,(d,a),(d,b),(d,c),
                            a^p,b^p=(b,a,b),c^p,d^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
if p mod 4 eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b)=(b,a,a)^w,(d,a),(d,b),(d,c),
                            a^p,b^p=(b,a,b)^w,c^p,d^p=(b,a,a)>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of order";
vprint Orderp7, 2:"p^7 satisfying [d,a]=[d,b]=[d,c]=1,[c,a]=[b,a,b],[c,b]=[b,a,a]^w";

vprint Orderp7, 2: "Total number of groups is (3p^2 + 6p + 11 + gcd(p-1,4))/2 =",
(3*p^2+6*p+11+Gcd(p-1,4))/2;

if Process then return Nmr; else return L; end if;

end function;

Group5_3e := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//This program computes presentations for groups from
//Case 5 in the descendants of 5.3
//[c,a]=[d,a]=[d,c]=1, [c,b]=[b,a,a], [d,b]=[b,a,b]

class:=3;
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

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|(c,a),(c,b)=(b,a,a),(d,a),(d,b)=(b,a,b),(d,c),
             a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b)=(b,a,a),(d,a),(d,b)=(b,a,b),(d,c),
             a^p,b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b)=(b,a,a),(d,a),(d,b)=(b,a,b),(d,c),
             a^p,b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b)=(b,a,a),(d,a),(d,b)=(b,a,b),(d,c),
             a^p,b^p=(b,a,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d|(c,a),(c,b)=(b,a,a),(d,a),(d,b)=(b,a,b),(d,c),
                 a^p=(b,a,a),b^p=(b,a,b)^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
               a^p=e,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
               a^p=e,b^p=e^w*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
               a^p=f,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
               a^p=f,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
               a^p=f,b^p=e^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=p+9;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=f,b^p=e^x*f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=f^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=f^w,b^p=e,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=f^w,b^p=e^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=f^w,b^p=e^x*f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a),(c,b)=(b,a,a),(d,a),(d,b)=(b,a,b),(d,c),
                   a^p,b^p,c^p,d^p=(b,a,a)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p=f,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=f,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=f^w,b^p,c^p,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b)=(b,a,a),(d,a),(d,b)=(b,a,b),(d,c),
                   a^p,b^p,c^p,d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p=e,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p=e^w,c^p,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+7;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=e,b^p=e^x,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p,c^p=e,d^p=f^x>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
count:=count+1;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                 a^p,b^p,c^p=e,d^p=e*f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                     a^p=f^x,b^p,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                     a^p=f^x,b^p=f,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p,c^p=f,d^p=e^x*f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p,c^p=f,d^p=e>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p,c^p=f,d^p=e^w>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b)=(b,a,a),(d,a),(d,b)=(b,a,b),(d,c),
                   a^p,b^p,c^p=(b,a,b),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=e,b^p,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                     a^p=e^w,b^p,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                     a^p=e^w2,b^p,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p=e,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p=e^w,c^p=f,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                     a^p,b^p=e^w2,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                     a^p,b^p=e^w3,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end if;
if p mod 3 eq 1 then
  for i in [2..p-2] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
    for y in [1,w,w2] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                       a^p=e^y,b^p=e^x,c^p=f,d^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    end for;
    end if;
  end for;
else;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                     a^p=e,b^p=e^x,c^p=f,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
end if;
for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=e^x,b^p=e^y,c^p=f,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of order";
vprint Orderp7, 2:"p^7 satisfying [c,a]=[d,a]=[d,c]=1,[c,b]=[b,a,a],[d,b]=[b,a,b]";

vprint Orderp7, 2: "Total number of groups is p^2 + 9p + 20 + gcd(p-1,3) + gcd(p-1,4) =",
p^2+9*p+20+Gcd(p-1,3)+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;

Group5_3f := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

/*
This program computes the orbits of the 4x2 matrices
representing a^p,b^p,c^p,d^p needed for Case 6 in the
descendants of 5.3

[c,a]=[b,a,b], [c,b]=[b,a,a], [d,a]=1, [d,b]=[b,a,b], [d,c]=1

We have a 4x2 matrix A with rows representing pa,pb,pc,pd
and we premultiply by

     [a,-b,c,d]
  +/-[b,a,l,m]
     [0,0,a^2-b^2,-4ab]
  +/-[0,0,ab,a^2-b^2]

and post multiply by the inverse of

  (a^2+b^2). +/-[a,-b]
                [b,a]

*/

class:=3;
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

Z:=Integers();
V2:=VectorSpace(F,2);
H22:=Hom(V2,V2);

range:={[0,1]};
for i in [0..p-1] do
  if (1+i^2) mod p ne 0 then
    Include(~range,[1,i]);
  end if;
end for;

nz:=[[1,1],[1,2],[2,1],[2,2]];

SQ:={};
for i in [1..((p-1) div 2)] do
  Include(~SQ,(F!i)^2);
end for;

for i in [2..p-1] do
  j:=F!i;
  if j notin SQ then
    lnsq:=j; zlnsq:=i; break;
  end if;
end for;

mats:={};
L:=[]; Nmr := 0;

//First get non-zero possibilities for pc,pd.

for y1 in [0..1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

A:=H22![y1,y2,y3,y4];
if A eq 0 then continue; end if;

//Get first non-zero entry in A
for i in [1..4] do
  spot:=nz[i];
  if A[spot[1],spot[2]] ne 0 then break; end if;
end for;

//We only need A with leading entry 1
if A[spot[1],spot[2]] ne 1 then continue; end if;

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

for r in range do
a:=r[1]; b:=r[2];

B:=H22![a^2-b^2,-4*a*b,a*b,a^2-b^2];
C:=F!(a^2+b^2)*H22![a,-b,b,a];
D:=B*A*C^-1;

//Get first non-zero entry in D
for i in [1..4] do
  spot:=nz[i];
  if D[spot[1],spot[2]] ne 0 then; break; end if;
end for;

//Normalize D
u:=D[spot[1],spot[2]];
D:=u^-1*D;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

B[2]:=-B[2];
C[1]:=-C[1];
D:=B*A*C^-1;

//Get first non-zero entry in D
for i in [1..4] do
  spot:=nz[i];
  if D[spot[1],spot[2]] ne 0 then; break; end if;
end for;

//Normalize D
u:=D[spot[1],spot[2]];
D:=u^-1*D;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  Include(~mats,A);
end if;

end for;
end for;
end for;
end for;

count:=0;

//Get pa,pb when pc=pd=0
for y1 in [0,1,zlnsq] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A:=H22![y1,y2,y3,y4];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  continue;
end if;

//Get first non-zero entry in A
for i in [1..4] do
  spot:=nz[i];
  if A[spot[1],spot[2]] ne 0 then break; end if;
end for;

if (A[spot[1],spot[2]] ne 1) and (A[spot[1],spot[2]] ne zlnsq) then continue; end if;

for r in range do
a:=r[1]; b:=r[2];

B:=H22![a,-b,b,a];
C:=F!(a^2+b^2)*H22![a,-b,b,a];
D:=B*A*C^-1;

//Get first non-zero entry in D
for i in [1..4] do
  spot:=nz[i];
  if D[spot[1],spot[2]] ne 0 then break; end if;
end for;

u:=D[spot[1],spot[2]];
D:=u^-1*D;
if u notin SQ then D:=lnsq*D; end if;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

B[2]:=-B[2];
C[1]:=-C[1];
D:=B*A*C^-1;

//Get first non-zero entry in D
for i in [1..4] do
  spot:=nz[i];
  if D[spot[1],spot[2]] ne 0 then break; end if;
end for;

u:=D[spot[1],spot[2]];
D:=u^-1*D;
if u notin SQ then D:=lnsq*D; end if;

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
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=e^y1*f^y2,b^p=e^y3*f^y4,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;

//Now get rest

for A in mats do

t1:=Z!(A[1][1]);
t2:=Z!(A[1][2]);
t3:=Z!(A[2][1]);
t4:=Z!(A[2][2]);

if Rank(A) eq 2 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p,b^p,c^p=e^t1*f^t2,d^p=e^t3*f^t4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
else;

if t1 eq 0 and t3 eq 0 then

if t2 ne 0 then
  v:=A[1];
else;
  v:=A[2];
end if;
u:=v[2];
v:=u^-1*v;

for y1 in [0..p-1] do
y2:=0;
for y3 in [0..p-1] do
y4:=0;

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A2:=H22![y1,y2,y3,y4];

for r in range do
a:=r[1]; b:=r[2];

B:=H22![a^2-b^2,-4*a*b,a*b,a^2-b^2];
C:=F!(a^2+b^2)*H22![a,-b,b,a];
D1:=B*A*C^-1;

//Get first non-zero entry in D1
for i in [1..4] do
  spot:=nz[i];
  if D1[spot[1],spot[2]] ne 0 then break; end if;
end for;

u1:=D1[spot[1],spot[2]];
D1:=u1^-1*D1;

B[2]:=-B[2];
C[1]:=-C[1];
D2:=B*A*C^-1;

//Get first non-zero entry in D2
for i in [1..4] do
  spot:=nz[i];
  if D2[spot[1],spot[2]] ne 0 then break; end if;
end for;

u2:=D2[spot[1],spot[2]];
D2:=u2^-1*D2;

if D1 eq A or D2 eq A then

B:=H22![a,-b,b,a];
C:=F!(a^2+b^2)*H22![a,-b,b,a];

if D1 eq A then

C1:=u1^2*C;
D:=B*A2*C1^-1;

z2:=D[1][2];
D[1]:=D[1]-z2*v;
z4:=D[2][2];
D[2]:=D[2]-z4*v;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

if D2 eq A then

B[2]:=-B[2];
C[1]:=-C[1];
C2:=u2^2*C;
D:=B*A2*C2^-1;

z2:=D[1][2];
D[1]:=D[1]-z2*v;
z4:=D[2][2];
D[2]:=D[2]-z4*v;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;
end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e,(d,a),(d,b)=f,(d,c),
                   a^p=e^y1,b^p=e^y3,c^p=f^t2,d^p=f^t4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;

else;
//one of t1,t3 is non-zero

if t1 ne 0 then
  v:=A[1];
else;
  v:=A[2];
end if;
u:=v[1];
v:=u^-1*v;

y1:=0;
for y2 in [0..p-1] do
y3:=0;
for y4 in [0..p-1] do

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A2:=H22![y1,y2,y3,y4];

for r in range do
a:=r[1]; b:=r[2];

B:=H22![a^2-b^2,-4*a*b,a*b,a^2-b^2];
C:=F!(a^2+b^2)*H22![a,-b,b,a];
D1:=B*A*C^-1;

//Get first non-zero entry in D1
for i in [1..4] do
  spot:=nz[i];
  if D1[spot[1],spot[2]] ne 0 then break; end if;
end for;

u1:=D1[spot[1],spot[2]];
D1:=u1^-1*D1;

B[2]:=-B[2];
C[1]:=-C[1];
D2:=B*A*C^-1;

//Get first non-zero entry in D2
for i in [1..4] do
  spot:=nz[i];
  if D2[spot[1],spot[2]] ne 0 then break; end if;
end for;

u2:=D2[spot[1],spot[2]];
D2:=u2^-1*D2;

if D1 eq A or D2 eq A then

B:=H22![a,-b,b,a];
C:=F!(a^2+b^2)*H22![a,-b,b,a];

if D1 eq A then

C1:=u1^2*C;
D:=B*A2*C1^-1;

z1:=D[1][1];
D[1]:=D[1]-z1*v;
z3:=D[2][1];
D[2]:=D[2]-z3*v;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

if D2 eq A then

B[2]:=-B[2];
C[1]:=-C[1];
C2:=u2^2*C;

D:=B*A2*C2^-1;

z1:=D[1][1];
D[1]:=D[1]-z1*v;
z3:=D[2][1];
D[2]:=D[2]-z3*v;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e,(d,a),(d,b)=f,(d,c),
   a^p=f^y2,b^p=f^y4,c^p=e^t1*f^t2,d^p=e^t3*f^t4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;

end if;
end if;
end for;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of order";
vprint Orderp7, 2:"p^7 satisfying [c,a]=[b,a,b], [c,b]=[b,a,a], [d,a]=1,";
vprint Orderp7, 2:"[d,b]=[b,a,b], [d,c]=1";

if p mod 12 eq 1 then vprint Orderp7, 2: "Total number of groups is 3p^2+(19/2)p+15+p^3/2",3*p^2+(19/2)*p+15+p^3/2; end if;
if p mod 12 eq 5 then vprint Orderp7, 2: "Total number of groups is 3p^2+(19/2)p+12+p^3/2",3*p^2+(19/2)*p+12+p^3/2; end if;
if p mod 12 eq 7 then vprint Orderp7, 2: "Total number of groups is 2p^2+(5/2)p+2+p^3/2",2*p^2+(5/2)*p+2+p^3/2; end if;
if p mod 12 eq 11 then vprint Orderp7, 2: "Total number of groups is 2p^2+(5/2)p+3+p^3/2",2*p^2+(5/2)*p+3+p^3/2; end if;

if Process then return Nmr; else return L; end if;

end function;

Group5_3g := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

/*
This program computes the orbits of the 4x2 matrices representing
a^p,b^p,c^p,d^p needed for Case 7 in the descendants of 5.3

[c,a]=[b,a,b], [c,b]=[b,a,a]^w, [d,a]=1, [d,b]=[b,a,b], [d,c]=1

We have a 4x2 matrix A with rows representing pa,pb,pc,pd
and we premultiply by

     [a,b,c,d]
  +/-[-wb,a,l,m]
     [0,0,a^2-wb^2,4wab]
  +/-[0,0,-ab,a^2-wb^2]

and post multiply by the inverse of

  (a^2+wb^2). +/-[a,b]
                 [-wb,a]

*/

class:=3;
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

Z:=Integers();
V2:=VectorSpace(F,2);
H22:=Hom(V2,V2);

range:={[0,1]};
for i in [0..p-1] do
  if (1+w*i^2) mod p ne 0 then
    Include(~range,[1,i]);
  end if;
end for;

nz:=[[1,1],[1,2],[2,1],[2,2]];

SQ:={};
for i in [1..((p-1) div 2)] do
  Include(~SQ,(F!i)^2);
end for;

for i in [2..p-1] do
  j:=F!i;
  if j notin SQ then
    lnsq:=j; zlnsq:=i; break;
  end if;
end for;

mats:={};

//First get non-zero possibilities for pc,pd.

for y1 in [0..1] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

A:=H22![y1,y2,y3,y4];
if A eq 0 then continue; end if;

//Get first non-zero entry in A
for i in [1..4] do
  spot:=nz[i];
  if A[spot[1],spot[2]] ne 0 then break; end if;
end for;

//We only need A with leading entry 1
if A[spot[1],spot[2]] ne 1 then continue; end if;

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

for r in range do
a:=r[1]; b:=r[2];

B:=H22![a^2-w*b^2,4*w*a*b,-a*b,a^2-w*b^2];
C:=F!(a^2+w*b^2)*H22![a,b,-w*b,a];
D:=B*A*C^-1;

//Get first non-zero entry in D
for i in [1..4] do
  spot:=nz[i];
  if D[spot[1],spot[2]] ne 0 then; break; end if;
end for;

//Normalize D
u:=D[spot[1],spot[2]];
D:=u^-1*D;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

B[2]:=-B[2];
C[1]:=-C[1];
D:=B*A*C^-1;

//Get first non-zero entry in D
for i in [1..4] do
  spot:=nz[i];
  if D[spot[1],spot[2]] ne 0 then; break; end if;
end for;

//Normalize D
u:=D[spot[1],spot[2]];
D:=u^-1*D;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  Include(~mats,A);
end if;

end for;
end for;
end for;
end for;

count:=0;
L:=[]; Nmr := 0;

//Get pa,pb when pc=pd=0
for y1 in [0,1,zlnsq] do
for y2 in [0..p-1] do
for y3 in [0..p-1] do
for y4 in [0..p-1] do

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A:=H22![y1,y2,y3,y4];
if A eq 0 then
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b)=(b,a,a)^w,(d,a),(d,b)=(b,a,b),(d,c),
                   a^p,b^p,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  continue;
end if;

//Get first non-zero entry in A
for i in [1..4] do
  spot:=nz[i];
  if A[spot[1],spot[2]] ne 0 then break; end if;
end for;

if (A[spot[1],spot[2]] ne 1) and (A[spot[1],spot[2]] ne zlnsq) then continue; end if;

for r in range do
a:=r[1]; b:=r[2];

B:=H22![a,b,-w*b,a];
C:=F!(a^2+w*b^2)*H22![a,b,-w*b,a];
D:=B*A*C^-1;

//Get first non-zero entry in D
for i in [1..4] do
  spot:=nz[i];
  if D[spot[1],spot[2]] ne 0 then break; end if;
end for;

u:=D[spot[1],spot[2]];
D:=u^-1*D;
if u notin SQ then D:=lnsq*D; end if;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

B[2]:=-B[2];
C[1]:=-C[1];
D:=B*A*C^-1;

//Get first non-zero entry in D
for i in [1..4] do
  spot:=nz[i];
  if D[spot[1],spot[2]] ne 0 then break; end if;
end for;

u:=D[spot[1],spot[2]];
D:=u^-1*D;
if u notin SQ then D:=lnsq*D; end if;

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
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b)=f,(d,c),
                   a^p=e^y1*f^y2,b^p=e^y3*f^y4,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;
end for;
end for;

//Now get rest

for A in mats do

t1:=Z!(A[1][1]);
t2:=Z!(A[1][2]);
t3:=Z!(A[2][1]);
t4:=Z!(A[2][2]);

if Rank(A) eq 2 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b)=f,(d,c),
                   a^p,b^p,c^p=e^t1*f^t2,d^p=e^t3*f^t4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
else;

if t1 eq 0 and t3 eq 0 then

if t2 ne 0 then
  v:=A[1];
else;
  v:=A[2];
end if;
u:=v[2];
v:=u^-1*v;

for y1 in [0..p-1] do
y2:=0;
for y3 in [0..p-1] do
y4:=0;

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A2:=H22![y1,y2,y3,y4];

for r in range do
a:=r[1]; b:=r[2];

B:=H22![a^2-w*b^2,4*w*a*b,-a*b,a^2-w*b^2];
C:=F!(a^2+w*b^2)*H22![a,b,-w*b,a];
D1:=B*A*C^-1;

//Get first non-zero entry in D1
for i in [1..4] do
  spot:=nz[i];
  if D1[spot[1],spot[2]] ne 0 then break; end if;
end for;

u1:=D1[spot[1],spot[2]];
D1:=u1^-1*D1;

B[2]:=-B[2];
C[1]:=-C[1];
D2:=B*A*C^-1;

//Get first non-zero entry in D2
for i in [1..4] do
  spot:=nz[i];
  if D2[spot[1],spot[2]] ne 0 then break; end if;
end for;

u2:=D2[spot[1],spot[2]];
D2:=u2^-1*D2;

if D1 eq A or D2 eq A then

B:=H22![a,b,-w*b,a];
C:=F!(a^2+w*b^2)*H22![a,b,-w*b,a];

if D1 eq A then

C1:=u1^2*C;
D:=B*A2*C1^-1;

z2:=D[1][2];
D[1]:=D[1]-z2*v;
z4:=D[2][2];
D[2]:=D[2]-z4*v;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

if D2 eq A then

B[2]:=-B[2];
C[1]:=-C[1];
C2:=u2^2*C;
D:=B*A2*C2^-1;

z2:=D[1][2];
D[1]:=D[1]-z2*v;
z4:=D[2][2];
D[2]:=D[2]-z4*v;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;
end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b)=f,(d,c),
                   a^p=e^y1,b^p=e^y3,c^p=f^t2,d^p=f^t4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;

else;
//one of t1,t3 is non-zero

if t1 ne 0 then
  v:=A[1];
else;
  v:=A[2];
end if;
u:=v[1];
v:=u^-1*v;

y1:=0;
for y2 in [0..p-1] do
y3:=0;
for y4 in [0..p-1] do

new:=1;
index:=p^3*y1+p^2*y2+p*y3+y4;

A2:=H22![y1,y2,y3,y4];

for r in range do
a:=r[1]; b:=r[2];

B:=H22![a^2-w*b^2,4*w*a*b,-a*b,a^2-w*b^2];
C:=F!(a^2+w*b^2)*H22![a,b,-w*b,a];
D1:=B*A*C^-1;

//Get first non-zero entry in D1
for i in [1..4] do
  spot:=nz[i];
  if D1[spot[1],spot[2]] ne 0 then break; end if;
end for;

u1:=D1[spot[1],spot[2]];
D1:=u1^-1*D1;

B[2]:=-B[2];
C[1]:=-C[1];
D2:=B*A*C^-1;

//Get first non-zero entry in D2
for i in [1..4] do
  spot:=nz[i];
  if D2[spot[1],spot[2]] ne 0 then break; end if;
end for;

u2:=D2[spot[1],spot[2]];
D2:=u2^-1*D2;

if D1 eq A or D2 eq A then

B:=H22![a,b,-w*b,a];
C:=F!(a^2+w*b^2)*H22![a,b,-w*b,a];

if D1 eq A then

C1:=u1^2*C;
D:=B*A2*C1^-1;

z1:=D[1][1];
D[1]:=D[1]-z1*v;
z3:=D[2][1];
D[2]:=D[2]-z3*v;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

if D2 eq A then

B[2]:=-B[2];
C[1]:=-C[1];
C2:=u2^2*C;

D:=B*A2*C2^-1;

z1:=D[1][1];
D[1]:=D[1]-z1*v;
z3:=D[2][1];
D[2]:=D[2]-z3*v;

z1:=Z!(D[1][1]);
z2:=Z!(D[1][2]);
z3:=Z!(D[2][1]);
z4:=Z!(D[2][2]);

ind1:=p^3*z1+p^2*z2+p*z3+z4;

if ind1 lt index then new:=0; end if;

end if;

end if;

if new eq 0 then break; end if;
end for;

if new eq 1 then
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b)=e^w,(d,a),(d,b)=f,(d,c),
   a^p=f^y2,b^p=f^y4,c^p=e^t1*f^t2,d^p=e^t3*f^t4>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end if;

end for;
end for;

end if;
end if;
end for;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of order";
vprint Orderp7, 2:"p^7 satisfying [c,a]=[b,a,b], [c,b]=[b,a,a]^w, [d,a]=1,";
vprint Orderp7, 2:"[d,b]=[b,a,b], [d,c]=1";

if p mod 12 eq 1 then vprint Orderp7, 2: "Total number of groups is 2p^2+(5/2)p+2+p^3/2 =",2*p^2+(5/2)*p+2+p^3/2; end if;
if p mod 12 eq 5 then vprint Orderp7, 2: "Total number of groups is 2p^2+(5/2)p+3+p^3/2 =",2*p^2+(5/2)*p+3+p^3/2; end if;
if p mod 12 eq 7 then vprint Orderp7, 2: "Total number of groups is 3p^2+(19/2)p+13+p^3/2 =",3*p^2+(19/2)*p+13+p^3/2; end if;
if p mod 12 eq 11 then vprint Orderp7, 2: "Total number of groups is 3p^2+(19/2)p+10+p^3/2 =",3*p^2+(19/2)*p+10+p^3/2; end if;

if Process then return Nmr; else return L; end if;

end function;

Group5_3h := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//This program computes presentations for groups from
//Case 8 in the descendants of 5.3
//[c,a]=[c,b]=[d,a]=[d,b]=1, [d,c]=[b,a,a]

class:=3;
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

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
             a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
             a^p,b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
             a^p,b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
             a^p,b^p=(b,a,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                 a^p=(b,a,a),b^p=(b,a,b)^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e,b^p=e^w*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=p+6;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f,b^p=e^x*f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f^w,b^p=e^x*f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p,b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p,b^p=e,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e|e=(b,a,a),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p,b^p=e^w,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p,b^p=(b,a,b),c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+4;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,a),b^p=(b,a,b)^x,c^p=(b,a,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=e,b^p=e*f,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=e,b^p=e^w*f,c^p=e,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+2;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f,b^p=e^x*f,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p=(b,a,a),c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p=(b,a,a)^w,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f^w,b^p=e^x*f,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p=(b,a,a),c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p=(b,a,a)^w,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
for y in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e*f^x,b^p=e*f^y,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e*f^x,b^p=e^w*f^y,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e,b^p=f^x,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e*f,b^p=f^x,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e*f^w,b^p=f^x,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+3;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=f^x,b^p=e*f,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
               a^p=f^x,b^p=e^w*f,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
for x in [1,w] do
for y in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f^y,b^p=e^x,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [0,1] do
for y in [0,1,w] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f^y,b^p=f^x,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
GR:=Group<a,b,c,d|(c,a),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p,b^p,c^p=(b,a,a),d^p=(b,a,b)>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p,b^p=f,c^p=e,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p,b^p=e,c^p=e,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p,b^p=e^w,c^p=e,d^p=f>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+4;
if p mod 4 eq 1 then
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                     a^p,b^p=e^w2,c^p=e,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                     a^p,b^p=e^w3,c^p=e,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=e,b^p=f^x,c^p=e,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in [1..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=e,b^p=e^x*f,c^p=e,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
for x in [0..p-1] do
for y in [0..((p-1) div 2)] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f,b^p=e^x*f^y,c^p=e,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a),(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f^w,b^p=e^x*f^y,c^p=e,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
end for;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of order";
vprint Orderp7, 2:"p^7 satisfying [c,a]=[c,b]=[d,a]=[d,b]=1, [d,c]=[b,a,a]";

vprint Orderp7, 2: "Total number of groups is 3p^2 + 14p + 37 + gcd(p-1,4) =",
3*p^2+14*p+37+Gcd(p-1,4);

if Process then return Nmr; else return L; end if;

end function;

Group5_3i := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

//This program computes presentations for groups from
//Case 9 in the descendants of 5.3
//[c,b]=[d,a]=[d,b]=1, [c,a]=[b,a,b], [d,c]=[b,a,a]

class:=3;
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
w4:=w^4 mod p;
w5:=w^5 mod p;
m2w:=((p-2)*w) mod p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
             a^p,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
             a^p,b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
             a^p,b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
             a^p,b^p=(b,a,b),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                 a^p=e,b^p=f^x,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e,b^p=e*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e,b^p=e^w*f,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=p+6;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b),b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f,b^p=e^x*f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p=(b,a,a),c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p=(b,a,b)^w,b^p=(b,a,a)^w,c^p,d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+3;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f^w,b^p=e^x*f,c^p,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p,b^p,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p,b^p=(b,a,a),c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p,b^p=(b,a,a)^w,c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                   a^p,b^p=(b,a,b),c^p=(b,a,a),d^p>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
count:=count+4;
if p mod 3 eq 1 then
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                     a^p,b^p=(b,a,b)^w,c^p=(b,a,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d|(c,a)=(b,a,b),(c,b),(d,a),(d,b),(d,c)=(b,a,a),
                     a^p,b^p=(b,a,b)^w2,c^p=(b,a,a),d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end if;
for x in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=e,b^p=f^x,c^p=e,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  if p mod 3 eq 1 then
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                       a^p=e^w,b^p=f^x,c^p=e,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                       a^p=e^w2,b^p=f^x,c^p=e,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end if;
end for;
if p mod 3 eq 1 then
  for i in [2..p-1] do
    if i^3 mod p eq 1 then CU:=i; break; end if;
  end for;
  for x in [1..p-1] do
    x1:=(CU*x) mod p; x2:=(CU*x1) mod p;
    if x le x1 and x le x2 then
     GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                        a^p=e,b^p=e^x*f,c^p=e,d^p>;
     ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
     GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                        a^p=e^w,b^p=e^x*f^w,c^p=e,d^p>;
     ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
     GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                        a^p=e^w2,b^p=e^x*f^w2,c^p=e,d^p>;
     ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
     count:=count+3;
    end if;
  end for;
else;
  for x in [1..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=e,b^p=e^x*f,c^p=e,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
end if;
if p mod 4 eq 1 then
  for i in [2..p-2] do
    if i^4 mod p eq 1 then QU:=i; break; end if;
  end for;
  for k in [1,w,w2,w3] do
  for x in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^k,b^p=e^x,c^p=e,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
  end for;
  for y in [1..((p-1) div 2)] do
    y1:=(QU*y) mod p; y2:=p-y1;
    if y le y1 and y le y2 then
      for k in [1,w,w2,w3] do
      for x in [0..p-1] do
      count:=count+1;
      GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                       a^p=f^k,b^p=e^x*f^y,c^p=e,d^p>;
      ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
      end for;
      end for;
    end if;
  end for;
else;
  for x in [0..p-1] do
  for y in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f,b^p=e^x*f^y,c^p=e,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^w,b^p=e^x*f^y,c^p=e,d^p>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
  end for;
end if;
for x in [0..p-1] do
for y in [0..p-1] do
for z in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=e*f^x,b^p=e^y*f^z,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end for;
for x in [0..p-1] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f^x,b^p=e^y*f,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [0,1,w] do
for y in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                   a^p=f^x,b^p=e^y,c^p=f,d^p>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
for x in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^x,b^p,c^p,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^x,b^p=e,c^p,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^x,b^p=e^w,c^p,d^p=e>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+3;
 if x ne p-2 then
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^x,b^p=e^y*f,c^p,d^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
 end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^x,b^p,c^p,d^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^x,b^p=e,c^p,d^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^x,b^p=e^w,c^p,d^p=e^w>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+3;
 if x ne m2w then
  for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=f^x,b^p=e^y*f,c^p,d^p=e^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
 end if;
end for;
for x in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=e*f^-2,b^p=e^x,c^p,d^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                     a^p=e*f^m2w,b^p=e^x,c^p,d^p=e^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;

for x in [0..p-1] do
if x ne p-2 then
for y in [0..p-1] do
for z in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
               a^p=f^x,b^p=e^y*f^z,c^p=f,d^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end if;
end for;

for x in [0..p-1] do
if x ne m2w then
for y in [0..p-1] do
for z in [0..((p-1) div 2)] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
               a^p=f^x,b^p=e^y*f^z,c^p=f,d^p=e^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;
end if;
end for;

for x in [0..((p-1) div 2)] do
for y in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e^x*f^-2,b^p=e^y,c^p=f,d^p=e>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e^x*f^m2w,b^p=e^y,c^p=f,d^p=e^w>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
end for;
end for;

for x in [0..p-1] do
for y in [0..p-1] do
for z in [0..p-1] do
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e^x*f,b^p=e^y*f^z,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
               a^p=e^x*f^w,b^p=e^y*f^z,c^p,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  count:=count+2;
end for;
end for;
end for;
if p mod 4 eq 1 then
  for x in [1,w,w2,w3] do
  for y in [0..((p-1) div 2)] do
  for z in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                a^p=e^x,b^p=e^y*f^z,c^p,d^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
  end for;
  end for;
else;
  for x in [1,w] do
  for y in [0..p-1] do
  for z in [0..p-1] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                a^p=e^x,b^p=e^y*f^z,c^p,d^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
  end for;
  end for;
end if;
if p mod 4 eq 1 then
  for x in [0..((p-1) div 2)] do
  for y in [1,w,w2,w3] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                a^p,b^p=e^x*f^y,c^p,d^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
  end for;
else;
  for x in [0..p-1] do
  for y in [1,w] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                a^p,b^p=e^x*f^y,c^p,d^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
  end for;
end if;
if p mod 3 eq 1 then
  for x in [0,1,w,w2,w3,w4,w5] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                a^p,b^p=e^x,c^p,d^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
else;
  for x in [0,1,w] do
    count:=count+1;
    GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                a^p,b^p=e^x,c^p,d^p=f>;
    ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
  end for;
end if;
if p mod 5 eq 1 then
 for i in [2..p-1] do
   if i^5 mod p eq 1 then FI:=i; break; end if;
 end for;
 T5:={};
 for i in [1..p-1] do
   i2:=(FI*i) mod p; i3:=(FI*i2) mod p; i4:=(FI*i3) mod p; i5:=(FI*i4) mod p; 
   if i le i2 and i le i3 and i le i4 and i le i5 then
     Include(~T5,i);
   end if;
 end for;
 for k in [1,w,w2,w3,w4] do
 for x in T5 do
 for y in [0..p-1] do
 for z in [0..p-1] do
 for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
             a^p=e^x*f^y,b^p=e^z*f^t,c^p=e^k,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
 end for;
 end for;
 end for;
 end for;
 end for;
 for k in [1,w,w2,w3,w4] do
 for y in T5 do
 for z in [0..p-1] do
 for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
             a^p=f^y,b^p=e^z*f^t,c^p=e^k,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
 end for;
 end for;
 end for;
 end for;
 for k in [1,w,w2,w3,w4] do
 for z in T5 do
 for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
             a^p,b^p=e^z*f^t,c^p=e^k,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
 end for;
 end for;
 end for;
 for k in [1,w,w2,w3,w4] do
 for t in T5 do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
             a^p,b^p=f^t,c^p=e^k,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
 end for;
 end for;
 for k in [1,w,w2,w3,w4] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
                   a^p,b^p,c^p=e^k,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
 end for;
else;
 for x in [0..p-1] do
 for y in [0..p-1] do
 for z in [0..p-1] do
 for t in [0..p-1] do
  count:=count+1;
  GR:=Group<a,b,c,d,e,f|e=(b,a,a),f=(b,a,b),(c,a)=f,(c,b),(d,a),(d,b),(d,c)=e,
             a^p=e^x*f^y,b^p=e^z*f^t,c^p=e,d^p=f>;
  ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);
    if limited and Nmr ge Limit then return L; end if;
 end for;
 end for;
 end for;
 end for;
end if;

vprint Orderp7, 2:"There are",count,"four generator p-class three groups of order";
vprint Orderp7, 2:"p^7 satisfying [c,b]=[d,a]=[d,b]=1, [c,a]=[b,a,b], [d,c]=[b,a,a]";

vprint Orderp7, 2: "Total number of groups is p^4+4p^3+7p^2+14p+10+(p+3)gcd(p-1,3)+(p+2)gcd(p-1,4)+gcd(p-1,5) =",
p^4+4*p^3+7*p^2+14*p+10+(p+3)*Gcd(p-1,3)+(p+2)*Gcd(p-1,4)+Gcd(p-1,5);

if Process then return Nmr; else return L; end if;

end function;

Group5_3 := function (p: Process:=true, Select:=func<x|true>, Limit:=0)

   if p lt 5 then print "5.3 valid only for p>3"; return false; end if;

   limited := not Process and Limit ge 1;
   L := []; count := 0; lim := 0;
   M := Group5_3a (p: Process:=Process, Select:=Select, Limit := Limit);
   Append (~L, M);
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;
   M := Group5_3b (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;
   M := Group5_3c (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;
   M := Group5_3d (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;
   M := Group5_3e (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;
   M := Group5_3f (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;
   M := Group5_3g (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M);
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;
   M := Group5_3h (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M); 
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;
   M := Group5_3i (p: Process:=Process, Select:=Select,Limit:=lim);
   Append (~L, M); 
   if limited then count +:= #M;
    if count ge Limit then return &cat L; end if;
    lim := Limit-count;
   end if;

   if Process eq true then L := &+L; Nmr := L; end if;
   if Process eq false then L := &cat (L); Nmr := #L; end if;

   vprint Orderp7, 2: "Sequence of groups has length", Nmr;

   vprint Orderp7, 2: "Group 5.3 has p^4+5p^3+19p^2+64p+140+(p+6)gcd(p-1,3)+(p+7)gcd(p-1,4)+gcd(p-1,5) =",
       p^4+5*p^3+19*p^2+64*p+140+(p+6)*Gcd(p-1,3)+(p+7)*Gcd(p-1,4)+Gcd(p-1,5),
          "immediate descendants of order p^7";

   return L;
end function;

Children41 := function (p: Process:=true, Select:=func<x|true>)
   return Group5_3 (p: Process := Process, Select := Select);
end function;

