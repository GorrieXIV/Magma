freeze;

import "misc.m": ProcessPresentation;
 
Group7_1 := function (p: Process:=true, Select:=func<x|true>)

class:=1;

vprint Orderp7, 2:"p equals",p;

L:=[]; Nmr := 0;
GR:=Group<a,b,c,d,e,f,g |>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 1:"There is one seven generator group of order p^7 and p-class 1";

vprint Orderp7, 2: "Total number of groups is 1";

if Process then return Nmr; else return L; end if;

end function;
