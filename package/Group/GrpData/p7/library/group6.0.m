freeze;

import "misc.m": ProcessPresentation; 

Group6_0 := function (p: Process:=true, Select:=func<x|true>)

class:=7;

vprint Orderp7, 2:"p equals",p;

L:=[]; Nmr := 0;
GR:=Group<a|>;
ProcessPresentation (~L, GR, p, class, ~Nmr: Process := Process, Select := Select);

vprint Orderp7, 2:"There is one cyclic group of order p^7";

vprint Orderp7, 2: "Total number of groups is 1";

if Process then return Nmr; else return L; end if;

end function;
