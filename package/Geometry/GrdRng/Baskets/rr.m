freeze;
 
/*
i want to make a big rr formula that recognise sings and applies
the right correction term so that i can make weak fanos.
*/

forward terminal_contribution;
intrinsic Contribution(p::GRPtS,n::RngIntElt) -> FldRatElt
{}
    if not assigned p`C then
	p`C := [ Rationals() | ];
    end if;
    n mod:= Index(p);
    C := p`C;
    if n eq 0 then
	return 0;
    elif not IsDefined(C,n) then
	if IsTerminalThreefold(p) then
	    C[n] := terminal_contribution(1,p,n);
	    p`C := C;
	elif IsCanonicalThreefold(p) then
	    p`C := Contributions(p);
	else
	    require false: "Formula for RR contribution is missing";
	end if;
    end if;
    return (p`C)[n];
end intrinsic;

/////////////////////////////////////////////////////////////////////

// The corrections to RR for nA (n modulo r) coming from the
// singularity p = 1/r(a,b,c).
forward i_is, inv, bar;
function terminal_contribution(f,p,n)
    r := Index(p);
    P := TerminalPolarisation(p);               // P is [f,a,b] where b = r - a.
    a := inv(P[1],r) * P[2] mod r;      // if p=1/r(f,a0,b0), I want a = a0/f
    i := i_is(f,r,n);
    b := inv(a,r);
    first := -i*(r^2-1)/(12*r);
    if i in {0,1} then
        extra := 0;
    else
        extra := &+[ bar(b*j,r)*(r-bar(b*j,r))/(2*r) : j in [0..i-1] ];
    end if;
    return first + extra;
end function;

function i_is(f,r,n)
    h,u,v := XGCD(f,r);
    return (-n*u) mod r;
end function;

bar := func< m,r | m mod r >;

inv := func< a,r | i_is(a,r,1) >;

