freeze;

IncorporateCentralisingGenerators := procedure(GQ, ~GQnew, C, ~prgens)
    X := RandomSchreierCoding(GQnew:Run:=5);
    if &*BasicOrbitLengths(X) eq #GQ then
	return;
    end if;
    P1 := RandomProcess(GQnew);
    P2 := RandomProcess(C);
    repeat
	c := Random(P2);
	x := c*Random(P1);
	flag, res, lev := Strip(X, x);
	if flag then
	    continue;
	end if;
	if lev gt #Base(X) then
	    assert lev eq #Base(X) + 1;
	    flag := exists(p){p:p in Labelling(GQ)|p^res ne p};
	    assert flag;
	    AppendBasePoint(~X, p);
	end if;
	AddStrongGenerator(~X, res, ~n);
	UpdateLevels(~X, n, 1, lev);
	GQnew := sub<GQ|GQnew, c>;
	Append(~prgens, 1);
    until &*BasicOrbitLengths(X) eq #GQ;
    GQnew`Order := #GQ;
end procedure;
