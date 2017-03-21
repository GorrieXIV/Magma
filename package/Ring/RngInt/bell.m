freeze;

/*
Computation of Bell numbers via Dobinski sum.
Modified version of submission by Fred Lunnon (2007-08-02).
*/

intrinsic Bell(n::RngIntElt) -> RngIntElt
{The n-th Bell number}
    requirege n, 0;

    // compute the desired precision
    LP := RealField(10);
    expn := Exp(LP!n);
    i := 0;
    while (LP!i)^i le expn do
	i +:= 1;
    end while;
    i_0 := i - 1;	// approximate index of last term

    // required bits = Log(2, max term * number of terms)
    bits := (n^2/i_0 - n + i_0 + n/i_0) / Log(LP!2);
    prec := Max(10, Round(bits));
    HP := RealField(prec : Bits);	// high precision infinite sum

    bell := HP!0;
    faci := HP!1;
    i := 0;
    repeat
	i +:= 1;
	faci *:= i;
	term := (HP!i)^n / faci;
	bell +:= term;
    until term le 0.1;		// terms << unity ignored

    return Round(bell / Exp(HP!1));
end intrinsic;
