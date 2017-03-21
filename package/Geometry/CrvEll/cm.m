freeze;

///////////////////////////////////////////////////////////////////////
//         Functions related to Complex Multiplication               //
//             for Elliptic Curves.                                  //
//                 Mike Harrison 11/04                               //
///////////////////////////////////////////////////////////////////////


//////         Functions to determine whether E defined           /////
//     over a number field has CM and, if so, by which quad order    //

function CMTest(f)

/* 
   f is a monic irreducible polynomial over Z.
   Function determines whether the roots are the
   j-invariants of elliptic curves with CM and if so
   returns -D, the discriminant of the CM order
*/

  // handle special case of rational j-invariant using known list
  if Degree(f) eq 1 then
	j := -Coefficient(f,0);
	j_invs := \[0,1728,-3375,8000,-32768,54000,287496,-884736,-12288000,
		     16581375,-884736000,-147197952000,-262537412640768000];
        discs := \[3,4,7,8,11,12,16,19,27,28,43,67,163];
	idx := Index(j_invs,j);
	if idx eq 0 then
	    return false,_;
	else
	    return true,-discs[idx];
	end if;
  end if;

  // First find an approx to the real roots of f
     // -- get an upper bound of Log_10(rt) - Zassenhaus' bound?
  bd := Max([ (Log(10,Abs(c[n+1-i]))-Log(10,Binomial(n,i)))/i : i in [1..n] |
		c[n+1-i] ne 0] ) - Log(10,Root(2,n)-1)
	  where c := Coefficients(f) where n is Degree(f);
  if bd le 5.0 then // a lower bound for non-rat maximal real CM j-invariants
	return false,_;
  end if;
  rts := RealRoots(f,RealField(4*Ceiling(bd/4)+4),0.0001);
   // #rts must be a power of 2
  if (#rts eq 0) or (#rts ne 2^Valuation(#rts,2)) then
	return false,_;
  end if;
  
  // find appropriate root
  rt := Max(rts);  
  if rt le 1729 then
	boo3 := true; // case 1 : poss D = 3 mod 4
	rt := -Min(rts); // rt ~ -j((1+sqrt(-D))/2)
        if rt lt 191650 then return false,_; end if;
  else
	boo3 := false; // case 2:  poss D = 4*d,  rt ~ j(sqrt(-d))
	if rt lt 1264530 then return false,_; end if;	    
  end if;
  
  // Now use the fact that j(z) = q + 744 + (err) * |q| ^(-1)
  //    where |err| < 5000000 and q is exp(2*pi*i*z)
  //    [ assuming that |q| < (1/100) ]
  // This gives:
  //  j(sqrt(-d)) = exp(2*pi*sqrt(d)) + 744 + err with 0 < err < 4
  //                  if d >= 5 and
  //  j((1+sqrt(-D))/2) = -exp(pi*sqrt(D)) + 744 + err with |err| < 26
  //                  if D >= 15
  //
  // In case 2 we get d = (log(j)/2*pi)^2 - err with 0 < err < 0.0005
  // In case 1 we get D = (log(-j)/pi)^2 + err with 0 < err <  0.01

  pi := Pi(Parent(rt));
  if not boo3 then pi *:= 2; end if;  
  d_val := (Log(rt)/pi)^2;
  pot_d := Round(d_val);

  // do some relatively quick checks on the potential D
  err_bd := (pot_d eq 15) select 0.01 else 0.001;  
  if Abs(d_val-pot_d) ge err_bd then
	return false,_;
  end if;
  if boo3 and ((pot_d mod 4) ne 3) then
	return false,_;
  end if;
  D := boo3 select pot_d else 4*pot_d;
  if ClassNumber(-D) ne Degree(f) then
	return false,_;
  end if;

  // finally test that the potential D value gives the right j-invt
  f_j := Parent(f)!HilbertClassPolynomial(-D);
  if (f eq f_j) then
	return true,-D;
  else
	return false,_;
  end if;

end function;

intrinsic HasComplexMultiplication(E::CrvEll) -> BoolElt, RngIntElt
{  Determines whether E (defined over Q or a number field) has CM
   or not. If it does, also returns the discriminant  of the quadratic 
   order of CM. }

    require (typ eq FldRat) or ISA(typ,FldNum) where
		typ is Type( BaseRing(E) ) :
	"E must be defined over the rationals or a number field";
    f := AbsoluteMinimalPolynomial(jInvariant(E));
    if &and[IsIntegral(c) : c in Coefficients(f)] then
	return CMTest(PolynomialRing(Integers())!f);
    else
	return false,_;
    end if;

end intrinsic;
