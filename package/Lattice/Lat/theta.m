freeze;

/*
THETA SERIES OF LATTICES
  AKS, 
*/

declare verbose Theta, 2;

Q := RationalField();

////////////////////////////////////////////////////////////////////////////////

// NOTE: always return series with coefficients up to and including n

function ThetaSeriesSub
(L, n, TimeLimit: ExponentConstant:=1, TimeLimitExtra := 0,
 Prune := [1.0:i in [1..Dimension(L)]] )
/* TimeLimit = 0 => normal (no limit).
   Returns whether full (limit not hit), then full/partial theta series. */

 function GetThetaSeriesIntegral2(L, n: Prune := [1.0:i in [1..Dimension(L)]] )
  if TimeLimitExtra gt 0 and TimeLimit gt 0 then
   return ThetaSeriesIntegralLimited(L, n, TimeLimit, TimeLimitExtra);
   elif TimeLimit gt 0 then
    return ThetaSeriesIntegralLimited(L, n, TimeLimit); end if;
  return true, ThetaSeriesIntegral(L, n: Prune:=Prune); end function;

 function GetThetaSeriesIntegral(L,n : Prune := [1.0:i in [1..Dimension(L)]] )
  if IsEven(L) and IsOdd(n) then
   b,f:=GetThetaSeriesIntegral2(L,n-1 : Prune:=Prune); ChangePrecision(~f,n+1);
  else b,f:=GetThetaSeriesIntegral2(L,n : Prune:=Prune); end if;
 return b,f; end function;

    if IsIntegral(L) then Z:=Integers(); bool,eci:=IsCoercible(Z,1/ExponentConstant);
      error if not bool, "ExponentConstant not valid: must be 1/m for an integer m";
      full, T := GetThetaSeriesIntegral(L, (n+1)*eci-1 : Prune:=Prune);
      if eci eq 1 then assert AbsolutePrecision(T) eq n+1; return full,T;  end if;
      T:=PuiseuxSeriesRing(Z)!T; ChangeExponentDenominator(~T,eci); 
      assert AbsolutePrecision(T) eq n+1; 
      T:=T+O(Parent(T).1^(n+1)); // TO DO: coercion fails without this
      bool,T:=IsCoercible(PowerSeriesRing(Z),T); error if not bool, 
      "ExponentConstant not valid: theta series does not have integral exponents";
      return full,T; end if;

    // The gram matrix for L is not integral
    error if ExponentConstant ne 1,
     "Parameter ExponentConstant is not available for non-integral lattices";
    LL, d := IntegralBasisLattice(L);
    s := d^2;
    full, T := GetThetaSeriesIntegral(LL, n*s: Prune:=Prune); 
    coeffs := [Coefficient(T,i) : i in [0.. n*s]];
    if exists(dummy){i : i in [0.. n*s] | (i mod s) ne 0 and coeffs[i+1] ne 0} then
       S := PuiseuxSeriesRing(Integers());
       ans := &+[ coeffs[i+1] * S.1^(i/s) : i in [0.. n*s]] + O(S.1^(n+1/s));
    else
       S := PowerSeriesRing(Integers());
       ans := &+[ coeffs[i*s+1] * S.1^i : i in [0..n]] + O(S.1^(n+1));
    end if;
    return full, ans;
end function;

intrinsic ThetaSeries(L::Lat, n::RngIntElt : ExponentConstant:=1, Prune:=[1.0:i in [1..Dimension(L)]] ) -> RngSerElt
{The theta series of lattice L to precision n}

    requirege n, 0;
    require Rank(L) ge 1: "Argument 1 must be non-zero";
    if Type(Prune) ne Infty then 
      require #Prune eq Rank(L): "The length of Prune must be the rank of argument 1";
      require forall{i: i in [1..Rank(L)] | Prune[i] ge 0.0 and Prune[i] le 1.0}:       "The elemements of Prune must be in [0.0, 1.0]"; 
    end if;  


    full, theta := ThetaSeriesSub(L, n, 0: ExponentConstant:=ExponentConstant, Prune:=Prune );
    assert full;
    return theta;

end intrinsic;

intrinsic ThetaSeriesLimited(
			     L::Lat, n::RngIntElt, TimeLimit::RngIntElt : ExponentConstant:=1, Prune := [1.0:i in [1..Dimension(L)]]
) -> RngSerElt
{Attempt to compute the theta series of integral lattice L to precision n
with time limit TimeLimit; if the full series is computed, return true and the 
series, otherwise return false and a series whose coefficients are lower
bounds for the correct coefficients.}

    requirege n, 0;
    require Rank(L) ge 1: "Argument 1 must be non-zero";
    if Type(Prune) ne Infty then 
      require #Prune eq Rank(L): "The length of Prune must be the rank of argument 1";
      require forall{i: i in [1..Rank(L)] | Prune[i] ge 0.0 and Prune[i] le 1.0}:       "The elemements of Prune must be in [0.0, 1.0]"; 
    end if;  


    full, theta := ThetaSeriesSub(
				  L, n, TimeLimit: ExponentConstant:=ExponentConstant, Prune:=Prune
    );
    return full, theta;

end intrinsic;

intrinsic ThetaSeriesLimited(
    L::Lat, n::RngIntElt, TimeLimit::RngIntElt, TimeLimitExtra::RngIntElt:
    ExponentConstant:=1, Prune := [1.0:i in [1..Dimension(L)]]
) -> RngSerElt
{Attempt to compute the theta series of integral lattice L to precision n
with time limit TimeLimit; if the full series is computed, return true and the 
series, otherwise return false and a series whose coefficients are lower
bounds for the correct coefficients.}

    requirege n, 0;
    require Rank(L) ge 1: "Argument 1 must be non-zero";
    if Type(Prune) ne Infty then 
      require #Prune eq Rank(L): "The length of Prune must be the rank of argument 1";
      require forall{i: i in [1..Rank(L)] | Prune[i] ge 0.0 and Prune[i] le 1.0}:       "The elemements of Prune must be in [0.0, 1.0]"; 
    end if;  


    full, theta := ThetaSeriesSub(
	L, n, TimeLimit:
	TimeLimitExtra := TimeLimitExtra, ExponentConstant:=ExponentConstant,
	Prune:=Prune
    );
    return full, theta;

end intrinsic;
