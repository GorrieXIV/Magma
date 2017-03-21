freeze;
////////////////////////////////////////////////////////////////////////
//                                                                    //  
//       Uses the exact values for n<=8 and n=24.                     //
//       Uses Mordell's inequality for n=9 and n=25.                  //
//       Uses the n-dim volume otherwise.                             //  
//                                                                    // 
////////////////////////////////////////////////////////////////////////

intrinsic HermiteConstant(n::RngIntElt) -> RngElt
  {The n-th Hermite constant to the power n for quadratic forms (or upper bounds for them if n>8)}

  gammatothed := [1, 4/3, 2, 4, 8, 64/3, 64, 256];
  if n le 8 then
    return gammatothed[n];
  end if;
  if n eq 9 then 
    return 1248.2699819053828515;
  end if;
  if n eq 24 then 
    return 4^24;
  end if;
  if n eq 25 then 
    return 5080574419771171.3259;
  end if;
  return Gamma((n+4)/2)^2*(2/Pi(GetDefaultRealField()))^n;
end intrinsic;


