freeze;

function cremona_cost(I,J,type)
 x:=PolynomialRing(Rationals()).1; R:=Roots(x^3-3*I*x+J,RealField());
 if type eq 1 then r3,r2,r1:=Explode([r[1] : r in R]); A:=(r1-r3)/9; H:=0;
  for a in [1..Floor(A)] do
   Hmax:=Min(4*a*r1,4*a*r3+(4/3)*(r3^2-I)); Hmin:=4*a*r2;
   H+:=Max(Hmax-Hmin,0)*a; // b factor
   Hmax:=Min(4*-a*r3,4*-a*r1+(4/3)*(r1^2-I)); Hmin:=4*-a*r2;
   H+:=Max(Hmax-Hmin,0)*a; // b factor
  end for; return H; end if;
 if type eq 2 then r3,r2,r1:=Explode([r[1] : r in R]); A:=(r1-r3)/9; H:=0;
  for a in [1..Floor(A)] do
   Hmax:=4*a*r3; Hmin:=4*a*r2+(4/3)*(r2^2-I); H+:=Max(Hmax-Hmin,0)*a;
   Hmax:=4*-a*r1; Hmin:=4*-a*r2+(4/3)*(r2^2-I); H+:=Max(Hmax-Hmin,0)*a;
   end for; return H; end if;
 if type eq 3 then r:=R[1][1]; H:=0;
  if r gt 0 then lower:=-Sqrt((r^2-4*I)/27);
   A:=(2*Sqrt(r^2-I)+Sqrt(r^2-4*I))/Sqrt(108);
   upper:=Min(A,Max((r+Sqrt(r^2-4*I))/6,2*(r^2-I)/(9*r)));
  elif r eq 0 then upper:=Sqrt(-4*I/27); lower:=-upper;
  else upper:=Sqrt((r^2-4*I)/27);
   A:=(2*Sqrt(r^2-I)+Sqrt(r^2-4*I))/Sqrt(108);
   lower:=Min(-A,Max((r-Sqrt(r^2-4*I))/6,2*(r^2-I)/(9*r))); end if;
  B:=(2/3)*Sqrt(r^2-4*I); //"B",B;
  for a in [Ceiling(lower)..Floor(upper)] do
   u:=4*(r^2-I)-27*a^2; // a,u;
   if u lt 0 then continue; end if;
   Ba:=B*Sqrt(4*(r^2-I)-27*a^2); // Cremona typo ? "Ba",Ba;
   Hmax:=Min(4*a*r,-2*a*r+Ba); Hmin:=Max(4*a*r-(4/3)*(r^2-I),-2*a*r-Ba);
   H+:=Max(Hmax-Hmin,0)*Abs(a); end for; return H; end if;
 end function;

function guess_cremona_time(E)
 c4,c6:=Explode(cInvariants(MinimalModel(E)));
 if Discriminant(E) gt 0 then // factor of 2 for egg
  C1:=cremona_cost(c4,2*c6,1)/2; C2:=cremona_cost(c4,2*c6,2); C:=C1+C2;
 else C:=cremona_cost(c4,2*c6,3); end if;
 if Valuation(c4,2) ge 2 and Valuation(2*c6,2) ge 3 and 
  Valuation(2*c4+2*c6,2) ge 4 then; // factor of 2 for large quartics
 else C:=C*2; end if; return C/3/10^10; end function;

