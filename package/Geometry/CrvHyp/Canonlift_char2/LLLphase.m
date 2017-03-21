freeze;

/***********************************************************

  Functions to compute the minimal polynomial (over Q) of
  the modular parameter beta, which is input to a high
  2-adic precision. Uses an LLL method.
  Also contains a special case function for genus 2 which
  computes the full characteristic polynomial of frobenius
  directly from the 2-adic approximation to beta.
     Mike Harrison 01/2004.
  
***********************************************************/

/* NB:  To compute the minimal poly of beta, we compute beta
       2-adically to precision f(g)*n + LLLconst(g) with LLLconst
       as below, g is the genus and the base filed is GF(2^n).
       The implementation here uses the function 
         f(g) = 2^(2*g-3) * (g-2) + 2^(g-1) - 1 for g>2
       rather than the smaller one suggested by Lercier.
       For this f, I can prove that all "small" vectors
       coming from the LLL computation below DEFINITELY give a
       polynomial divisible by the min poly of beta. */
       
function LLLconst(g)

    G := 2^(g-1);
    if IsEven(g) then
       E := (&+[(Binomial(G,i)*(2^i))^2 : i in [0..G]])*(2/3);
    else       
       E := 1 + &+[(4-2*(i mod 2))*(Binomial(G,i)*(2^(i-1)))^2 : i in [1..G]];
    end if;
    return G^2 + (G div 2) + Ceiling((G div 2)*Log(2,E));
    
end function;

function BetaPrecision(g,n)

    if g eq 2 then return 2*n+4; end if;
    arr := [39,159,645,2602];
    prec0 := (2^(2*g-3) * (g-2) + 2^(g-1) - 1) * n;
    if g le 6 then 
        return prec0+arr[g-2];
    else
        return prec0+LLLconst(g);
    end if;

end function;

function Genus2CharPoly(beta,q)

  //NB. Assumption that q >= 16 is made.

  b1 := beta mod q;
  u1 := ((b1-beta) div q)*beta + 3*q;
  i := (((2-u1)*b1) mod 8);
  if i ge 4 then i -:= 8; end if;
  u1 := (u1+i*beta) mod (16*q);
  PI := PolynomialRing(IntegerRing()); x := PI.1;
  polq := x^2+q;
  posspols := [PI|];
  for sgn in [1,-1] do
    b := sgn*(b1+i*q);
    a2 := (u1+2*b) mod (16*q);
    // i chosen s.t. a2 = (b+1)^2 mod 16.
    boo := (a2 ge 4*b) and (4*q*a2 lt (4*q+b)^2);
    if boo then
        boo1,a := IsSquare(a2);
        if boo1 then
          Append(~posspols,polq^2+a*polq*x+b*x^2);
          if a ne 0 then
            Append(~posspols,polq^2-a*polq*x+b*x^2);
          end if;
        end if;
    end if;
  end for;
  assert #posspols gt 0;
  return posspols;
  
end function;

function MinPolyFromBeta(beta,q,g)

  G := 2^(g-2);
  n := Valuation(q,2);
  m := BetaPrecision(g,n);
  Gamma := (q^(G*(g-2)+1))*(2^(g-1))*
                   Maximum([(2^i)*Binomial(2*G,i): i in [1..2*G]]);
  G *:= 2;
  M := RMatrixSpace(IntegerRing(),G+2,G+2)!0;
  eta := ResidueClassRing(2^m)!beta;
  prod := Parent(eta)!1;
  for i in [1..G] do
    x := Intseq(IntegerRing()!prod,2);
    M[i,1] := Gamma * Seqint([0 : j in [1..n*(G-i)]] cat
                 [x[j] : j in [1..Min(m-n*(G-i),#x)]],2);
    prod := prod * eta;
  end for;
  M[G+1,1] := Gamma * IntegerRing()!prod;
  M[G+2,1] := Gamma * (2^m);
  for i in [1..G] do
    M[i,G+3-i] := 2^((n*(i-1)*(g-2)) div 2);
  end for;
  M[G+1,2] := q^(((G div 2)*(g-2))+1);
  L := LatticeWithBasis(M: CheckIndependent := false);
  vprint JacHypCnt,4 : "Getting shortest vectors...";
  vecs := ShortestVectors(L);
  vprintf JacHypCnt,4 : "Found %o.\n",#vecs;
  PolI := PolynomialRing(IntegerRing());
  pols := [PolI|];
  for i in [1..#vecs] do
    coeffs := Eltseq(vecs[i]);
    j := 1;
    while coeffs[j] eq 0 do j +:= 1; end while;
    if j eq 1 then
       error "LLL phase error!\n";
    end if;
    coeffs := [coeffs[k] div M[G+3-k,k] : k in [j..G+2]];
    if coeffs[1] ne (j eq 2 select 1 else q) then
//printf "Ignoring vector %o.\n",i;
    else
      coeffs := [1] cat [coeffs[k]*q^(k-2) : k in [2..#coeffs]];
      Append(~pols,PolI!Reverse(coeffs));
    end if;
  end for;
  if #pols eq 0 then 
    error "LLL phase failure!\n";
  end if;
  posspols := {PolI|};
  for poly in pols do
    facts := Factorization(poly);
    posspols := posspols join {p : f in facts | 
      IsOdd(Coefficient(p,Degree(p)-1))  where p is f[1]};
    //NB. For each poly, only 1 factor will satisfy the above condition.
  end for;
  if #posspols gt 1 then
    posspols := { p : p in posspols | Evaluate(p,eta) eq 0 };
    if #posspols gt 1 then
      error "LLL phase gives multiple answers!\n";
    end if;
  end if;
  vprint JacHypCnt,4 : "Found unique possibility";
  return Rep(posspols);

end function;
