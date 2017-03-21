freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  MESTRE LERCIER/LUBICZ ALGORITHM                   //
//                      Mike Harrison  01/2004                        //
//             Mestre's generalised AGM method to compute             //
//             the characteristic polynomial of Frobenius             //
//               on Jacobians of ordinary hyperelliptic               //
//                   curves in characteristic 2.                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

/***********************************************************************
Change Log:

10/06: In the case that everything works up until the very last stage,
but it's impossible to get down to a unique minimal polynomial (usually
because of a bad Jacobian decomposition and further bad luck with the
orders of twists of the factors - generally will only occur over
fairly small fields), try to narrow down further by computing #C(F_q^i)
for some small fields (i < genus obviously, or we could have used
the naive counting method originally!). [mch]

12/06: DropDegree function fixed. [mch]

***********************************************************************/

import "lifting.m": LiftMain;
import "LLLphase.m"  : MinPolyFromBeta,Genus2CharPoly,BetaPrecision;
import "symtofrob.m" : PsymToFrob;
import "../kedlaya_char2.m" : KedlayaChar2;


/* Called when C/K is a hyperelliptic curve with a Jacobian group
   law, but we need a model of C/F where F is an extn of K of even
   degree which still has a group law.
   (the problem case is for g even > 2 when C has no points at infty
     - C/F will have 2 points at infty).
    We use the fact that C/F IM to C1/F where
       C1: y^2+h1*y = h1*f where h1 = product(x-r : r in rts)
    and transform C1 to have 1 point at infty.
*/
function ReModel(C,rts,f,F)

  _,h := HyperellipticPolynomials(C);
  g := #rts-1;
  if (Degree(h) eq g) or (g eq 2) then 
    return BaseChange(C,F);
  end if;
  x := Parent(f).1;
  r := rts[#rts];
  h1 := &*[(rts[i]+r)*x + 1 : i in [1..g]];
  f1 := Parent(f)!Reverse(Coefficients(Evaluate(f,x+r))) * 
                    x^(g+1-Degree(f));
  return HyperellipticCurve([f1*h1,h1]);
  
end function;

function CheckAndLift(C)

  g := Genus(C);
  f,h := HyperellipticPolynomials(C);
  d1 := Degree(h); d2 := Degree(f);
  F := BaseRing(Parent(h));
  if d1 eq g then
    x := Parent(h).1;
    if Coefficient(h,0) eq 0 then
      for i in [1..#F] do
        fldelt := elt<F | Intseq(i,2)>;
        if Evaluate(h,fldelt) ne 0 then
          h := Evaluate(h,x+fldelt);
          f := Evaluate(f,x+fldelt);
          break;
        end if;
      end for;
    end if;
    h := x * Parent(h)!Reverse(Coefficients(h));
    f := Parent(h)!Reverse(Coefficients(f));
    if d2 eq 2*g+1 then
      f := x*f;
    end if;
  end if;
  if LeadingCoefficient(h) ne F!1 then
    f := f/LeadingCoefficient(h)^2;
    h := h/LeadingCoefficient(h);
  end if;
  rts,F := RootsInSplittingField(h);
  rts := [a[1] : a in rts];
  PolR := PolynomialRing(F); x := PolR.1;
  h := PolR!h; f := PolR!f;
  partprod := PolR!1;
  for i in [1..#rts] do
    /* at the start of the loop, partprod = (x-rts[1])*..(x-rts[i-1])
       and the curve has eqn. y^2+h(x)*y=partprod*f(x).
       The loop effects a transformation of the form y -> y+partprod*r
       where r=0 or a suitable linear polynomial in x
    */
    val := Evaluate(f,rts[i]);
    if val ne 0 then
      f := f-r*(h+partprod*r) where r is x-rts[i]+SquareRoot(val/
        ((i eq 1) select 1 else &*[rts[i]-rts[j] : j in [1..(i-1)]]));
    end if;
    f := f div (x-rts[i]);
    partprod := partprod * (x-rts[i]);
  end for;
  // new eqn of C is y^2+h(x)*y=h(x)*f(x)
  return rts,f,F;
 
end function;

function NormComp(taus,g,q,booGNB)

    E := (&+[a^2 : a in taus] +1) div 2^g;
    if booGNB then
        E := 1 div Norm(E);
    else
        E := Exp(-Trace(Log(E)));
    end if;
    return ( (g eq 2) select IntegerRing()!E else
                 IntegerRing()!(E + ((q^g) div E)) );
    
end function;

function EliminateAndVerify(C,charpols)

   vprintf JacHypCnt,2 :
    "Found %o possible characteristic polynomials over GF(2^%o).\n",
                  #charpols,Valuation(#BaseRing(C),2);
   vprint JacHypCnt,2 :
       "Performing random point tests to eliminate...";
   testcnt := 0;
   J := Jacobian(C);
   ords := [ &+Coefficients(pol) : pol in charpols];
   passed := [1..#charpols];
   // find the correct characteristic polynomial
   while #passed gt 1 do
       if testcnt gt 20 then
           return [charpols[j] : j in passed];
       end if;
       P := Random(J);
       for i := #passed to 1 by -1 do
         if ords[passed[i]]*P ne J!0 then
            Remove(~passed,i);
         end if;
       end for;
       testcnt +:=1;
   end while;
   if #passed ne 1 then
       error "No valid frobenius characteristic polynomial found!\n";
   end if;
   // do extra tests if required (3 in all)
   vprint JacHypCnt,2 : "Found the unique possibility.";
   if testcnt lt 3 then
     vprintf JacHypCnt,2 :
     "Performing an extra %o random tests for validation...\n",3-testcnt;
   end if;
   ord := ords[passed[1]];
   for i in [testcnt..2] do   
       P := Random(J);
       if ord*P ne J!0 then
           error "No valid frobenius characteristic polynomial found!\n";
       end if;
   end for;
   vprint JacHypCnt,2 : "Polynomial validated.";
   return [charpols[j] : j in passed];

end function;

function DropDegree(C,charpols,n)

   vprintf JacHypCnt,2 :
       "Descending to original base field, GF(2^%o)\n",
                                     Degree(BaseRing(C));
   powx := (Parent(charpols[1]).1)^n;
   finalpols := [];
   for cpol in charpols do
     facts := Factorization(cpol);
     posspols := [Parent(cpol)!1];
     for fact in facts do
        factrts := {a[1] : a in Factorization(Evaluate(fact[1],powx))};
        //assert IsOdd(n) or IsEven(#factrts);
        mult_deg := fact[2]*Degree(fact[1]);
	goodsets := [Setseq(q) : q in tmp | &+[Degree(e) : e in q] eq mult_deg]
		where tmp is &join[Subsets(factrts,i) : i in [1..fact[2]]];
        posspols := [p*(&*q) : p in posspols, q in goodsets];
     end for;
     finalpols := finalpols cat posspols;
   end for;
   return EliminateAndVerify(C,finalpols);

end function;

function UseNaiveFilter(C,charpols)

    Fq := BaseRing(C);
    n := Degree(Fq);
    // first try to use info on #C(F_q^m) from naive count
    // for small fields
    N := Floor(15/n);
    if N gt 0 then
	vprint JacHypCnt : "Trying naive counting over small extensions.";
	trs := [[Integers()|] : i in [1..#charpols]];
    end if;
    for i in [1..N] do
	vprintf JacHypCnt,2 : "Counting points over extension degree %o.\n",i;
	trC := 2^(n*i)+1 - InternalOrder((N eq 1) select C else
			BaseChange(C, ext<Fq|i>));
	for j := #trs to 1 by -1 do
	    s := -i*cs[#cs-i]-&+[Integers()|
		trs[j][k]*cs[#cs-i+k] : k in [1..i-1]] where cs is
		  Coefficients(charpols[j]);
	    if s ne trC then
		Remove(~trs,j); Remove(~charpols,j);
	    else
		Append(~(trs[j]),s);
	    end if;
	end for;
	if #trs le 1 then break; end if;
    end for;
    return charpols; 

end function;

/* Main function to apply Mestre's generalised AGM method to
   compute the EulerFactor of Jacobian(C), where C is a
   hyperelliptic curve of genus g  over GF(q), with q = 2^n.
*/   
 /**********  NB! ********************
   It is assumed that the input curve, C is ordinary, and is
  given by an equation that allows a group law on Jacobian(C).
   Additionally, it is assumed that n >= g-1 (4 for g=2) -
  this allows us to slightly simplify the code in some parts
  (particularly the the lifting phase).
 *************************************/

function Mestre_CharPoly_Char2(C)

      starttime := Cputime();
      rts,f,F := CheckAndLift(C);
      bext := (Degree(F) gt Degree(BaseRing(C)));
      if bext then
          vprintf JacHypCnt,2 :
              "Extending base field to GF(2^%o)\n\n",Degree(F);
      end if;
      g := Genus(C);
      precfin := BetaPrecision(g,Degree(F))+g;
      vprint JacHypCnt, 2 : "Performing lifting stage...";
      tyme := Cputime();
      taus,booGNB := LiftMain(rts,f,F,precfin);
      vprintf JacHypCnt,2 : "Total lift time: %o\n",Cputime(tyme);
      vprint JacHypCnt, 2 : "Computing norm...";
      vtime JacHypCnt,2 : beta := NormComp(taus,g,#F,booGNB);
//printf "beta: %o\n",beta mod 2^(precfin-g);
      if g gt 2 then
          vprint JacHypCnt,2 :
            "Finding minimal polynomial of beta via LLL...";
          tyme := Cputime();
          betapol :=  MinPolyFromBeta(beta,#F,g);
          vprintf JacHypCnt,2 : "LLL time: %o\n",Cputime(tyme);
          vprintf JacHypCnt,3 : 
              "Minimum polynomial of beta:\n  %o\n",betapol;
          vprint JacHypCnt,2 :
            "Finding possible frobenius characteristic polynomials...";
          tyme := Cputime();
          vtime JacHypCnt,2 : boo1,charpols := PsymToFrob(betapol,#F,g);
          error if not boo1, "Sorry, the method failed!\n",
                            "  (Jacobian decomposes badly).\n";
      else
          vprint JacHypCnt,2 :
            "Finding possible frobenius characteristic polynomials...";
          vtime JacHypCnt,2 : charpols := Genus2CharPoly(beta,#F);
      end if;
      vprintf JacHypCnt,3 : "Found %o possibilities :\n %o\n",
                       #charpols,charpols;
      vprint JacHypCnt,2 : "Performing elimination stage...";
      tyme := Cputime();
      dext := Degree(F) div Degree(BaseRing(C));
      cpols := EliminateAndVerify(bext select C1 else C, charpols) where
                 C1 is IsOdd(dext) select BaseChange(C,F) else
                                                 ReModel(C,rts,f,F);
      if bext then
         if #cpols gt 1 then
            vprintf JacHypCnt,2 : "Still have %o possibilities.\n",#cpols;
         end if;
         cpols := DropDegree(C,cpols,dext);
      end if;
      /*error if (#cpols gt 1),
        "Failed to determine unique frobenius polynomial by random tests!\n";*/
      if (#cpols gt 1) then
      // try naive counting over small extensions to try to get to unique result
	 vprint JacHypCnt : 
	"Failed to determine unique frobenius polynomial by random tests!";
	 cpols := UseNaiveFilter(C,cpols);
	 if (#cpols gt 1) then
	    vprint JacHypCnt : 
	     "Failed to determine unique frobenius polynomial by naive filter\n",
	     "Switching to kedlaya";
	    return KedlayaChar2(C);
	 end if;
      end if;
      vprintf JacHypCnt,2 : "Total elimination time: %o\n", Cputime(tyme);
      vprintf JacHypCnt : "Total time: %o\n", Cputime(starttime);
      return Parent(cpols[1])!Reverse(Coefficients(cpols[1]));

end function;
