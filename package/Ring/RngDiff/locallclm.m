freeze;


import "../../../package/Ring/RngDiff/DiffOpForRngDiff.m":
  DiffOpRingOverRngMPol;
import "localfactorisation.m" :
  TruncateEntriesMatrix,
  TruncateEntriesVector,
  TransferToSystemOverRngSerPow;
import "ricatti.m" :  
  MinimumOfCoefValuationsRHF;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    LCLM over series rings                      //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
function BasisForLCLM(F, K)
  // Input: Fields F and K.
  // Output: a basis of F over K (by matching bases of intermediate
  //  extensions recursively).
  assert ISA(Type(F), FldRat) or ISA(Type(F), FldNum);
  bl, cov :=  ExistsCoveringStructure(F, K);
  assert bl;
  assert cov eq F;  
  basis := [F|1];
  if K eq F then 
    return basis;
  end if;
  basefield := F;
  while K ne basefield do
    B := Basis(basefield);
    basis := [F|v*(F!w):  w in B, v in basis];
      // The ordering is [v1*w1,...,v1*wn, v2*w1,...,v2*wn, etc]. 
      // This means that first one gets the basis of the base field times one
      // fixed element in the ring above.
      // Example: M=Q<T^3-5>, N=M<S^2+4>. The sequence [1,s] of the 
      // extension N/M, becomes [1,t,t^2,s,t*s,t^2*s] in N/Q.
    basefield := BaseField(basefield);
  end while;
  return basis; 
end function;

// ok
// This routine respects the ordering as in BasisForLCLM.
function SequenceOverBasisForLCLM(x,K)
  // Input: x in F=Parent(x) and a Field K.
  // Output : the sequence of x on the basis of F/K obtained by 
  //          successively taking bases of direct extensions. 
  //          The universe of the sequence is F.
  F := Parent(x);
  assert ISA(Type(F), FldRat) or ISA(Type(F), FldNum);
  bl, cov :=  ExistsCoveringStructure(F, K);
  assert bl;
  assert cov eq F;
  seq := [F|x];
  if F eq K then
    return seq;
  end if;
  basefield := F;
  while K ne basefield do   
    seq := &cat([Eltseq(a): a in seq]); 
      // Example: M=Q<T^3-5>, N=M<S^2+4>. The sequence [0,1] in the 
      // extension N/M, becomes [0,0,0,1,0,0] in N/Q.
    basefield := BaseField(basefield);
    assert Universe(seq) eq basefield;
  end while;
  return seq;
end function;

// Used in the next function.
function PolMap(BCpol,UKpol)
  // The embedding for C[X1,...,Xk] to C((z))[Y1,...,YK], where Xi goes to Yi.
  UK := BaseRing(UKpol);
  function PolMapOnElt(x)
    mpx := UKpol!0;
    for t in Terms(x) do
      c := LeadingCoefficient(t);
      v := Exponents(t);
      mpx := mpx + (UK!c)*&*([(UKpol.i)^v[i]: i in [1..#v]]); 
    end for;
    return mpx;
  end function;
  return map<BCpol->UKpol| x :-> PolMapOnElt(x)>; 
end function;


// The next LCLM intrinsic is written specifically for our case for calculating
// right hand factors.
// It works in general if we know that deg(LCLM) = degree(extension)*deg(L)
// but have no way to check this identity beforehand yet.
// Body idea by Nils Bruin.
function LCLMOverSeries(L, mp) 
 // Output: The LCLM of the operator L and its conjugates w.r.t. the 
 //         extension of  BaseRing(L) over the basering of the domain of mp. }
 // Think of mp as the embeddingsmap K[D] -> F[D], induced by 
 // a purely ramified polynomial T^n=a*(K.1).
 // If the routine fails we return 0.
 // We assume that L is of degree 1 and cannot be defined 
 // over a smaller field.
 // Body idea by Nils Bruin.
  R:=Parent(L);
  F:=BaseRing(R);
  assert Characteristic(F) eq 0;
  assert IsDifferentialLaurentSeriesRing(F);
  relprecF := RelativePrecision(F);
  assert IsWeaklyMonic(L) and Degree(L) eq 1;
  assert Codomain(mp) eq R;
  RK := Domain(mp);
  assert IsDifferentialOperatorRing(RK);   
  K := BaseRing(RK);
  assert IsDifferentialLaurentSeriesRing(K);
    // ExistsCoveringStructure(F, K); Does not work for diff rings (3-2005).
  CK := ConstantRing(K);
  CF := ConstantRing(F);
  bl, cov := ExistsCoveringStructure(CF, CK);
  assert bl;
  assert cov eq CF;     
  mpgenK := F!mp(K.1);
  degtrans := Valuation(mpgenK);
  assert degtrans ge 1;
  assert degtrans eq Degree(mpgenK); 
  b := -Coefficient(mpgenK,degtrans);
  bl, b :=IsCoercible(CK,b);
  if not bl then 
    "Cannot coerce elements in a constant ring.";
    return R!0, R!0, false;
  end if;
  a := 1/b;
  if R eq RK then
    return L, R!1, true;
  end if;
    // We consider F/K and an intermediate field Kext, that is
    // the maximal constant field extension of K possible within F/K.
  if CK eq CF then
    Kext := K;
    mpKtoKext := Coercion(K,K);
    sameconstantfield := true;
  else
    Kext, mpKtoKext := ConstantFieldExtension(K,CF);
    sameconstantfield := false;
  end if;
  mpKexttoF := map< Kext->F | x:-> 
                 &+([F|Coefficient(x,i)*mp(K.1^i) : i in Exponents(x)]) 
                 + (bp cmpeq Infinity() select 0 else O(mp(K.1^bp))
                 where bp := AbsolutePrecision(x))>;
  assert ConstantRing(Kext) eq CF;
  basisC := BasisForLCLM(CF,CK);
  vprint RightHandFactors, 1:"Finding basis for constant field extension.";  
  assert basisC[1] eq F!1;
  degconst := #basisC;
    // Due to the maps of the form X^n-a*t, we can lift the basis
    // to F/K as follows.  
  basis := [F| mpKexttoF(v)*(F.1)^i : v in basisC, i in [0..degtrans-1]]; 
  vprint RightHandFactors, 1:"Finding basis for differential field extension.";  
  right := L;
  degright := WeakOrder(right);  
    // Compute the order of the basis.
  d:=degconst*degtrans;
  degL := d*degright;
  degleft := degL-degright;
  vprint RightHandFactors, 1: "Degree of left factor:", degleft;  
  rankM := degleft*d;
    // We are ging to solve a system with rankM unknowns to retrieve
    // The left factor. 
  M:=PolynomialRing(F, rankM);
  seq:=[M|0: i in [1..rankM]];
    // Construct differential operator ring with a rankM basis
    // whose derivations are 0.
  Fpol:=DifferentialRingExtension(seq);  
  Rpol:=DiffOpRingOverRngMPol(Fpol,Derivation(Fpol),CF);
  bl, seqrightinFpol := CanChangeUniverse(Eltseq(right), Fpol); 
  assert bl;
  rightinRpol := Rpol!seqrightinFpol;
  leftinRpol := Rpol![Fpol| &+([M.(d*(i-1)+j)*basis[j]: j in [1..d]]) : 
                            i in [1..degleft]] +(Rpol.1)^degleft;                          
  prodinRpol := leftinRpol*rightinRpol;
    // we can do things on underlying rings now, as we do not need 
    // to multiply operators any more.
  Mswap, swapmpM := SwapExtension(UnderlyingRing(Fpol));
    // This is a Laurent series ring.    
  Cextpol := BaseRing(Mswap);
    // This is a multivariate polynomial ring of rank rankM over CF.  
  dimmat := degL*d-degL;  
  UK := UnderlyingRing(K);
  mat := ZeroMatrix(UK, dimmat, dimmat);
  counterrow := 0;
  vector := [UK|];
  coefs := [];
  for indexofD in [0..(degL-1)] do
      // Look at the coefficient of D^i
      // We want to get the degree in F.1.
    coef := swapmpM(Coefficient(prodinRpol,indexofD)); 
    coefs := coefs cat [coef];
      // Valuation and highest known exponent in F.1.
    val := Valuation(coef);
    deg := Degree(coef);  
      // We want to make sequences of length degtrans. 
    minval := Floor(val/degtrans);  
      // Compute the minimum of all valuations in F.1 of all coefficients. 
    if indexofD eq 0 then
      minimumvalgenK := minval;
      maxdeg := Floor((deg+1)/degtrans);
    else
      minimumvalgenK := Minimum(minimumvalgenK, minval);
      maxdeg := Minimum(maxdeg,Floor((deg+1)/degtrans)); 
    end if;
  end for;  
    // We may need to end the loop through indexofD here.
    // And the start up again. If so, the coefficients need
    // to be stored so that they can be retrieved again.
    //
    // maxdeg := Floor((deg+1)/degtrans);
  minval := minimumvalgenK;
  minprec := (maxdeg-minval)*degtrans;
  if not minprec le relprecF then 
    // "The precision of the ring may be too small to compute the LCLM.",
    // "If routine fails try setting the precision to at least", minprec;
    // return R!0, R!0, false;     
  end if;
  for indexofD in [0..(degL-1)] do  
    coef := coefs[indexofD+1];
    seqCextpol := [];
    seqpowgenK := [K|];
    for s in [minval..(maxdeg-1)] do
      seq:= [Cextpol|Coefficient(coef,s*degtrans+j): j in [0..(degtrans-1)]];
      seqCextpol := seqCextpol cat [ seq ];
      seqpowgenK := seqpowgenK cat [ a*(K.1)^s];        
    end for;
      // Every element should contain degtrans entries.
      // The power of K.1 is seperated in seqpowgenK.
      // Transfer this to a system of sequences on the basis of 
      // 1, (F.1), .. (F.1)^(degtrans-1) respectively.
    seqFKext :=[];
    seqmult :=[];
    for i in [1..degtrans] do
      seqFKext := seqFKext cat [[Cextpol|v[i]: v in seqCextpol]];
      seqmult := seqmult cat [seqpowgenK];
    end for;
    assert #seqFKext eq degtrans;
    assert #seqmult eq degtrans;
      // # elements in seqFKext[i] = # elements in seqmult[i]
      // Every sequence is a coeffient of some z^j, 
      // Later we need to add all of these per sequence.
      // sum(seqFKext[i]*seqmult[i]) is coefficient of (F.1)^(i-1). 
      // Next every constant in CF is written wrt a basis over CK.
    Cpol := PolynomialRing(CK, rankM);
    zeroexps := [0: i in [1..rankM]];
    row := [];
    for v in seqFKext do
      entryrow := [];
      for r in v do
        c := MonomialCoefficient(r,zeroexps);
	seqc := SequenceOverBasisForLCLM(CF!c,CK);
	assert #seqc eq degconst;
	totalterm:= seqc;
        for i in [1..rankM] do
	   c := Coefficient(r,Cextpol.i,1);
	   seqc := SequenceOverBasisForLCLM(CF!c,CK);
	   assert #seqc eq degconst;
	   seqterm := [Cpol| a*Cpol.i: a in seqc];
	   totalterm := [totalterm[j]+seqterm[j]: j in [1..degconst]]; 
	end for;
	entryrow := entryrow cat [totalterm];
      end for;
      row := row cat [entryrow];
    end for;
    UKpol := PolynomialRing(UK,rankM);
    mppol := PolMap(Cpol, UKpol);  
    rowsmatrixonbasis:=[[ &+([ mppol(row[r][i][j])*(UK!seqmult[r][i]) 
                               : i in [1..#row[r]]]) : j in [1..degconst]]   
                               : r in [1.. #row]];  
    rowsmatrix := &cat([ v : v in rowsmatrixonbasis]);
    assert #rowsmatrix eq d;
    for i in [2..d] do
      row := [UK|Coefficient(rowsmatrix[i],UKpol.j,1) : j in [1..rankM]];
      /*
      for j in [1..#row] do
        if not IsWeaklyZero(row[j]) then
          row[j] := row[j] + O(UK.1^1);// O(UK.1^(Degree(row[j])+1));
        end if;
      end for;
      */
      counterrow := counterrow+1;
      mat[counterrow] := Vector(row);
      mon := MonomialCoefficient(rowsmatrix[i],zeroexps);
      vector := vector cat 
                  [UK|-MonomialCoefficient(rowsmatrix[i],zeroexps)];
    end for;
  end for;  
  // mat:=TruncateEntriesMatrix(mat);
  /*
  for j in [1..#vector] do
    if not IsWeaklyZero(vector[j]) then
      vector[j] := vector[j] + O(UK.1^1);//O(UK.1^(Degree(vector[j])+1));
    end if;
  end for;
  */
  vector:=Vector(vector);
  mat, vector := TransferToSystemOverRngSerPow(mat,vector,
                   Integers()!RelativePrecision(K), minval);                                        
  hassolution, S, N := IsConsistent(Transpose(mat),vector);    
  if hassolution then
    if Dimension(N) eq 0 then
      S := ChangeRing(S,K);    
      left := R![F| &+([mp(RK!S[d*(i-1)+j])*basis[j]: j in [1..d]]) : 
                          i in [1..degleft]] +(R.1)^degleft;                       
      prod := left*right;
      // vprint RightHandFactors, 1: [(v): v in Coefficients(prod)];
      prod := RK![Inverse(mp)(v): v in Coefficients(prod)];
      return prod, left, true;
    else 
      "Computation of the LCLM failed.";  
      "The system is overdetermined, try setting a higher precision.";
      return R!0, R!0, false;
    end if;
  else
    "Computation of the LCLM failed.";
    return R!0, R!0, false;
  end if;
end function;
 
