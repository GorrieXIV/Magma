freeze;

/*
  $Id: unitary.m 15594 2008-04-24 06:23:57Z murray $

  Sergei Haller and Scott H Murray
  
  6 November 2008
  
  Conjugacy class code for groups G with SU(n,q) <= G <= CU(n,q).
  This builds on the C-level code written by Sergei Haller.
  It is based on our preprint 
  "Computing conjugacy in finite classical groups 1:
  Similarity in unitary groups".  

*/

import "linear.m" : AllIrreduciblePolynomialsL;

// the automorphism of K with order a
FiniteFieldAuto := function( K, a )
  _, p, n := IsPrimePower( #K );
  ok, b := IsDivisibleBy( n, a );
  if ok then
    F := sub<K|b>;
    return FrobeniusMap(K,F), F;
  else
    error "Error: Invalid order";
  end if;
end function;


// ======================================================================
//
// Polynomials
//
// ======================================================================

// sigma is a map or a boolean
//   sigma=false  ->  sigma=id
//   sigma=true   ->  |sigma|=2

intrinsic Dual( p::RngUPolElt : t:=1, sigma:=false ) -> RngUPolElt
{The dual of a polynomial}
  P := Parent( p );
  F := CoefficientRing( P );
  R := RationalFunctionField( F ); x := R.1;
  a0 := Coefficient(p, 0);
  require a0 ne Zero(F) : "Polynomial must have nonzero constant term";
  dual := P!( x^Degree(p) * Evaluate( R!p, t/x ) / a0 );
  if Category(sigma) eq BoolElt then
    if sigma then
      sigma := FiniteFieldAuto( F, 2 );
    else
      return dual;
    end if;
  end if;
  _,h := ChangeRing( P, F, sigma );
  return h(p);
end intrinsic;

AlltIrreduciblePolynomialsU := function( E, d )
  F := sub< E | Degree(E,PrimeField(E)) div 2 >;  
  sigma := FiniteFieldAuto( E, 2 );
  P := PolynomialRing(E); X := P.1;
  ts := [ t : t in F | t ne 0 ];
  pols := [ [] : t in ts ];
  if IsOdd( d ) then
    for f in AllIrreduciblePolynomialsL( E, d ) do
      for i in [1..#ts] do
        if f eq Dual( f : t:=ts[i], sigma:=sigma ) then
          Append( ~pols[i], f );
        end if;
      end for;
    end for;
  else
    for f in AllIrreduciblePolynomialsL( E, d div 2 ) do
      for i in [1..#ts] do
        dual := Dual( f : t:=ts[i], sigma:=sigma );
        if f ne dual and f*dual notin pols[i] then
	  Append( ~pols[i], f*dual );
	end if;
      end for;
    end for;
  end if;
  return pols, ts;
end function;

// ======================================================================
//
// Invariants
//
// ======================================================================

ClassInvariantsCU := function( d, q )
  E := GF(q^2);
  P := PolynomialRing(E); X := P.1;
  _, ts := AlltIrreduciblePolynomialsU(E,1);
  pols := [ [] : I in [1..#ts] ];
  for n in [1..d] do
    newpols := AlltIrreduciblePolynomialsU(E,n);
    for tidx in [1..#ts] do
      pols[tidx] cat:= newpols[tidx];
    end for;
  end for;
  parts := [ Partitions(i) : i in [1..d] ];
  oldparams := [ [ [] : n in [1..d] ] : i in [1..#ts] ];
  for tidx in [1..#ts] do
    t := ts[tidx];
    for f in pols[tidx] do
      //print "f ", f;
      params := oldparams;
      for n in [0..d-1] do
    	//print "  n ", n;
    	dimleft := d-n;
    	if Degree(f) le dimleft then
    	  multleft := dimleft div Degree(f);
    	  for i in [1..multleft] do
    	    for param in ((n ne 0) select oldparams[tidx][n] else [[]]) do
    	      for part in parts[i] do
    		Append( ~params[tidx][n+Degree(f)*i], param cat [<t,f,part>] );
    	      end for;
    	    end for;
    	  end for;
    	end if;
      end for;
      oldparams := params;
    end for;
  end for;
  return &cat[ params[tidx][d] : tidx in [1..#ts] ];
end function;

/*for d in [1..5] do
  for q in [2,3,4,5] do
    d, q, #ClassInvariantsCU(d,q) eq NumberOfClasses(CU(d,q));
  end for;
end for;*/
