freeze;

/*
  $Id: symplectic.m 15594 2008-04-24 06:23:57Z murray $

  Scott H Murray
  
  6 November 2008
  
  Conjugacy class code for groups G with Sp(n,q) <= G <= CSp(n,q).
  It is based on my preprint 
  "Computing conjugacy in finite classical groups 2:
  Similarity in symplectic and orthogonal groups".  
  
  Currently we require q odd.

  Moved test code and supporting functions to test_symp.m
*/

// Moved from Lang.m, since that file will not load correctly
intrinsic WriteMatrixOverSmallerField( c::Mtrx, k::Fld ) -> Mtrx
{Write the matrix c over a smaller field k}
  K := BaseRing( c );
  d := Degree( K, k );  n := Nrows( c );
  B := Basis( K, k );
  EltReduceField := func< c | Matrix( [ Eltseq( b*c, k ) : b in B ] ) >;
  C := ZeroMatrix( k, n*d, n*d );
  for i in [1..n] do
    for j in [1..n] do
      InsertBlock( ~C, EltReduceField( c[i,j] ), (i-1)*d+1, (j-1)*d+1 );
    end for;
  end for;
  return C;
end intrinsic;





import "linear.m" : AllIrreduciblePolynomialsL;
import "../Classical/isometry.m" : centralSum;

// -----------------------------------------------------------
//
// Parameters for CSp
//
// The partition is signed iff f(X)=X^e+a_0 for some a_0
//

Is1IrreducibleSO := function( f )
  return f eq Dual(f) and ( IsIrreducible(f) or 
    ( #fact eq 2 and fact[1][2] eq 1 and fact[2][2] eq 1 
      where fact is Factorisation(f) ) );
end function;

AlltIrreduciblePolynomialsSO := function( F, d )
  P := PolynomialRing(F); X := P.1;
  ts := [ t : t in F | t ne 0 ];
  pols := [ [] : t in ts ];
  if d eq 1 then
    for tidx in [1..#ts] do
      rts := Roots( X^2 - ts[tidx] );
      pols[tidx] := [ X + rts[i][1] : i in [1..#rts] ];
    end for;
  elif IsEven(d) then
    for f in AllIrreduciblePolynomialsL( F, d ) do
      for i in [1..#ts] do
        if f eq Dual( f : t:=ts[i] ) then 
          Append( ~pols[i], f );
        end if;
      end for;
    end for;
    for f in AllIrreduciblePolynomialsL( F, d div 2 ) do
      for i in [1..#ts] do
        dual := Dual( f : t:=ts[i] );
        if f ne dual and f*dual notin pols[i] then
	  Append( ~pols[i], f*dual );
	end if;
      end for;
    end for;
  end if;
  return pols, ts;
end function;

allPartitions := function( d )
  oldpartitions := [ [] : I in [1..d] ];
  for part in [1..d] do
    partitions := oldpartitions;
    for n in [0..d-1] do
      dimleft := d-n;
      if part le dimleft then
        multleft := dimleft div part;
        for i in [1..multleft] do
	  for partition in ((n ne 0) select oldpartitions[n] else [[]]) do
	    Append( ~partitions[n+part*i], partition cat [<part,i>] );
	  end for;
	end for;
      end if;
    end for;
    oldpartitions := partitions;
  end for;
  return partitions;
end function;

// partitions is all symplectic signed partitions.
// kill says which to remove with one sign killed in the conformal group.
// If EvenChar is true, then only even parts with even multiplicity have signs.
SignedPartitionsS := function( d : EvenChar := false )
  oldpartitions := [ [] : i in [1..d] ];
  oldkills := [ [] : i in [1..d] ];  
  for part in [1..d] do
    partitions := oldpartitions;  kills := oldkills;
    for n in [0..d-1] do
      dimleft := d-n;
      if part le dimleft then
        if IsOdd(part) then
          multleft := dimleft div (2*part);
	  for i in [1..multleft] do
	    oldpartitionsn := ((n ne 0) select oldpartitions[n] else [[]]);
	    oldkillsn  := ((n ne 0) select oldkills[n] else [false]);
	    for idx in [1..#oldpartitionsn] do
	      partition := oldpartitionsn[idx];
	      kill := oldkillsn[idx];
	      Append( ~partitions[n+2*part*i], partition cat [<part,2*i>] );
	      Append( ~kills[n+2*part*i], kill );
	    end for;
	  end for;
	else
          multleft := dimleft div part;
	  for i in [1..multleft] do
	    oldpartitionsn := ((n ne 0) select oldpartitions[n] else [[]]);
	    oldkillsn  := ((n ne 0) select oldkills[n] else [false]);
	    for idx in [1..#oldpartitionsn] do
	      partition := oldpartitionsn[idx];
	      kill := oldkillsn[idx];
	      Append( ~partitions[n+part*i], partition cat [<part,i>] );
	      Append( ~kills[n+part*i], kill );
	      if not EvenChar then
   	        Append( ~partitions[n+part*i], partition cat [<-part,i>] );
   	      end if;
	      // If the partition has not already been killed, and there is
	      // no earlier part which could have been killed ...
	      if not kill and IsOdd(i) and // for i even the multiplicity is + even if the part is signed
	      not exists{ t : t in partition | IsEven(t[1]) and IsOdd(t[2]) }
	      then
	        kill := true;
	      end if;
	      Append( ~kills[n+part*i], kill );
	    end for;
	  end for;
	end if;
      end if;
    end for;
    oldpartitions := partitions;
    oldkills := kills;
  end for;
  return partitions, kills;
end function;

// even char "signs"
// We follow Xue, since we can't understand Wall

Is1IrreducibleSO := func< f | Dual(f) eq f and
  ( IsIrreducible(f) or (#fact eq 2 and fact[1][2] eq 1 and fact[2][2] eq 1
    where fact is Factorisation(f)) ) >;
     

// Supported subsets: All, Semisimple
ClassParametersCSp := function( d, F : Subset:="All" )
  //F := GF(q);
  P := PolynomialRing(F); X := P.1;
  _, ts := AlltIrreduciblePolynomialsSO(F,1);
  pols := [ [] : i in [1..#ts] ];
  for n in [1..d] do
    newpols := AlltIrreduciblePolynomialsSO(F,n);
    for tidx in [1..#ts] do
      pols[tidx] cat:= newpols[tidx];
    end for;
  end for;//pols;
  if Subset eq "All" then
    parts := allPartitions(d);
    sparts, kills := SignedPartitionsS( d );
  elif Subset eq "Semisimple" then
    parts := [ [[<1,i>]] : i in [1..d] ];
    sparts := parts;  kills := [ [ false: p in part] : part in sparts ];
  end if;
  params := [ ];  
  killeds := [ ];  // have we already killed a sign for this param
  for tidx in [1..#ts] do
    t := ts[tidx];
    oldtparams := [ [] : n in [1..d] ];
    oldtkilleds := [ [] : n in [1..d] ];
    for f in pols[tidx] do
      tparams := oldtparams;  tkilleds := oldtkilleds;
      for n in [0..d-1] do
    	dimleft := d-n;
    	if Degree(f) le dimleft then
    	  multleft := dimleft div Degree(f);
    	  for i in [1..multleft] do
    	    tparamsn := ((n ne 0) select oldtparams[n] else [[]]);
    	    tkilledsn := ((n ne 0) select oldtkilleds[n] else [false]);
    	    //tparamsn;
    	    for idx in [1..#tparamsn] do
    	      param := tparamsn[idx];
    	      killed := tkilledsn[idx];
              if IsDivisibleBy(X^2-t,f) then
                if killed or f eq X^2-t then //or IsEven(q) then  
                // only kill for linear factors in odd char
     	          for part in sparts[i] do
    		    Append( ~(tparams[n+Degree(f)*i]), param cat [<t,f,part>] );
    		    Append( ~(tkilleds[n+Degree(f)*i]), true );
    	          end for;
    	        else
                  for idx in [1..#sparts[i]] do
                    if not kills[i][idx] then
                      part :=  sparts[i][idx];
                      Append( ~(tparams[n+Degree(f)*i]), param cat [<t,f,part>] );
                      Append( ~(tkilleds[n+Degree(f)*i]), 
                        exists{ t : t in part | IsEven(t[1]) and IsOdd(t[2]) } );
                    end if;
                  end for;
                end if;
              else
      	        for part in parts[i] do
    		  Append( ~(tparams[n+Degree(f)*i]), param cat [<t,f,part>] );
    		  Append( ~(tkilleds[n+Degree(f)*i]), killed );
    	        end for;
              end if;
    	    end for;
    	  end for;
    	end if;
      end for;
      oldtparams := tparams;  oldtkilleds := tkilleds;
    end for;
    params[tidx] := tparams;  killeds[tidx] := tkilleds;
  end for;
  params := &cat[ params[tidx][d] : tidx in [1..#ts] ];
  return params;
end function;


// -----------------------------------------------------------
//
// Representatives for CSp
//
//

CMatS := function( t, f )
  F := BaseRing( f );
  d := Degree( f );  
  if d eq 1 then 
    return Matrix( 1,1, [F| -Coefficient(f,0)] );  
  end if;
  m := d div 2;
  a := Coefficients( f )[2..m+1];  
  C := ZeroMatrix( F, d, d );
  for i in [1..m-1] do
    C[i,i+1] := 1;
    C[m+1,i+1] := t*a[i];
    C[m+i+1,m+i] := t;
    C[2*m-i+1,2*m] := -a[i]/t^(m-1);
  end for;
  a0 := Coefficient( f, 0 );
  except := forall{c : c in a | c eq 0} and a0 eq -t^m;
  C[m,2*m] := except select -1/t^m else -1/t^m;
  C[m+1,1] := except select a0*t else t^(m+1);
  C[m+1,2*m] := -a[m]/t^(m-1);
  return C;
end function;

JMatL := function( C, m )
  F := BaseRing( C );  
  if m eq 0 then  return Matrix(0,0,[F|]);  end if;
  d := Nrows( C );
  J := DiagonalJoin( [Parent(C)|C: i in [1..m]] );
  I := Parent(C)!1;
  for i in [1..m-1] do
    InsertBlock( ~J, I, (i-1)*d+1, i*d+1 );
  end for;
  return J; 
end function;

// matrix for a pair of odd parts
JMatSOdd := function( t, f, part )
  J := JMatL( CMatS(t,f), part );
  return DiagonalJoin( J, t*J^-1 );
end function;

// matrix for a single even part (with sign)
JMatSEven := function( t, f, part )
  F := BaseRing( f );  P<X> := Parent(f);
  sgn := Sign( part );
  m := Abs(part) div 2;
  C := CompanionMatrix(f);
  J := JMatL( Matrix(1,1,[F!1]), m );
  X := DiagonalJoin( J, J^-1 );
  d := Degree(f);  Id := IdentityMatrix(F, d);
  X := KroneckerProduct(X,C);
  if sgn eq +1 then
    a := Id;
  elif d eq 1 then 
    a := Nonsquare(F)*Id;
  else
    E := ext< F | f >;
    a := WriteMatrixOverSmallerField( Matrix(1,1,[Nonsquare(E)]), F);
  end if;
  for i in [1..m] do  
    InsertBlock( ~X, (-1)^i*a*C, (m-1)*d+1, (m+i-1)*d+1 );
  end for;
  return X;
end function;

// homogeneous matrices
SignedHMatS := function( t, f, partition )  
  e := Degree(f);
  X := ZeroMatrix( Parent(t), 0, 0 );
  for part in partition do
    if IsOdd( part[1] ) then
      for i in [1..(part[2] div 2)] do
        X := centralSum( X, JMatSOdd( t, f, part[1] ) );
      end for;
    else
      mult := part[2];
      q := #Parent(t);
      if (q^e mod 4 eq 1) or (mult mod 4 in {0,1}) then
        X := centralSum( X, JMatSEven( t, f, part[1] ) );
      else
        X := centralSum( X, JMatSEven( t, f, -part[1] ) );
      end if;
      for i in [2..mult] do
        X := centralSum( X, JMatSEven( t, f, Abs(part[1]) ) );
      end for;  
      // if q=1 mod 4, then any central sum of +s gives a +
      // if q=3 mod 4, then a central sum of m=mult-1 copies of + is a + iff m=0,1 mod 4.
    end if;
  end for;
  return X;
end function;

UnsignedHMatS := function( t, f, partition )
  X := ZeroMatrix( Parent(t), 0, 0 );
  for part in partition do
    for i in [1..part[2]] do
        X := centralSum( X, CMatS( t, f^part[1] ) );
    end for;
  end for;
  return X;
end function;


paramToMatS := function( param )
  t := param[1][1];
  F := Parent(t);  P := PolynomialRing(F); X := P.1;
  x := ZeroMatrix( Parent(t), 0, 0 );
  for i in [1..#param] do
    f := param[i][2];  partition := param[i][3];
    y := (IsDivisibleBy(X^2-t,f)) select 
      SignedHMatS( t, f, partition ) else UnsignedHMatS( t, f, partition );
    x := centralSum( x, y );
  end for;
  return x;
end function;

Z := Integers();

paramToCentOrder := function( param )
  t := param[1][1];
  F := Parent(t);  P := PolynomialRing(F); X := P.1;
  q := #F;
  order := (q-1);  overcntflag := false;  noovercntflag := false;
  for i in [1..#param] do
    k := 0;
    f := param[i][2];  e := Degree( param[i][2]);  spartition := param[i][3];
    for j in [1..#spartition] do
      spart := spartition[j][1]; smult := spartition[j][2];
      part := Abs( spart );
      if IsDivisibleBy( X^2-t, f ) then
        if IsOdd( spart ) then //printf "s";
          k +:= smult * ( (part-1)*smult/2 + 
            &+[Z| Abs(spartition[k][1])*spartition[k][2] : k in [1..j-1] ] );
          order *:= #Sp( smult, q^e );
        else //printf "o";
          k +:= smult * ( (part-1)*smult/2 + 
             &+[Z| Abs(spartition[k][1])*spartition[k][2] : k in [1..j-1] ] + 1/2);
          order *:= ( (smult eq 1) select 2 else 
              #InternalGeneralOrthogonalGroup( Sign(spart), smult, GF(q^e) ) );
          if e eq 1 and spart gt 0 and smult eq 1 then 
              // we overcount -I in this case
            overcntflag := true;  
          end if;
          if e eq 1 and smult ne 1 and IsOdd(smult) then
            noovercntflag := true;
          end if;
        end if;
      else 
        if IsIrreducible(f) then //printf "u";
        k +:= smult * ( (part-1)*smult/2 + 
           &+[Z| Abs(spartition[k][1])*spartition[k][2] : k in [1..j-1] ] );
          order *:= #GU( smult, q^(e div 2) );
        else //printf "l";
        k +:= smult * ( (part-1)*smult/2 + 
           &+[Z| Abs(spartition[k][1])*spartition[k][2] : k in [1..j-1] ] );
          order *:= #GL( smult, q^(e div 2) );
        end if;
      end if;
    end for;
    order *:= q^(Z!(k*e));
  end for;
  
  if not noovercntflag and overcntflag then  order div:= 2;  //printf "v";  
  end if;
  
  return order;
end function;
        

ClassRepresentativesCSpOdd := function( d, q : Subset:="All" )
  if IsEven(q) then  error "q must be odd";  end if;
  F := GF(q);  G := CSp(d,q);
  params := [ param : param in ClassParametersCSp(d,F:Subset:=Subset) ];
  reps := [ G | paramToMatS(param) : param in params ];
  return reps, params;
end function;

// -----------------------------------------------------------
//
// Sp
//
//

HatSO := function( p )
    P := Parent( p );
    F := CoefficientRing( P );
    R := RationalFunctionField( F ); x := R.1;
    return P!( x^Degree(p) * Evaluate( R!p, x + 1/x ) );
end function;

All1IrreduciblePolynomialsSO := function( F, d )
  P := PolynomialRing(F); X := P.1;
  pols := {@@};
  if d eq 1 then
    pols := {@ X + a : a in {F|1,-1} @};
  elif IsEven(d) then
    allhalf := (d eq 2) select [ X + a : a in F | a ne 0] else
      AllIrreduciblePolynomialsL( F, d div 2 );
    if d eq 2 then  
      Include( ~pols, HatSO(X) );
    end if;
    for f in allhalf do
      hat := HatSO(f);
      if IsIrreducible( hat ) then
        Include( ~pols, hat );
      end if;
    end for;
    for f in allhalf do
      dual := Dual( f );
      if f ne dual then
        Include( ~pols, f*dual );
      end if;
    end for;
  end if;
  return IndexedSetToSequence( pols );
end function;

IsSignedPol := func< f | f eq X+1 or f eq X-1
  where X is Parent(f).1 >;

ClassParametersSp := function( d, q )	     
//  if IsEven(q) then error "q must be odd";  end if;
  F := GF(q);
  P := PolynomialRing(F); X := P.1;
  pols := &cat[ All1IrreduciblePolynomialsSO(F,i) : i in [1..d] ];
  parts := allPartitions(d);
  sparts := SignedPartitionsS( d );
  oldparams := [ [] : n in [1..d] ];
  for f in pols do
    //print "f ", f;
    params := oldparams;
    fparts := IsSignedPol(f) select sparts else parts;
    for n in [0..d-1] do
      //print "  n ", n;
      dimleft := d-n;
      if Degree(f) le dimleft then
  	multleft := dimleft div Degree(f);
  	for i in [1..multleft] do
  	  for param in ((n ne 0) select oldparams[n] else [[]]) do
  	    for part in fparts[i] do
  	      Append( ~params[n+Degree(f)*i], param cat [<f,part>] );
  	    end for;
  	  end for;
  	end for;
      end if;
    end for;
    oldparams := params;
  end for;
  return params[d];
end function;

ClassRepresentativesSpOdd := function( d, q : Subset:="All" )
  if IsEven(q) then  error "q must be odd";  end if;
  F := GF(q);  G := Sp(d,q);
  params := [ param : param in ClassParametersSp(d,q) ];  //:Subset:=Subset) ];
  reps := [ G | paramToMatS(param) : param in params ];
  return reps, params;
end function;


// =================================================
//
// Constructing the groups
//
// =================================================

// representative elt of Delta=Sp(n,q) with tau=x
taurep := function( Delta, x )
  n := Degree(Delta);  m := n div 2;  q := #BaseRing( Delta );
  if IsEven( q ) then
    return x^(q div 2) * Delta!1;
  else
    return Delta!DiagonalMatrix([x:i in [1..m]] cat [1:i in [1..m]]);
  end if;
end function;

intrinsic ExtendedSpOld( n::RngIntElt, q::RngIntElt, m::RngIntElt ) -> GrpMat
{The matrix group containing Sp(n,q) with index m}
  require m gt 0 : "m must be positive";
  ok, r := IsDivisibleBy( q-1, m );
  require ok : "m must divide q-1";
  Delta := CSp(n, q);
  Omega := Sp(n, q);  // catch errors!
  x := PrimitiveElement( GF(q) );
  ngens := NumberOfGenerators( Omega );
  G := MatrixGroup< n, q | Append( [ Delta | Omega.i : i in [1..ngens] ], 
    taurep(Delta,x^r) ) >;
  return G;
end intrinsic;

intrinsic RecogniseExtendedSp( G::GrpMat ) -> RngInt
{Find the index of the symplectic group inside G}
  require Category( BaseRing(G) ) eq FldFin : "The base field must be finite";
  require IsSymplecticGroup( G ) : "Not a linear group";
  d := Degree(G); k := BaseRing(G);
  F := StandardAlternatingForm( d, k );
  require G`forms`bilinearForm eq F : "Nonstandard symplectic";

  V := VectorSpace(k,d);
  assert exists(i,j){<i,j> : i,j in [1..d] | F[i,j] ne 0 };
  vi := V.i; vj := V.j;
  w := F[i,j]^-1;
  return LCM( [Integers() | Order(InnerProduct(vi*g*F,vj*g)*w) : g in Generators(G)] );
end intrinsic;

intrinsic RecognizeExtendedSp( G::GrpMat ) -> RngInt
{"} // "
  return RecogniseExtendedSp(G);
end intrinsic;


intrinsic InternalClassesExtendedSpOld( G::GrpMat ) -> SeqEnum
{Internal function: The conjugacy classes of CSp(d,q)}
  d := Degree(G); k := BaseRing(G);  q := #k;
  try
    m := RecogniseExtendedSp( G );
  catch e
    return false;
  end try;

  // Currently only works for CSp over odd char fields
  if IsOdd( q ) then
    if m eq q-1 then
      ordG := #G;
      reps, params := ClassRepresentativesCSpOdd(d, q);
      C := [ <Order(reps[i]),ordG div paramToCentOrder(params[i]),reps[i]> : i in [1..#reps] ];
      if not assigned G`Classes then
        G`Classes := C;
      end if;
      return true;
    /*elif m eq 1 then
      reps, params := ClassRepresentativesSpOdd(d, q);
      return true, reps, params;*/
    end if;
  end if;
  
  return false;    
end intrinsic;


