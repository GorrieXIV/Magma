freeze;

/*
  $Id: $

  Sergei Haller and Scott H Murray
  
  6 November 2008

  Orthogonal groups in odd characteristic

  Intrinsics:
      InternalConformalOrthogonalGroup
      InternalGeneralOrthogonalGroup
      InternalClassesExtendedOmega
*/

/*
SetVerbose("Classes",0);
*/

import "symplectic.m" : allPartitions, spartToDeg, 
    All1IrreduciblePolynomialsSO, AlltIrreduciblePolynomialsSO, 
    IsSignedPol, /* matToParamL, DualSO,*/ JMatL;

// return T st T*F1*Tr(T) eq F2 (or a scalar multiple)
// where Fi is the square matrix of degree 2*m+1 with
// 1s on the antidiagonal, except for Fi[m+1,m+1] = ai (i=1,2).
centreTransformer := function( m, F, a1, a2 )
    c := a2/a1;
    if IsSquare( c ) then
        c0 := F!1;  c1 := Sqrt(c);
    else
        c0 := Nonsquare(F);  c1 := Sqrt(c*c0);
        // almost equivalent to c0 := c; c1 := c;
        // except that it's not always the case that
        // Sqrt(c*c) eq c.
    end if;
    I := IdentityMatrix(F,m);
    return DiagonalJoin(c0*I,DiagonalJoin(Matrix(1,1,[c1]),I));
end function;

/*
matTot2 := function( A, F )
  return ((A)*F*Transpose(A)*Transpose(F))[1,1];
end function;
*/

/* this only works up to a constant, for q prime
formOMinus2 := function(q)
  F := GF(q);
  F2 := ext< F | 2 >;
  xi := F2.1;
  n := F!(xi*xi^q);  t := F!(xi+xi^q)/2;
  d := F!((xi-xi^q)^2);
  return Matrix( 2, 2, [1,t,t,n] );
end function;
*/
/* check
for q in [3,5,7,11,13,17,19,23] do
  F := GF(q);
  G := GOMinus( 4, q );
  J := ExtractBlock(ClassicalForms(G)`bilinearForm, 2,2,2,2 );
  //J := Matrix(J)/J[1,1];
  F2 := ext<F|2>;//GF(q^2);
  xi := F2.1;
  n := F!(xi*xi^q);  t := F!(-xi^1-xi^(q));  d := F!((xi^-1-xi^-q)^2);
  print q, t, n, -t/2, J[1,1]*d;

    //J eq formOMinus2(q);
//  if J ne F then
//    print q, J, F;
//  end if;
end for;

*/


// ===========================================================================
//
// The Witt group
//
// Elements of the Witt group represented by pairs <d,s>
// where d is the degree mod 2, and s is the element of F^*/F^*2 = Z/2Z.
//
// In the notation of the paper:
//   0     = <0,0>
//   1     = <1,0>
//   delta = <1,1>
//   omega = <0,1>

// Witt group element of a given form matrix
/*
formToWElt := function( F )
  return < Nrows(F) mod 2, 
    IsSquare( (-1)^(Nrows(F) div 2) *Determinant(F) ) select 0 else 1 >;
end function;

WEltToForm := function( d, q, w )
  assert d mod 2 eq w[1];
  return OrthogonalForm( w[2] eq 0 select +1 else -1, d, q );
end function;
*/

WAdd := function( q, w1, w2 )
  if q mod 4 eq 1 then
    return < (w1[1]+w2[1]) mod 2, (w1[2]+w2[2]) mod 2 >;
  else
    return < (w1[1]+w2[1]) mod 2, (w1[2]+w2[2] + w1[1]*w2[1]) mod 2 >;
  end if;
end function;

/* Check
WPow := function( q, w, m )
  if q mod 4 eq 1 then
    return < m*w[1] mod 2, m*w[2] mod 2 >;
  else
    return < m*w[1] mod 2, (m*w[2] + (m*(m-1) div 2)*w[1]) mod 2 >;
  end if;
end function;

for q in [3,5,7,9] do
  for w1,w2 in [<i,j> : i,j in [0,1]] do
    WAdd(q,w1,w2) eq 
    formToWElt(DiagonalJoin(WEltToForm(2+w1[1],q,w1), WEltToForm(2+w2[1],q,w2)));
  end for;
end for;
for q in [3,5,7,9] do
  for w in [<i,j> : i,j in [0,1]] do
    for m in [1..10] do
      WPow(q,w,m) eq 
      formToWElt(DiagonalJoin([Parent(A)|A: i in [1..m]]))
      where A is WEltToForm(2+w[1],q,w);
    end for;
  end for;
end for;

WMult := function( q, w1, w2 )
  return < (w1[1]*w2[1]) mod 2, (w1[2]*w2[1]+w1[1]*w2[2]) mod 2 >;
end function;

// Check
for q in [3,5,7,9] do
  for w1,w2 in [<i,j> : i,j in [0,1]] do
    WMult(q,w1,w2) eq 
    formToWElt(KroneckerProduct(WEltToForm(2+w1[1],q,w1), WEltToForm(2+w2[1],q,w2)));
  end for;
end for;
*/

wittToSign := func< w | (-1)^w[2] >;
// signToWitt := func< d, sgn | <d mod 2, (1-sgn) mod 2> >;

// ===========================================================================
//
// Parameters
//

// -----------------------------------------------------------
//
// GO
//
//

// This function returns two sequences
// partitions: list of all orthogonal signed partitions.
// kills: partitions that should be ignored when removing one sign in the 
//   conformal case. ie, partitionss whose first signed part is negative.
SignedPartitionsO := function( d : EvenChar := false )

  // We create partitions starting with the smallest part size.
  // When part = i, oldpartitions consists of a partitions with
  // no part of size i or larger.
  oldpartitions := [ [] : i in [1..d] ];
  oldkills := [ [] : i in [1..d] ];  
  for part in [1..d] do  // part = the size of the part we are currently adding

    partitions := oldpartitions;  kills := oldkills;

    for n in [0..d-1] do  // n = currently adding to partitions of n

      dimleft := d-n;  // the amount of space left in our partition
      if part le dimleft then  // there is room
      
        if IsEven(part) then  // even parts have even multiplicity, no signs
          multleft := dimleft div (2*part);  // there is room for multleft pairs of parts
	  for i in [1..multleft] do // i = half the multiplicity of the new part
	    oldpartitionsn := ((n ne 0) select oldpartitions[n] else [[]]);
	    oldkillsn  := ((n ne 0) select oldkills[n] else [false]);
	    for idx in [1..#oldpartitionsn] do  // for each old partition of n
	      partition := oldpartitionsn[idx];
	      kill := oldkillsn[idx];
	      Append( ~partitions[n+2*part*i], partition cat [<part,2*i>] );
	      Append( ~kills[n+2*part*i], kill );
	    end for;
	  end for;

	else  // odd parts have signs
          multleft := dimleft div part;  // there is room for multleft parts
	  for i in [1..multleft] do  // i = the multiplicity of the new part
	    oldpartitionsn := ((n ne 0) select oldpartitions[n] else [[]]);
	    oldkillsn  := ((n ne 0) select oldkills[n] else [false]);

	    for idx in [1..#oldpartitionsn] do  // for each old partition of n
	      partition := oldpartitionsn[idx];
	      kill := oldkillsn[idx];
	      Append( ~partitions[n+part*i], partition cat [<part,i>] );
	      Append( ~kills[n+part*i], kill );
   	      Append( ~partitions[n+part*i], partition cat [<-part,i>] );
	      // If the partition has not already been killed, and there is
	      // no earlier part which could have been killed ...
	      if not kill and IsOdd(i) and 
	      not exists{ t : t in partition | IsOdd(t[1]) and IsOdd(t[2]) }
	      then
	        kill := true;
	      end if;
	      Append( ~kills[n+part*i], kill );
	    end for; // idx
	  end for; // i

	end if; // part even/odd
      end if; // part le dimleft

    end for; // n

    oldpartitions := partitions;
    oldkills := kills;
  end for; // part
  return partitions, kills;
end function;

/*SignedPartitionsO := function( d : EvenChar:= false )
  oldpartitions := [ [] : I in [1..d] ];
  for part in [1..d] do
    partitions := oldpartitions;
    for n in [0..d-1] do
      dimleft := d-n;
      if part le dimleft then
        if IsEven(part) then
          multleft := dimleft div (2*part);
	  for i in [1..multleft] do
	    for partition in ((n ne 0) select oldpartitions[n] else [[]]) do
	      Append( ~partitions[n+2*part*i], partition cat [<part,2*i>] );
	    end for;
	  end for;
	else
          multleft := dimleft div part;
	  for i in [1..multleft] do
	    for partition in ((n ne 0) select oldpartitions[n] else [[]]) do
	      Append( ~partitions[n+part*i], partition cat [<part,i>] );
	      if not EvenChar then
  	        Append( ~partitions[n+part*i], partition cat [<-part,i>] );
  	      end if;
	    end for;
	  end for;
	end if;
      end if;
    end for;
    oldpartitions := partitions;
  end for;
  return partitions;
end function;*/

partitionToSign := func<partition | &*[Sign(part[1]) : part in partition]>;

/*
partitionToDeg := func< partition | 
  &*[ Abs(part[1])^part[2] : part in partition ] >;
*/

termToWitt := function( t, f, part, mult )
  w := < Abs(part)*mult*Degree(f) mod 2, 0 >;
  P<X> := Parent(f);
  if IsDivisibleBy(X^2-t,f) then
    w[2] := (part gt 0) select 0 else 1;
  elif IsIrreducible(f) then
    w[2] := part*mult mod 2;
  end if;
  return w;
end function;

paramToWitt := function( param )
  t := param[1][1];
  q := #Parent(t);
  w := <0,0>;
  for term in param do
    f := term[2];  partition := term[3];
    if IsIrreducible(f) then
      for p in partition do //termToWitt(t,f,p[1],p[2]);
        w := WAdd(q,w,termToWitt(t,f,p[1],p[2]));
      end for;
    // else w := WAdd(q,w,< 0, 0 > );
    end if;
  end for;
  return w;
end function;

paramToSign := func< param | (-1)^paramToWitt(param)[2] >;

/*paramToSign := func< param | 
  &*[ ((IsIrreducible(p[2])) select -1 else +1)^spartToDeg(p[3]) * partitionToSign(p[3]) : 
    p in param ] where X is Parent(param[1][1]).1 >;*/

ClassParametersCOPlusMinus := function( d, F : Subset:="All" )
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
    sparts, kills := SignedPartitionsO( d );
  elif Subset eq "Semisimple" then
    parts := [ [[<1,i>]] : i in [1..d] ];
    sparts := parts;  kills := [ [ false: p in part] : part in sparts ];
  end if;
  params := [ ];  
  killeds := [ ];  // have we already killed a sign for this param?
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
                        exists{ t : t in part | IsOdd(t[1]) and IsOdd(t[2]) } );
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

ClassParametersCO := function( t, d, F )
  if t eq 0 then  
//    return [ param : param in ClassParametersCOPlusMinus( d, F ) ];
    return ClassParametersCOPlusMinus( d, F );
  end if;
  return [ param : param in ClassParametersCOPlusMinus( d, F ) | 
    paramToSign(param) eq t ];//ClassParametersOPlusMinus( d, q );
end function;

/*
seqpairs := func< Q | Setseq( {<a,#[b:b in Q|b eq a]> : a in Seqset(Q)} ) >;

matToParamCO := function( sgn, X )
  t := matTot2(X, SymmetricBilinearForm(sgn,Nrows(X),BaseRing(X)));
  Lparam := matToParamL( X );
  param := [];
  for p in Lparam do
    f := p[1];
    if f eq Dual(f:t:=t) then
      Append( ~param, <t, f, seqpairs(p[2])> );
    else
      f := f * Dual(f:t:=t);
      if not exists{ p : p in param | p[2] eq f } then
        Append( ~param, <t, f, seqpairs(p[2])> );
      end if;
    end if;
  end for;
  return param;
end function;

stripSigns := function( param )
  for i in [1..#param] do
    for j in [1..#param[i][3]] do
      param[i][3][j][1] := Abs(param[i][3][j][1]);
    end for;
  end for;
  return param;
end function;


cmp := function( param )
  return { < pair[1], pair[2], Seqset(pair[3]) > : pair in param };
end function;

for d in [2..14] do
  q:=3;//for q in [3,5,7,9,11] do
    for t in (IsEven(d) select [+1,-1] else [0]) do
      F := GF(q);  P := PolynomialRing(F); X := P.1;
      mine := ClassParametersCO( t, d, q );  
      real  := [ matToParamCO( t, c[3] ) : c in Classes(CO(t,d,q)) ];
      mine := {* cmp(stripSigns(param)) : param in mine *};
      real := {* cmp(param) : param in real *};
      all := &join[ MultisetToSet(A) : A in [ mine, real] ];
      print d, q,t, { <p,m1,m2> : p in all | m1 ne m2
        where m1 is Multiplicity(mine,p) where m2 is Multiplicity(real,p) };
    end for;
  end for;
end for;


for d in [2..14] do
  for q in [3,5,7,9,11] do
    for t in (IsEven(d) select [+1,-1] else [0]) do
      mine := #ClassParametersCO( t, d, q );  
      real := NumberOfClasses(CO(t,d,q));
      d, q, t, "\t", mine, "\t", real;
    end for;  
  end for;
end for;




for d in [2,4,6] do
  for q in [3,5,7,9,11] do
    for t in [+1,-1] do
      F := GF(q);  P := PolynomialRing(F); X := P.1;
      real := [ param : c in Classes(CO(t,d,q)) | #param eq 1 and param[1][2] eq X-1 
        where param is matToParamCO( t, c[3] ) ];
      mine := [ param : param in ClassParametersCO( t, d, q ) | #param eq 1 and param[1][2] eq X-1 ];
      print d, q, {* cmp(stripSigns(param)) : param in mine *} eq {* cmp(param) : param in real *};

    end for;
  end for;
end for;



for d in [2,4,6] do
  for q in [3,5,7,9,11] do
    //for t in [+1,-1] do
      F := GF(q);  P := PolynomialRing(F); X := P.1;
      real := &cat[ [ param : c in Classes(CO(t,d,q)) | IsUnipotent(c[3]) //#param eq 1 and param[1][2] eq X-1 
        where param is matToParamCO( t, c[3] ) ] : t in (IsEven(d) select [+1,-1] else [0]) ];
      mine := &cat[ [ param : param in ClassParametersCO( t, d, q ) | #param eq 1 and param[1][2] eq X-1 ]
        : t in (IsEven(d) select [+1,-1] else [0]) ];;
      print d, q, {* cmp(stripSigns(param)) : param in mine *} eq {* cmp(param) : param in real *};

    //end for;
  end for;
end for;




all := All1IrreduciblePolynomialsSO(F,d);
forall{ f : f in all | f eq DualSO(f) };
params := ClassParametersSp(d,q);
C := Classes(Sp(d,q));
[ char : c in C | IsIrreducible(char)
  where char is CharacteristicPolynomial( c[3] ) ];
[ char : char in all | IsIrreducible(char) ];
Lparams := [ matToParamL( c[3] ) : c in C ];

[ Factorisation( CharacteristicPolynomial( c[3] ) ) : c in C ];
*/


ClassParametersOPlusMinus := function( d, F )	    
  q := F; 
  if IsEven(q) then error "q must be odd"; end if;
  q := #F;
  P := PolynomialRing(F); X := P.1;
  pols := &cat[ All1IrreduciblePolynomialsSO(F,i) : i in [1..d] ];
  parts := allPartitions(d);
  sparts := SignedPartitionsO( d );
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
  	    for part in fparts[i] do //params; param cat [<f,part>];
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

ClassParametersGO := function( d, F )
  if IsEven(d) then "use ClassParametersOPlus or ClassParametersOMinus";  end if;
  return [ param : param in ClassParametersOPlusMinus( d, F ) | 
    paramToSign(param) eq +1 ];//ClassParametersOPlusMinus( d, q );
end function;

ClassParametersGOPlus := function( d, F )
  if IsOdd(d) then "use ClassParametersGO";  end if;
  return [ param : param in ClassParametersOPlusMinus( d, F ) | 
    paramToSign(param) eq +1 ];
end function;

ClassParametersGOMinus := function( d, F )
  if IsOdd(d) then "use ClassParametersGO";  end if;
  return [ param : param in ClassParametersOPlusMinus( d, F ) | 
    paramToSign(param) eq -1 ];
end function;

/*
// put parameter in a form that is easy to compare
cmp := function( param )
  return { < pair[1], Seqset(pair[2]) > : pair in param };
end function;

load "parameters.mag";
for d in [2,4,6] do
  for q in [3,5,7,9,11] do
    plus, minus := ClassParametersO( d, q );
    d, q, "\t", #plus, NumberOfClasses(GOPlus(d,q)), "\t",
    #minus, NumberOfClasses(GOMinus(d,q));
  end for;
end for;

for d in [2,4,6,8] do
  for q in [3,5,7,9,11] do
    F := GF(q);  P := PolynomialRing(F); X := P.1;
    plus, minus := ClassParametersCO(d,q);
    Oplus := [ matToParamSO( c[3] ) : c in Classes(GOPlus(d,q)) ];
    Ominus := [ matToParamSO( c[3] ) : c in Classes(GOMinus(d,q)) ];
    print d, q,
      { cmp(stripSigns(param)) : param in plus } diff { cmp(param) : param in Oplus },
      { cmp(param) : param in Oplus } diff { cmp(stripSigns(param)) : param in plus };
  end for;
end for;



for d in [2,4,6] do
  for q in [3,5,7,9,11] do
    F := GF(q);  P := PolynomialRing(F); X := P.1;
    Oplus := [ matToParamSO( c[3] ) : c in Classes(GOPlus(d,q)) ];
    Ominus := [ matToParamSO( c[3] ) : c in Classes(GOMinus(d,q)) ];
    print d, q, "plus",[ param : param in Oplus | #param eq 1 and param[1][1] eq X^2+1 ],
      "minus",[ param : param in Ominus | #param eq 1 and param[1][1] eq X^2+1 ];
  end for;
end for;




all := All1IrreduciblePolynomialsSO(F,d);
forall{ f : f in all | f eq DualSO(f) };
params := ClassParametersSp(d,q);
C := Classes(Sp(d,q));
[ char : c in C | IsIrreducible(char)
  where char is CharacteristicPolynomial( c[3] ) ];
[ char : char in all | IsIrreducible(char) ];
Lparams := [ matToParamL( c[3] ) : c in C ];

[ Factorisation( CharacteristicPolynomial( c[3] ) ) : c in C ];
*/

// -----------------------------------------------------------
//
// SO
//
//

paramToDet := func< param | 
  &*[ (-1^(Degree(p[1]))*Evaluate(p[1],0))^spartToDeg(p[2]) : 
  p in param ] >;
isSplitSO := function( param )
  P<X> := Parent( param[1][1] );
  partitions := [ p[2] : p in param | p[1] in {X+1,X-1} ];
  return forall{ part : part in &cat(partitions) | IsEven(part[1]) };
end function;
      
  

splitParams := function( params, paramToIm, isSplit )
  params := [ param : param in params | paramToIm(param) eq 1 ];
  newparams := [];
  for param in params do
    if isSplit(param) then
      newparams cat:= [ <param,+1>, <param,-1> ];
    else
      newparams cat:= [ < param,0> ];
    end if;
  end for;
  return newparams;
end function;

ClassParametersSOPlus := function( d, q )
  return splitParams( ClassParametersGOPlus(d,q), paramToDet, isSplitSO );
end function;

ClassParametersSOMinus := function( d, q )
  return splitParams( ClassParametersGOMinus(d,q), paramToDet, isSplitSO );
end function;

ClassParametersSO := function( d, q )
  return splitParams( ClassParametersGO(d,q), paramToDet, isSplitSO );
end function;


/*
load "parameters.mag";
for d in [2..7] do
  for q in [3,5,7,9,11] do
    if IsEven(d) then
      print d, q, "\t",
        #ClassParametersSOPlus( d, q ), NumberOfClasses(SOPlus(d,q)),
        #ClassParametersSOMinus( d, q ), NumberOfClasses(SOMinus(d,q));
    else
      print d, q, "\t",
        #ClassParametersSO( d, q ), NumberOfClasses(SO(d,q));
    end if;
  end for;
end for;


d := 4;  q := 7;
F := GF(q);  P := PolynomialRing(F); X := P.1;
G := GOPlus(d, q);  S := SOPlus(d,q);

ClassParametersSOPlus(d,q);

CG := Classes( G );
CGmap := ClassMap( G );
CS := Classes( S );
ind := [ CGmap(t[3]) : t in CS ];

split := [ matToParamSO(CG[i][3]) : i in Seqset(ind) | #[j:j in ind|j eq i] eq 2 ];
unsplit := [ matToParamSO(CG[i][3]) : i in Seqset(ind) | #[j:j in ind|j eq i] eq 1 ];

[ [ p : p in param | p[1] in {X+1,X-1} ] : param in unsplit ];
[ [ p : p in param | p[1] in {X+1,X-1} ] : param in split ];

#split + #unsplit eq #[ t : t in CG | Determinant(t[3]) eq 1 ];
2*#split + #unsplit eq #CS;

*/
// -----------------------------------------------------------
//
// Omega
//
//

// This is only tested for params of determinant 1
polToSp := func< f | IsSquare(Determinant((1+CompanionMatrix(f))/2)) 
  select 1 else -1 >;

paramToSp := function( param )
  P<X> := Parent( param[1][1] );  F := BaseRing(P);
  sp := &*[ Integers() | (polToSp(p[1])^spartToDeg(p[2])) : p in param ];
  if exists(p){p : p in param | p[1] eq X+1 } then
    sp *:= partitionToSign(p[2]);
    if not IsSquare(F!-1) then
      sp *:= (-1)^(spartToDeg(p[2]) div 2);
    end if;
  end if;
  return sp;
end function;

paramSOToSp := func< param | paramToSp(param[1]) >;

isSplitOmega := function( param )
  param := param[1];
  P<X> := Parent( param[1][1] );

  // all components must have sp = 1
  /*if exists{ p : p in param | paramToSp([p]) ne 1 } then
    return false;
  end if;*/

  if exists(p){ p : p in param | p[1] eq X-1 } then
    // all odd parts mult 1, all same sign
    if not ( forall{ part : part in p[2] | IsEven(part[1]) or part[2] eq 1 } and
    #{ Sign(part[1]) : part in p[2] | IsOdd(part[1]) } le 1 ) then
      return false;
    end if;
  end if;
  if exists(p){ p : p in param | p[1] eq X+1 } then
    // all odd parts mult 1, all same sign
    // EXCEPT for (5,1) in dimension 6 char 3,7,..
    if not (forall{ part : part in p[2] | IsEven(part[1]) or part[2] eq 1 } and
    #{ Sign(part[1]) : part in p[2] | IsOdd(part[1]) } le 1) /*and 
    not (not IsSquare(BaseRing(P)!-1) and #p[2] eq 2 and
    { <Abs(part[1]),part[2]> : part in p[2] } eq {<5,1>,<1,1>})*/ then
      return false;
    end if;
  end if;

  // all other parts even
  return forall{ p : p in param | p[1] in {X+1,X-1} or 
    forall{ part : part in p[2] | IsEven(part[1]) } };
end function;
      

ClassParametersOmegaPlus := function( d, q )
  return splitParams( ClassParametersSOPlus(d,q), paramSOToSp, isSplitOmega );
end function;

ClassParametersOmegaMinus := function( d, q )
  return splitParams( ClassParametersSOMinus(d,q), paramSOToSp, isSplitOmega );
end function;

ClassParametersOmega := function( d, q )
  return splitParams( ClassParametersSO(d,q), paramSOToSp, isSplitOmega );
end function;



/*
load "parameters.mag";
for d in [2..7] do
  for q in [3,5,7,9,11] do
    if IsEven(d) then
      print d, q, "\t",
        #ClassParametersOmegaPlus( d, q ), NumberOfClasses(OmegaPlus(d,q)),
        #ClassParametersOmegaMinus( d, q ), NumberOfClasses(OmegaMinus(d,q));
    else
      print d, q, "\t",
        #ClassParametersOmega( d, q ), NumberOfClasses(Omega(d,q));
    end if;
  end for;
end for;


// Test paramToSp
load "parameters.mag";
for d in [2..8] do
  for q in [3,5] do
    S := SOPlus(d, q);
    if d gt 2 then
      F := ClassicalForms(S)`bilinearForm; 
    else
      F := Matrix(GF(q),2,2,[0,1,1,0]);
    end if;

    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    p1 := { cmp(matToParamSO(t[3])) : t in Classes(S) | sp(t[3]) eq 1 };
    p2 := {cmp(stripSigns(param[1])) : param in ClassParametersSOPlus(d,q) | 
      paramToSp(param[1]) eq 1 };
    print d,q,"+",p1 diff p2, p2 diff p1;
    
    S := SOMinus(d, q);
    if d gt 2 then
      F := ClassicalForms(S)`bilinearForm; 
    else
      F := SubmatrixRange( ClassicalForms(SOMinus(4,q))`bilinearForm, 2,2, 3,3 );
    end if;

    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    p1 := { cmp(matToParamSO(t[3])) : t in Classes(S) | sp(t[3]) eq 1 };
    p2 := {cmp(stripSigns(param[1])) : param in ClassParametersSOMinus(d,q) |
      paramToSp(param[1]) eq 1 };
    print d,q,"-",p1 diff p2, p2 diff p1;
    
  end for;
end for;



load "parameters.mag";

AllSplitParams := function( S, M, sp )
  CS := Classes( S );
  CSmap := ClassMap( S );
  CM := Classes( M );
  ind := [ CSmap(t[3]) : t in CM ];

  return 
    [ matToParamSO(CS[i][3]) : i in Seqset(ind) | #[j:j in ind|j eq i] eq 2 ], 
    [ matToParamSO(CS[i][3]) : i in Seqset(ind) | #[j:j in ind|j eq i] eq 1 ];
end function;

q := 7;
F := GF(q);  P := PolynomialRing(F); X := P.1;
filter := func< paramseq |
  {* Rep(cmp(stripSigns(param)))[2] : param in paramseq | 
    #param eq 1 and param[1][1] eq X+1 *} >; 
for d in [3..8] do
  if IsEven( d ) then
    S := SOPlus(d, q);  M := OmegaPlus(d,q);
    F := ClassicalForms(S)`bilinearForm; 
    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    splitP, unsplitP := AllSplitParams( S, M, sp );

    S := SOMinus(d, q);  M := OmegaMinus(d,q);
    F := ClassicalForms(S)`bilinearForm; 
    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    splitM, unsplitM := AllSplitParams( S, M, sp );

    params := ClassParametersSOPlus(d,q) cat ClassParametersSOMinus(d,q);
    params := [ param : param in params | paramToSp(param[1]) eq 1 ];
    splitT := [ param[1] : param in params | isSplitOmega(param) ];    
    unsplitT := [ param[1] : param in params | not isSplitOmega(param) ];
    
    print d, q, "split", filter(splitP cat splitM) eq filter(splitT);
    print d, q, "unsplit", filter(unsplitP cat unsplitM) eq filter(unsplitT);
  else
    S := SO(d, q);  M := Omega(d,q);
    F := ClassicalForms(S)`bilinearForm; 
    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    splitP, unsplitP := AllSplitParams( S, M, sp );
     
    params := ClassParametersSO(d,q);
    params := [ param : param in params | paramToSp(param[1]) eq 1 ];
    splitT := [ param[1] : param in params | isSplitOmega(param) ];    
    unsplitT := [ param[1] : param in params | not isSplitOmega(param) ];
     
    print d, q, "split", filter(splitP) eq filter(splitT);
    print d, q, "unsplit", filter(unsplitP) eq filter(unsplitT);
  end if;
end for;

q := 5;
F := GF(q);  P := PolynomialRing(F); X := P.1;
filter := func< paramseq |
  {* Rep(cmp(stripSigns(param))) : param in paramseq | 
    #param eq 1 and param[1][1] notin {X+1,X-1} *} >; 
for d in [3..8] do
  if IsEven( d ) then
    S := SOPlus(d, q);  M := OmegaPlus(d,q);
    F := ClassicalForms(S)`bilinearForm; 
    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    splitP, unsplitP := AllSplitParams( S, M, sp );

    S := SOMinus(d, q);  M := OmegaMinus(d,q);
    F := ClassicalForms(S)`bilinearForm; 
    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    splitM, unsplitM := AllSplitParams( S, M, sp );

    params := ClassParametersSOPlus(d,q) cat ClassParametersSOMinus(d,q);
    params := [ param : param in params | paramToSp(param[1]) eq 1 ];
    splitT := [ param[1] : param in params | isSplitOmega(param) ];    
    unsplitT := [ param[1] : param in params | not isSplitOmega(param) ];
    
    print d, q, "split", filter(splitP cat splitM) eq filter(splitT);
    print d, q, "unsplit", filter(unsplitP cat unsplitM) eq filter(unsplitT);
  end if;
end for;

q := 5;
F := GF(q);  P := PolynomialRing(F); X := P.1;
filter := func< paramseq |
  {* cmp(stripSigns(param)) : param in paramseq *} >; 
for d in [3..8] do
  if IsEven( d ) then
    S := SOPlus(d, q);  M := OmegaPlus(d,q);
    F := ClassicalForms(S)`bilinearForm; 
    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    splitP, unsplitP := AllSplitParams( S, M, sp );

    S := SOMinus(d, q);  M := OmegaMinus(d,q);
    F := ClassicalForms(S)`bilinearForm; 
    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    splitM, unsplitM := AllSplitParams( S, M, sp );

    params := ClassParametersSOPlus(d,q) cat ClassParametersSOMinus(d,q);
    params := [ param : param in params | paramToSp(param[1]) eq 1 ];
    splitT := [ param[1] : param in params | isSplitOmega(param) ];    
    unsplitT := [ param[1] : param in params | not isSplitOmega(param) ];
    
    print d, q, "split", filter(splitP cat splitM) eq filter(splitT);
    print d, q, "unsplit", filter(unsplitP cat unsplitM) eq filter(unsplitT);
  else
    S := SO(d, q);  M := Omega(d,q);
    F := ClassicalForms(S)`bilinearForm; 
    sp := func< x | (SpinorNorm(x,Matrix(F)) eq 0) select 1 else -1 >;
    splitP, unsplitP := AllSplitParams( S, M, sp );
     
    params := ClassParametersSO(d,q);
    params := [ param : param in params | paramToSp(param[1]) eq 1 ];
    splitT := [ param[1] : param in params | isSplitOmega(param) ];    
    unsplitT := [ param[1] : param in params | not isSplitOmega(param) ];

    print d, q, "both", filter(splitP cat unsplitP) eq 
      filter(splitT cat unsplitT);
    print d, q, "split", filter(splitP) eq filter(splitT);
    print d, q, "unsplit", filter(unsplitP) eq filter(unsplitT);
  end if;
end for;

// REWRITE matToParamSO to compute signs !!!!!

*/




// ===================================================================
//
// Representatives
//
//


// -----------------------------------------------------------
//
// Representatives for CO
//
//

/*
// find x in K=ext<F|2> st a*T(x)=b*N(x)
NTlineq := function( K, F, a, b )
  if a eq 0 then
    return K!0;
  else
    nu := Sqrt(K!Nonsquare(F));
    if b eq 0 then
      return nu;
    else
      return 2*a/(b*(1+nu));
    end if;
  end if;
end function;
*/

// find x in K=ext<F|2> st a*(x^2+x^(2q))=b*N(x)
NTquadeq := function( K, F, a, b )
  if a eq 0 then
    return (b eq 0) select 1 else K!0;
  elif b+2*a eq 0 then
    return Sqrt(K!Nonsquare(F));
  elif IsSquare((b-2*a)/(b+2*a)) then
    q := #F;
    if exists(c){ c : c in F | c ne 0 and a*(c^2+c^(2*q)) eq b*c^(q+1)} then
      return c;
    else
      error "This is a particularly deliquescent bug in Magma. Please email the run to murray@maths.usyd.edu.au";
    end if;
    // this never happens for us, I don't know why
  else
    P := PolynomialRing(K); X := P.1;
    rts := Roots( X^2-X+a/(b+2*a) );
    c := rts[1][1];
    return c;
  end if;
end function;
/* Test
for q in [q:q in [2..20]|IsPrimePower(q) and IsOdd(q)] do
  F := GF(q);  K := GF(q^2);
  print q, 
    forall{<a,b>:a,b in F| exists{x:x in K | x ne 0 and a*(x^2+x^(2*q)) eq b*x^(q+1)} };
end for;

for q in [q:q in [2..20]|IsPrimePower(q) and IsOdd(q)] do
  F := GF(q);  K := GF(q^2);
  print q, 
    forall{<a,b>:a,b in F| a*(x^2+x^(2*q)) eq b*x^(q+1) 
      or IsSquare((b-2*a)/(b+2*a))
      where x is NTquadeq( K, F, a, b ) };
end for;
      
// the element gamma st gamma and 1-4*gamma are nonsquare
//  K=ext<k|2>
gammafunc := function( k, K )
  q := #k;
  xi := PrimitiveElement( K );
  return k!( xi^(q+1)/(xi+xi^q)^2 );
end function;
*/

nufunc := function( k, K )
  q := #k;
  xi := PrimitiveElement( K );
  return Sqrt( k!( 4*xi^(q+1)/(xi-xi^q)^2 ) );
end function;

/* Check
for q in [q:q in [2..1000]|IsPrimePower(q) and IsOdd(q)] do
  k := GF(q);  K := GF(q^2);
  gamma := gammafunc(k,K);
  print q, IsSquare(gamma),IsSquare(1-4*gamma);
end for;

for q in [q:q in [2..1000]|IsPrimePower(q) and IsOdd(q)] do
  k := GF(q);  K := GF(q^2);
  nu := nufunc(k,K);
  print q, IsSquare(1+nu^2);
end for;
*/

// This always gives the minus-type irreducible matrix
// For t nonsquare and f= X^2-t, there is also a plus-type,
// but it is just given by CompanionMatrix(f).
CMatO := function( t, f )
  k := BaseRing( f );  K := ext<k|2>;  q := #k;
  d := Degree( f );  square_t := IsSquare(t);
  P<X> := Parent( f );
  
  fact := Factorisation(f);
  if #fact eq 2 then
    g := fact[1][1]^fact[1][2];
    C := CompanionMatrix(g);
    F := SymmetricBilinearForm(+1,d div 2,k);
    return DiagonalJoin( C, t*F*Transpose(C)^-1*F );
  end if;
  
  delta := Nonsquare(k);  delta0 := Sqrt(K!delta);
  if d eq 1 then 
    return Matrix( 1,1, [k| -Coefficient(f,0)] );
  elif f eq X^2-t then
    nu := nufunc(k,K);
    x := Sqrt(t*(1+nu^2));  y := Sqrt(t/delta);
    return Matrix( 2,2, [ k| x, nu*y, -nu*delta*y, -x ] );
  elif d eq 2 then
    a := Coefficient(f,1);  disc := a^2-4*t;
    x := Sqrt(delta*disc);
    return Matrix( 2,2, [ k| -a/2, x/(2*delta), x/2, -a/2 ] ); 
  end if;
  r := d div 2 -1;
  as := Coefficients( f )[1..r+2];  a:= func< i | as[i+1] >;

  // compute c
  st := &+[ k | a(r-2*i)/t^i : i in [0..(r div 2)] ];
  sn := ( a(r+1) + 2* &+[ k | a(r+1-2*i)/t^i : i in [1..((r+1) div 2)] ] );
  if square_t then
    srt := Sqrt(t);
    c := NTquadeq(K,k,st,sn*srt);
    assert st*(c^2+c^(2*q)) eq sn*srt*c^(q+1);
    assert st*srt*(c^2+c^(2*q)) eq sn*t*c^(q+1);
    bp := k!0;
  else
    if exists(pair){ <bp,c> : bp in k, c in K | c ne 0 and 
      IsSquare(delta*bp^2 + t) and 
      ( t*sn*c^(q+1) eq st * ( srt*(c^2+c^(2*q)) + bp*delta0*(c^(2*q)-c^2) ) 
        where srt is Sqrt(delta*bp^2 + t) ) }
    then
      bp := pair[1];  c := pair[2];  srt := Sqrt(delta*bp^2 + t);
    else
      error "This is a particularly deliquescent bug in Magma. (2) Please email the run to murray@maths.usyd.edu.au";
    end if;
  end if;
  assert srt^2 eq delta*bp^2 + t;
  assert t*sn*c^(q+1) eq st * ( srt*(c^2+c^(2*q)) + bp*delta0*(c^(2*q)-c^2) );
 
  // compute b_i for i=0..r-1
  bs := [ (st ne 0) select t^(r+1)*c^(q+1)/st else k!2 ];  
  b:= func< i | bs[i+1] >;
  for i in [1..r-1] do
    bs[i+1] := ( a(i)*b(0) + ((i ne 1) select t^r*b(i-2) else 0) )/t^(r+1);
    b:= func< i | bs[i+1] >;
  end for;
  
  
  cs := c^q;
  assert Coefficient(f,0) eq t^(r+1);
  for i in [1..r-1] do
    assert Coefficient(f,i) eq 
      (t^(r+1)*b(i) - ((i ne 1) select t^r*b(i-2) else 0))/b(0);
  end for;
  assert r lt 2 or 
    Coefficient(f,r) eq (t^(r+1)*c*cs - ((r ne 1) select t^r*b(r-2) else 0))/b(0);
  //assert st eq 0 or r lt 1 or
  //  Coefficient(f,r+1) eq (srt*t^r*(c^2+cs^2) - 2*t^r*b(r-1))/b(0);

  // construct the matrix
  C := ZeroMatrix( k, d, d );
  for i in [1..r-1] do
    C[i,i+1] := 1;  
  end for;

  if r gt 0 then  C[r,d] := 1/b(0);  end if;

  C[r+1,r+1] := srt;  C[r+1,r+2] := -bp;    
  C[r+1,d] := -(-1)^r* (bp*(c-cs)*delta0 - srt*(c+cs)) /(2*b(0));

  C[r+2,r+1] := bp*delta;  C[r+2,r+2] := -srt;  
  C[r+2,d] := -(-1)^r* (srt*delta0*(c-cs) - bp*delta*(c+cs)) /(2*b(0));

  for i in [1..r] do  C[d-r+1,i] := t*b(i-1);  end for;
  if r gt 0 then
    C[d-r+1,r+1] := -(-1)^r*t*(c+cs);  C[d-r+1,r+2] := (-1)^r*t*(c-cs)/(delta0);
    C[d-r+1,d] := - t*c*cs/b(0);
  end if;

  for i in [2..r] do  
    C[d-r+i,d-r+i-1] := t;
    C[d-r+i,d] := -t*b(r+1-i)/b(0);
  end for;

  F := SymmetricBilinearFormMinus(d,k);
  F2 := DiagonalMatrix( [ k | 1/2, -delta/2 ] );
  InsertBlock(~F,F2,r+1,r+1);
  assert C*F*Transpose(C) eq t*F;

  
  // Convert to standard form
  _, T2 := TransformBilinearForm( F2 );
  I := IdentityMatrix( k, r );
  T := DiagonalJoin( I, DiagonalJoin( T2, I ) ); 
  C := T*C*T^-1;
  
  // check
  F := SymmetricBilinearFormMinus(d,k);
  assert C*F*Transpose(C) eq t*F;
  assert CharacteristicPolynomial(C) eq f;

  return C;
end function;



/* test
for q in [3,5,7,9,11,13,17,25,27] do
  for d in [2,4,6,8,10] do
    r := d div 2 -1;
    k := GF(q);  K := GF(q^2);  Tr:=Transpose;
    P := PolynomialRing(k); X := P.1;
    G := GOMinus(d,k);
    Fplus := SymmetricBilinearFormPlus(d,k);
    Fminus := SymmetricBilinearFormMinus(d,k);

    pols, ts := AlltIrreduciblePolynomialsSO(k,d);

    for i in [1..#ts] do
      t := ts[i];
      //if IsSquare(t) then
        print q,d,t;forall{ f : f in pols[i] |
          CharacteristicPolynomial(C) eq f and C*F*Tr(C) eq t*F 
          where C is CMatO(t,f) 
          where F is (IsIrreducible(f) select Fminus else Fplus) };
      //end if;
    end for;
  end for;
end for;




f := Random(pols);
C := CMatO(t,f);
C*F*Tr(C) eq F;
CharacteristicPolynomial(C) eq f;


forall{ f : f in pols | CharacteristicPolynomial(C) eq f and C*F*Tr(C) eq F
  where C is CMatO(f)};

*/



// the representative matrix x in COMinus with tau(x)=t
tauRepOMinus := function( d, k, K, t )
  ok, s := IsSquare(t);
  if ok then
    x2 := ScalarMatrix(2,s);
  else
    delta := Nonsquare(k);
    if IsSquare(k!-1) then
      s := Sqrt(-t*delta^-1);
      x2 := Matrix(2,2,[0,s,-s*delta,0]);
    else
      nu := nufunc(k,K);
      a := Sqrt(-delta^-1);
      b := Sqrt(t/(1+nu^2));
      x2 := b*Matrix(2,2,[1,a*nu,-a^-1*nu,1]);
    end if;
  end if;
  I := IdentityMatrix(k,d div 2 -1);
  return DiagonalJoin(t*I,DiagonalJoin(x2,I));
end function;

tauRepOPlus := function( d, t )
  I := IdentityMatrix(Parent(t),d div 2);
  return DiagonalJoin(t*I,I);
end function;

/* Check
d := 4;
for q in [q:q in [2..100]|IsPrimePower(q) and IsOdd(q)] do
  k := GF(q);  K := GF(q^2);
  F := SymmetricBilinearFormMinus(d,k);
  repeat t := Random(k); until t ne 0;
  x := tauRepOMinus(4,k,K,t);
  print q, x*F*Transpose(x) eq t*F;
  t *:= Nonsquare(k);
  x := tauRepOMinus(4,k,K,t);
  print q, x*F*Transpose(x) eq t*F;
end for;
*/

/* test
for q in [3,5,7,9,11,13,17,25,27] do
  for d in [4,6,8,10] do
    r := d div 2 -1;
    k := GF(q);  K := GF(q^2);  Tr:=Transpose;
    P := PolynomialRing(k); X := P.1;
    Fplus := SymmetricBilinearFormPlus(d,k);
    Fminus := SymmetricBilinearFormMinus(d,k);

    pols, ts := AlltIrreduciblePolynomialsSO(k,d);

    for i in [1..#ts] do
      t := ts[i];
      print q,d,t,forall{ f : f in pols[i] |
        CharacteristicPolynomial(C) eq f and C*F*Tr(C) eq t*F 
        where C is CMatO(t,f) 
        where F is (IsIrreducible(f) select Fminus else Fplus) };
    end for;
  end for;
end for;
*/

// matrix for a pair of even parts
JMatOEven := function( t, f, part )
  J := JMatL( CMatO(t,f), part );
  F := SymmetricBilinearForm(+1,part*Degree(f),Parent(t));
  return DiagonalJoin( J, t*F*Transpose(J^-1)*F );
end function;

// matrix for a single odd part (with sign)
// This is correct for unipotents, but wrong in other cases
JMatOOddOld := function( t, f, part )
  F := BaseRing( f );  P<X> := Parent(f);
  sgn := Sign( part );
  m := Abs(part) div 2;
  d := Degree(f);  Id := IdentityMatrix(F, d);
  C := CompanionMatrix(f);
  J := JMatL( Matrix(1,1,[F!1]), m );
  X := DiagonalJoin( J, DiagonalJoin( Matrix(1,1,[F!1]), J^-1 ));
  if Abs(part) gt 1 then  X[m,m+1] := 1;  end if;
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
    InsertBlock( ~X, (-1)^i*a*C/2, (m-1)*d+1,(m+i)*d+1 );
  end for;
  if sgn eq -1 and d eq 2 then
    C := CMatO(t,f);
    InsertBlock( ~X, C, m*d+1, m*d+1 );
  end if;
  for i in [1..m] do
    InsertBlock( ~X, (-1)^i*a*C, m*d+1,(m+i)*d+1 );
  end for;
  //assert IsScalar( X*J*Transpose(X) * J^-1 ) where
  //  J is SymmetricBilinearForm( sgn, Abs(part), F );

  return X;
end function;

JMatOOdd := function(t,f,part)
  F := BaseRing( f );  P<X> := Parent(f);
  sgn := Sign( part );
  if sgn eq -1 then 
    return OrthogonalTensorProduct(CMatO(t,f),JMatOOddOld(F!1,X-1,part): 
      ASign:=-1, BSign:=-1, Sign:=-1);
  else
    return OrthogonalTensorProduct(CompanionMatrix(f),JMatOOddOld(F!1,X-1,part): 
      ASign:=+1, BSign:=+1, Sign:=+1);
  end if;
end function;

// for f irreducible not dividing X^2-t
JMatOUnsigned := function(t,f,part)
  k := BaseRing( f );  q := #k;
  d := Degree( f );  P<X> := Parent( f );
  
  fact := Factorisation(f);
  if #fact eq 2 then
    g := fact[1][1]^fact[1][2];
    C := JMatL(CompanionMatrix(g),part);
    F := SymmetricBilinearForm(+1,(d div 2)*part,k);
    return DiagonalJoin( C, t*F*Transpose(C)^-1*F );
  elif IsOdd(part) then
    return OrthogonalTensorProduct(CMatO(t,f),JMatOOddOld(k!1,X-1,part) : 
      ASign:=-1, BSign:=+1, Sign:=(-1)^part);
  else
    sd := d*(part div 2);
    C := $$(t,f,part div 2);
    F1 := SymmetricBilinearForm((-1)^(part div 2),sd,k);
    assert C*F1*Transpose(C) eq t*F1;
    F0 := SymmetricBilinearForm(+1,sd,k);
    Bt := ZeroMatrix(k,sd,sd);
    Bt[sd,sd-1] := -1;  Bt[sd-1,sd] := 1;
    B := Bt*(F1*Transpose(C))^-1;
    A := BlockMatrix(2,2,[C,B,0,C]);
    assert A*F*Transpose(A) eq t*F where F is BlockMatrix(2,2,[0,F1,F1,0]);;
    T := BlockMatrix(2,2,[F0*F1^-1,0,0,1]);
    return T*A*T^-1;
  end if;
  
end function;

/* test
Signfunc := Sign;
Tr:=Transpose;

for q in [3,5,7,9,11,13,17,25,27] do
  F := GF(q);
  P := PolynomialRing(F); X := P.1;
  for t in [t:t in F | t ne 0] do
    if IsSquare(t) then  s := Sqrt(t);  fs := [X+s,X-s];
    else  fs := [X^2-t];
    end if;
    for f in fs do
      for part in [1,-1,3,-3,5,-5,7,-7] do
        A := JMatOOdd(t,f,part);
        J := SymmetricBilinearForm(Signfunc(part),Abs(part)*Degree(f),F);
        if not (CharacteristicPolynomial(A) eq f^Abs(part) and A*J*Tr(A) eq t*J) then
          error q, part,t,f;
        end if;
      end for;
    end for;
  end for;
end for;

for q in [3,5,7,9,11,13,17,25,27] do
  F := GF(q);
  P := PolynomialRing(F); X := P.1;
  for t in [t:t in F | t ne 0] do
    if IsSquare(t) then  s := Sqrt(t);  fs := [X+s,X-s];
    else  fs := [X^2-t];
    end if;
    for f in fs do
      for part in [2,4,6,8,10] do
        A := JMatOEven(t,f,part);
        J := SymmetricBilinearForm(+1,2*part*Degree(f),F);
        if not (CharacteristicPolynomial(A) eq f^(2*part) and A*J*Tr(A) eq t*J) then
          error q, part,t,f;
        end if;
      end for;
    end for;
  end for;
end for;

for q in [3,5,7,9,11,13,17,25,27] do
  F := GF(q);
  P := PolynomialRing(F); X := P.1;
  for d in [1..5] do

    pols, ts := AlltIrreduciblePolynomialsSO(F,d);

    for i in [1..#ts] do
      t := ts[i];
      for f in pols[i] do
        sgn := IsIrreducible(f) select -1 else +1;
        if not IsDivisibleBy( X^2-t, f ) then
          for part in [1..10] do
            A := JMatOUnsigned(t,f,part);
            J := SymmetricBilinearForm(sgn^part,part*Degree(f),F);
            if not (CharacteristicPolynomial(A) eq f^part and A*J*Tr(A) eq t*J) then
              error q, part,t,f, A*J*Tr(A) eq t*J;
            end if;
          end for;
        end if;
      end for;
    end for;
  end for;
end for;

*/

// homogeneous matrices
Signfunc := Sign;
SignedHMatO := function( t, f, partition )
  F := Parent(t);  q := #F;  deg := Degree(f) mod 2;
  Y := Matrix(0,0,[F|]);  wY := <0,0>;
  
  for i in [1..#partition] do

    part := partition[i];
    if IsEven( part[1] ) then
      X := Matrix(0,0,[F|]);  w := <0,0>;
      J := JMatOEven( t, f, part[1] );
      for i in [1..(part[2] div 2)] do
        X := OrthogonalDirectSum( X, J :
          ASign:=+1, BSign:=+1, Sign:=+1 );
      end for;
    else
      X := Matrix(0,0,[F|]);  w := <0,0>;
      J := JMatOOdd( t, f, Abs(part[1]) );  wJ := <deg,0>;
      for j in [1..(part[2]-1)] do
        oldw := w;  w := WAdd(q,w,wJ);  //oldw,wJ,w;
        X := OrthogonalDirectSum( X, J :
          ASign:=wittToSign(oldw), BSign:=wittToSign(wJ), Sign:=wittToSign(w) );
      end for;
      if wittToSign(WAdd(q,w,wJ)) ne Signfunc(part[1]) then
        J := JMatOOdd( t, f, -Abs(part[1]) );  wJ := <deg,1>;
      end if;
      oldw := w;  w := WAdd(q,w,wJ); // oldw,wJ,w;
      X := OrthogonalDirectSum( X, J :
        ASign:=wittToSign(oldw), BSign:=wittToSign(wJ), Sign:=wittToSign(w) );
      assert w eq <deg*part[2] mod 2,(1-Signfunc(part[1])) div 2>;
    end if;

    oldwY := wY;  wY := WAdd(q,wY,w);
    Y := OrthogonalDirectSum( Y, X :
        ASign:=wittToSign(oldwY), BSign:=wittToSign(w), Sign:=wittToSign(wY) );
  end for;

  assert wY eq paramToWitt([<t,f,partition>]);
  return Y;
end function;

UnsignedHMatO := function( t, f, partition )
  q := #Parent(t);
  X := ZeroMatrix( Parent(t), 0, 0 );  w := <0,0>;
  for part in partition do
    J := JMatOUnsigned( t, f, part[1] );
    wJ := paramToWitt( [ < t, f, [<part[1],1>] > ] );
    for i in [1..part[2]] do
      oldw := w;  w := WAdd(q,w,wJ);//  oldw,wJ,w;
      X := OrthogonalDirectSum( X, J :
        ASign:=wittToSign(oldw), BSign:=wittToSign(wJ), Sign:=wittToSign(w) );
    end for;
  end for;
  return X;
end function;

/* test
Signfunc := Sign;
Tr:=Transpose;

for q in [3,5,7,9,11,13,17,25,27] do
  F := GF(q);
  P := PolynomialRing(F); X := P.1;
  for t in [t:t in F | t ne 0] do
    if IsSquare(t) then  s := Sqrt(t);  fs := [X+s,X-s];
    else  fs := [X^2-t];
    end if;
    for f in fs do
      partitions := SignedPartitionsO(15);
      for d in [1..15] do q,d;
        for partition in partitions[d] do
          A := SignedHMatO(t,f,partition);
          J := SymmetricBilinearForm(paramToSign([<t,f,partition>]),
            d*Degree(f),F);
          if not (CharacteristicPolynomial(A) eq f^d and A*J*Tr(A) eq t*J) then
            error q, partition,t,f;
          end if;
        end for;
      end for;
    end for;
  end for;
end for;

partitions :=allPartitions(15);
for q in [3,5,7,9,11,13,17,25,27] do
  F := GF(q);
  P := PolynomialRing(F); X := P.1;
  pols, ts := AlltIrreduciblePolynomialsSO(F,d);
  for i in [1..#ts] do
    t := ts[i];
    for f in pols[i] do
      if not IsDivisibleBy(f,X^2-t) then
        for d in [1..15] do q,d;
          for partition in partitions[d] do
            A := UnsignedHMatO(t,f,partition);
            J := SymmetricBilinearForm(paramToSign([<t,f,partition>]),d*Degree(f),F);
            if not (CharacteristicPolynomial(A) eq f^d and A*J*Tr(A) eq t*J) then
              error q, partition,t,f;
            end if;
          end for;
        end for;
      end if;
    end for;
  end for;
end for;


*/


paramToMatO := function( param )
  t := param[1][1]; //param;
  F := Parent(t);  P := PolynomialRing(F); X := P.1;  q := #F;
  x := ZeroMatrix( Parent(t), 0, 0 );  w := <0,0>;
  for i in [1..#param] do
    f := param[i][2];  partition := param[i][3];
    y := (IsDivisibleBy(X^2-t,f)) select 
      SignedHMatO( t, f, partition ) else UnsignedHMatO( t, f, partition );   
    wy := paramToWitt( [param[i]] );  oldw := w;  w := WAdd( q, w, wy );
    //"hi", oldw, wy, w;
    x := OrthogonalDirectSum( x, y : 
      ASign:= wittToSign(oldw), BSign:=wittToSign(wy), Sign:=wittToSign(w) );
    //assert 
  end for;
  assert wittToSign(w) eq paramToSign(param);
  return x, wittToSign(w);
end function;


/*

for d in [2..14 by 2] do
  for q in [3,5,7,9,11] do
    for sgn in [+1,-1] do
      print d,q, sgn;
      F := GF(q);  P := PolynomialRing(F); X := P.1;
      G := CO(sgn,d,q);  
      params := [ param : param in ClassParametersCO(sgn,d,q) ];//| param[1][1] eq 1];
      reps := [ paramToMatO(param) : param in params ];//| param[1][1] eq 1 ];

      Fm := SymmetricBilinearForm(sgn,d,F);
      //forall(i){ i : i in [1..#params] |  X*Fm*Transpose(X) eq t*Fm 
      //  where X is reps[i] where t is params[i][1][1] };
      //forall(i){ i : i in [1..#params] |
      //  paramSToParamL( params[i] ) eq matToParamL( reps[i] ) };
      C := Classes(G:TFAl := "Random", ASAl := "Random");//, Reps:=reps);
      #C eq #reps;
      h := ClassMap(G);
      indices := { h(G!c) : c in reps };
      #indices eq #C;
      { {i,j} : i,j in [1..#C] | i lt j and h(reps[i]) eq h(reps[j]) };
    end for;
  end for;
end for;

*/

// ========================================================
//
// Generic orthogonal groups
//
intrinsic InternalGeneralOrthogonalGroup( t::RngIntElt, n::RngIntElt, F::FldFin ) -> GrpMat
{The matrix group GO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
   require IsFinite(F) : "The field must be finite";
  if IsEven(n) then
    require t in [+1,-1] : "Invalid sign";
    return (t eq +1) select GOPlus(n,F) else
      GOMinus(n,F);
  else
     require t in [+1,0,-1] : "Invalid sign";
     if Characteristic(F) eq 2 then
       require t eq 0 : "Invalid sign";
     end if;
     G := GO(n,F);
     return sub< Generic(G) | [ Transpose(G.i^-1) : i in [1..2] ] >;
     /*if sign ne 0 then
       m := n div 2;
       F[m+1,m+1] := (sign eq 1) select F!1/2 else Nonsquare(F)/2;
     end if;
     return F;*/
  end if;
end intrinsic;

intrinsic InternalConformalOrthogonalGroup( t::RngIntElt, n::RngIntElt, F::FldFin ) -> GrpMat
{The matrix group CO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
    require IsFinite(F) : "The field must be finite";
    if IsEven(n) then
        require t in [+1,-1] : "Invalid sign";
        return (t eq +1) select COPlus(n,F) else COMinus(n,F);
    else
        require t in [+1,0,-1] : "Invalid sign";
        if Characteristic(F) eq 2 then
            require t eq 0 : "Invalid sign";
        end if;
        G := CO(n,F);
        gord := FactoredOrder(G);
        G := sub< Generic(G) | [ Transpose(G.i^-1) : i in [1..Ngens(G)] ] >;
        if t ne 0 then
/*
            c := (t eq +1) select F!1/2 else Nonsquare(F)/2;
            if IsSquare( c ) then
                c0 := F!1;  c1 := Sqrt(c);
            else
                c0 := Nonsquare(F);  c1 := Sqrt(c*c0);
            end if;
*/
            T := centreTransformer( n div 2, F,
              F!2, (t eq +1) select F!1 else Nonsquare(F) );
            G := sub< Generic(G) | [ T*G.i*T^-1 : i in [1..Ngens(G)] ] >;
        end if;
        G`Order := gord;
        return G;
    end if;
end intrinsic;

ClassRepresentativesCOOdd := function( t, d, q : Subset:="All" )
  if IsEven(q) then  error "q must be odd";  end if;
  F := GF(q);  G := InternalConformalOrthogonalGroup(t,d,F);
  if IsEven(d) then
    params := [ param : param in ClassParametersCO(t,d,F) ];
    reps := [ G | paramToMatO(param) : param in params ];
  else
    m := d div 2;  k := GF(q);
    c := case< t | +1 : k!1, -1 : Nonsquare(k), default : k!2 >;
    T0 := centreTransformer( m, k, k!1, c );
    T1 := centreTransformer( m, k, Nonsquare(k), c );
    params := [ param : param in ClassParametersCO(0,d,F) ];
    reps := [ G | T*paramToMatO(param)*T^-1 
      where T is ((paramToSign(param) eq +1) select T0 else T1) : param in params ];
  end if;
  return reps, params;
end function;

Z := Integers();

paramToCentOrderCO := function( param )
  t := param[1][1];
  F := Parent(t);  P := PolynomialRing(F); X := P.1;
  q := #F;
  order := (q-1);  overcntflag := false;  noovercntflag := false;
  undercntflag := 0;
  for i in [1..#param] do
    k := 0;
    f := param[i][2];  e := Degree( param[i][2]);  spartition := param[i][3];
    for j in [1..#spartition] do
      spart := spartition[j][1]; smult := spartition[j][2];
      part := Abs( spart );
      if IsDivisibleBy( X^2-t, f ) then
        if IsEven( spart ) then //printf "s";
          k +:= smult * ( (part-1)*smult/2 + 
            &+[Z| Abs(spartition[k][1])*spartition[k][2] : k in [1..j-1] ] - 1/2);
          order *:= #Sp( smult, q^e );
        else //printf "o";
          k +:= smult * ( (part-1)*smult/2 + 
             &+[Z| Abs(spartition[k][1])*spartition[k][2] : k in [1..j-1] ] );
          order *:= ( (smult eq 1) select 2 else 
            #InternalGeneralOrthogonalGroup( Sign(spart), smult, GF(q^e) ) );
          if e eq 1 and spart gt 0 and smult eq 1 then // we overcount -I in this case
            overcntflag := true;  
          end if;
          if e eq 1 and smult ne 1 and IsOdd(smult) then
            noovercntflag := true;
          end if;
          if smult ne 1 and IsOdd(smult) then
            undercntflag +:= e;
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
  if undercntflag ge 2 then order *:= 2;  end if;
  return order;
end function;


/*

for d in [1,2,3,4,5,6,7,8,9,10,11,12,13,14] do
  for q in [3] do  //,5,7,9,11] do
    for t in {+1,-1} do
      print d,q,t;
      F := GF(q);  P := PolynomialRing(F); X := P.1;
      G := CO(t,d,q);
  [ <param,t> : param in ClassParametersCO(t,d,F) | t ne 1
    where t is #Centraliser( G, G!paramToMatO(param) ) / paramToCentOrderCO(param) ];   
//      forall(param){ param : param in ClassParametersCO(t,d,F) |
//        #Centraliser( G, G!paramToMatO(param) ) eq paramToCentOrderCO(param) };   
    end for;
  end for;
end for;


d := 8;  t := +1;
for q in [7,9] do
  print d,q,t;
  F := GF(q);  P := PolynomialRing(F); X := P.1;
  G := CO(t,d,q);
  [ <param,t> : param in ClassParametersCO(t,d,F) | t ne 1
    where t is #Centraliser( G, G!paramToMatO(param) ) / paramToCentOrderCO(param) ];   
end for;

d := 6; q := 7; t := +1;
F := GF(q);  P := PolynomialRing(F); X := P.1;
G := CO(t,d,q);
params := ClassParametersCO(t,d,F);
bad := [ param : param in params |
  #Centraliser( G, G!paramToMatO(param) ) ne paramToCentOrderCO(param) ]; 

param := bad[1];
#Centraliser( G, G!paramToMatO(param) );
paramToCentOrderCO(param);

*/



intrinsic InternalClassesExtendedOmega( G ) -> SeqEnum
{Internal function: The conjugacy classes of CO[Plus|Minus](d,q)}
  d := Degree(G); k := BaseRing(G);  q := #k;

  if assigned G`IsStandardClassical and G`IsStandardClassical then
    ordG := #G;
    if IsOdd(q) then
	if G`ClassicalName in ["ConformalOrthogonal","ConformalOrthogonalPlus"] then
	  reps, params := ClassRepresentativesCOOdd(+1, d, q);
	  if IsOdd(d) then
              T := centreTransformer(d div 2, k, k!2, k!1);
	      reps := [G| T*Transpose(r^-1)*T^-1 : r in reps];
	  end if;
	  G`Classes := [ <Order(reps[i]),ordG div paramToCentOrderCO(params[i]),reps[i]> : 
	    i in [1..#reps] ];
	  return true;
	elif G`ClassicalName eq "ConformalOrthogonalMinus" then
	  reps, params := ClassRepresentativesCOOdd(-1, d, q);
	  G`Classes := [ <Order(reps[i]),ordG div paramToCentOrderCO(params[i]),reps[i]> : 
	    i in [1..#reps] ];
	  return true;
	end if;
    end if;
  end if;
  vprint Classes: "Extended Omega tried and failed";

  return false;    
end intrinsic;



/*
checkClassReps := function( G, reps )
  C := Classes(G);  h := ClassMap(G);
  indices := { h(c) : c in reps };
  return #C eq #reps and #indices eq #C;
end function;


for d in [2..14] do
  for q in [3,5,7,9,11] do
    for sgn in (IsEven(d) select [+1,-1] else [0,+1,-1]) do
      d,q,sgn,checkClassReps(CO(sgn,d,q), ClassRepresentativesCOOdd(sgn,d,q));
    end for;
  end for;
end for;

*/


