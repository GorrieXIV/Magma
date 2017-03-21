freeze;

/*
  $Id: linear.m 48480 2014-09-28 02:09:52Z donnelly $

  Sergei Haller and Scott H. Murray
  
  6 November 2008
  
  Conjugacy class code for groups G with SL(n,q) <= G <= GL(n,q).
  This builds on the C-level code written by Sergei Haller.
  It is based on our preprint 
  "Computing conjugacy in finite classical groups 1:
  Similarity in unitary groups".  

*/

/*  Notes

Attach("/magma/murray/package/Group/GrpMat/ClassicalConj/linear.m");
import "/magma/murray/package/Group/GrpMat/ClassicalConj/linear.m":
  

ClassInvariants
ClassRepresentativeFromInvariants(G,p, h, t) 
 Third class invariant ignored for type GL
AssertAttribute(G, "Classes", Q)

Centralisers!!!
*/


// =================================================
//
// Polynomials
//
// =================================================

AllIrreduciblePolynomialsL := function( F, i )
  P := PolynomialRing(F); X := P.1;
  return (i eq 1) select [ X-a : a in F | a ne 0 ] 
    else Setseq( AllIrreduciblePolynomials(F,i) );
end function;
    
// ---------------------------------------------------------------------------
//
// Parameters
//
// Supported subsets: All, Semisimple
//
ClassParametersGL := function( d, q : Subset:="All" )
  F := GF(q);
  P := PolynomialRing(F); X := P.1;
  pols := &cat[ AllIrreduciblePolynomialsL(F,i) : i in [1..d] ];
  if Subset eq "All" then
    parts := [ Partitions(i) : i in [1..d] ];
  elif Subset eq "Semisimple" then
    parts := [ [[1:j in [1..i]]] : i in [1..d] ];
  end if;
  oldparams := [ [] : n in [1..d] ];
  for f in pols do
    params := oldparams;
    for n in [0..d-1] do
      multleft := (d-n) div Degree(f);
      for i in [1..multleft] do 
	for param in ((n ne 0) select oldparams[n] else [[]]) do
	  for part in parts[i] do
	    Append( ~params[n+Degree(f)*i], param cat [<f,part>] );
	  end for;
	end for;
      end for;
    end for;
    oldparams := params;
  end for;
  return params[d];
end function;



/*for d in [1..5] do
  for q in [2,3,4,5] do
    d, q, #ClassParametersGL(d,q) eq NumberOfClasses(GL(d,q));
  end for;
end for;*/



// =================================================
//
// Constructing the groups
//
// =================================================

// representative elt of Delta=GL(n,q) with det=x
detrep := function( Delta, x )
  n := Degree(Delta);
  return Delta!DiagonalMatrix([x] cat [1:i in [1..n-1]]);
end function;

intrinsic ExtendedSL( n::RngIntElt, q::RngIntElt, m::RngIntElt ) -> GrpMat
{The matrix group containing SL(n,q) with index m}
  require m gt 0 : "m must be positive";
  ok, r := IsDivisibleBy( q-1, m );
  require ok : "m must divide q-1";
  Delta := GL(n, q);
  Omega := SL(n, q);  // catch errors!
  x := PrimitiveElement( GF(q) );
  ngens := NumberOfGenerators( Omega );
  G := MatrixGroup< n, q | Append( [ Delta | Omega.i : i in [1..ngens] ], 
    detrep(Delta,x^r) ) >;
  return G;
end intrinsic;

intrinsic RecogniseExtendedSL( G::GrpMat ) -> RngInt
{Find the index of the special linear group inside G}
  require Category( BaseRing(G) ) eq FldFin : "The base field must be finite";
  require IsLinearGroup( G ) : "Group does not contain SL";
  return LCM( [ Integers() | Order(Determinant(g)) : g in Generators(G) ] );
end intrinsic;

intrinsic RecognizeExtendedSL( G::GrpMat ) -> RngInt
{Find the index of the special linear group inside G}
  return RecogniseExtendedSL(G);
end intrinsic;

/* test
for n in [1..6] do 
  for q in [q : q in [2..50] | IsPrimePower(q)] do
    for m in Divisors(q-1) do
      G := ExtendedSL(n,q,m);
      print m, Index( G, SL(n,q) ) eq m,
        RecogniseExtendedSL( G ) eq m;
    end for;
  end for;
end for;
*/

// ====================================================================
//
// Enumerating invariants
//
//  The classes of GL(n,q) correspond to invariants:
//    < P, Lambda >
//  where 
//    P is a sequence of irred polynomials over GF(q) other than X,
//    Lambda is a sequence of partitions,
//  satisying  
//    #P = #Lambda, and
//    sum_i( deg(P[i]) * |Lambda[i]| ) = n.
//  Define
//    det( <P,Lambda> ) = prod_i( (-1)^deg(P[i]) * P[i](0) )^|Lambda[i]|
//  If the elt x has invariant <P,Lambda>, then det(x)= det(<P,Lambda>).
//
//  Let F = GF(q).  Let m|(q-1).
//  Define F(m) = { x in F^* | x^m=1 }, 
//  the unique subgroup of F^* of order m.
//  Note that
//    F(m1) F(m2) = F(lcm(m1,m2)),  F(m1) meet F(m2) = F(gcd(m1,m2)),
//    F(l) <= F(m) iff l|m.
//  A transversal of F^*/F(m) is given by
//    T(m) = { xi^(m+i) : i=0,...(q-1)/m-1 }
//  Also
//     SLExt(n,q,m) = det^-1(F(m))
//
//  Let C = centraliser in GL(n,q) of elt x with invariant <P,Lambda>.  
//  Then det(C) = F(m_Lambda) where 
//    m_Lambda = (q-1) / gcd( q-1, Lambda[i,j] : i,j ).
//  Suppose that x is in SLExt(n,q,m)  [ie, (det<P,Lambda>)^m=1].
//  The SLExt(n,q,m)-classes under x correspond to elements of
//    F^* / F(lcm(m,m_Lambda))
//
//  So, the classes of SLExt(n,q,m) corresp to invariants
//    < P, Lambda, a >
//  where
//    < P, Lambda > as above with det( <P,Lambda> )^m=1, and
//    a is in T(lcm(m,m_Lambda))
//
// ====================================================================

// size of a partition
partSize := func< lambda | &+lambda >;

// determinant of an invariant
invDet := func< inv | 
  &*[ ( (-1)^Degree(f) * Evaluate(f,0) ) ^ partSize(lambda)
    where f is inv[1][i] where lambda is inv[2][i] : i in [1..#inv[1]] ] >;

m_Lambda := func< q, Lambda | 
  (q-1) div GCD( Append(Flat( Lambda ), q-1) ) >;



/* test
n := 4;  q := 3;  
G := GL(n,q);
C := Classes( GL(n,q) );
for c in C do
  x := c[3];  P,Lambda := ClassInvariants(G,x);
  invDet( <P,Lambda> ) eq Determinant(x);
end for;
*/

intrinsic InternalSemisimpleClassesGL( d, q ) -> SeqEnum
{Internal function: The semisimple conjugacy classes of GL}
  C := ClassParametersGL( d, q : Subset:="Semisimple" );
  return [ ClassRepresentativeFromInvariants( GL(d,q),
    [ c[i][1] : i in [1..#c] ], [ c[i][2] : i in [1..#c] ], GF(q)!1 ) :
    c in C ];
end intrinsic;


// Enumerate all invariant tuples for a give SL extension
intrinsic InternalClassesExtendedSL( G::GrpMat ) -> BoolElt, SeqEnum, SeqEnum
{Internal function: The conjugacy classes of the extension of SL}
  try
    m := RecogniseExtendedSL( G );
  catch e
    return false, _, _;
  end try;
  vprint Classes: "Linear type group -- compute GL classes";
  n := Degree( G );
  F := BaseRing( G );  q := #F;  xi := PrimitiveElement(F);
  Delta := GL(n,q);  C_GL := Classes( Delta );

  vprint Classes: "Splitting GL classes";
  // a transversal of F^*/F(l)
  transv := function( l, r )
    return { xi^(l+i) : i in [0..r-1] };
  end function;

  Z := Integers();
  C := [car<Z,Z,G>|];  Inv := [];
  FGrps := [];
  for i in [1..#C_GL] do
    x := Matrix( C_GL[i][3] );  
    P, Lambda := OldClassInvariants( Delta, i );
    inv := <P,Lambda>;
    if invDet(inv)^m eq 1 then
      l := LCM(m,m_Lambda(q,Lambda));  //Fm(~FGrps,r);
      r := (q-1) div l;
      for a in transv(l,r) do
        Append( ~Inv, <P,Lambda,a> );
        y := x;  y[1] := a^-1*y[1];
        for j in [1..n] do y[j,1] := a*y[j,1]; end for;
        //print x, inv, a;
        Append( ~C, < C_GL[i][1], C_GL[i][2] div r, G!y> );
      end for;
    end if;
  end for;
  if not assigned G`Classes then
    G`Classes := C;
  end if;
  return true, C, Inv;
end intrinsic;

/* Tests
SetVerbose("Classes",0);

checkClasses := function( G, C )
  C0 := Classes(G);  h := ClassMap(G);
  indices := { h(c[3]) : c in C };
  if &+[ c[2] : c in C ] ne #G then
    error "Bad class len";
  end if;
  if exists{ c : c in C | C0[h(c[3])][1] ne c[1] or C0[h(c[3])][2] ne c[2] } then
    error "bad class len/order";
  end if;
  return #C eq #C0 and #indices eq #C;
end function;

for n in [3..6] do 
  for q in [q : q in [2..50] | IsPrimePower(q)] do
    for m in Divisors(q-1) do
      G := SLExtension( n, q, m );
      time C0 := Classes( G );
      time C, Inv := ClassesSLExtension( n, q, m );
      print n, q, m, checkClasses( G, C );
    end for;
  end for;
end for;



n := 4;  q := 5;  m := 1;
G := SLExtension( n, q, m );
C0 := Classes( G );
C, Inv := ClassesSLExtension( n, q, m );
checkClasses( G, C );



n := 4;  q := 5;  m := 1;
F:=GF(q);
G := SLExtension( n, q, m );
C0 := Classes( G );
C, Inv := ClassesSLExtension( n, q, m );

Delta := GL(n,q);
C_GL := Classes( Delta );
Inv_GL := [];
for i in [1..#C_GL] do
  P, Lambda := ClassInvariants( Delta, i );
  Append( ~Inv_GL, <P,Lambda> );
end for;

invPair := function( g )
  Delta := Generic( Parent(g) );
  P, Lambda := ClassInvariants(Delta, g);
  return <P,Lambda>;
end function;

for i in [1..#Inv_GL] do
  inv := Inv_GL[i];
  P := inv[1];  Lambda := inv[2];
  num0 := #{ c : c in C0 | invPair(c[3]) eq inv };
  num := #{ c : c in C | invPair(c[3]) eq inv };
  if num ne num0 then
    print i, num0, num;
  end if;
end for;

*/


