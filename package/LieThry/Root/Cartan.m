freeze;

/*
  $Id: Cartan.m 43816 2013-07-09 07:25:57Z don $

  Arjeh Cohen, Scott H Murray and D E Taylor

  30 November 2000

  This is a Magma package for computing with various descriptions of
  Coxeter systems.  The descriptions used are:
  1. Coxeter matrices,
  2. Cartan matrices,
  3. Coxeter graphs,
  4. Dynkin digraphs (crystallographic groups only),
  5. Dynkin diagrams (finite and affine groups only),
  6. Cartan types    (finite and affine groups only),
  7. Cartan names    (finite and affine groups only).

  We now discuss each of these descriptions in detail.

  1. Coxeter matrices
     Definition: a symmetric square matrix M = [ m_ij ]
     with values in {1,2,3,...,infinity}, every m_ii = 1
     and m_ij > 1 for i ne j.

     We represent Coxeter matrices by integral matrices, using
     0 instead of infinity.

     The corresponding Coxeter group has generators s_i and relations
         s_i^2 = 1;  and
         s_i s_j s_i ... = s_j s_i s_j ... where both sides have length m_ij.

     Alternatively, the relations can be written
         (s_i s_j)^m_ij = 1.

     In both cases the relation is omitted if m_ij is infinite.

  2. Cartan matrices
     Definition: a square real matrix C = [ c_ij ] with
       a. c_ii = 2,
       b. c_ij <= 0  for  i ne j,
       c. c_ij = 0 iff c_ji = 0,
       d. Let n_ij := c_ij c_ji.  If n_ij < 4, then
          n_ij = 4 cos^2(pi/m_ij) for some integer m_ij >= 2.

     We allow these matrices to be defined over integers, rationals,
     number fields, or cyclotomic fields.
     We consider a number c to be real if Conjugates(c)[1] is real.
     This is also used to determine positivity.
     
     The corresponding Coxeter matrix M has  m_ii = 1;
     m_ij as in (d) when n_ij < 4;  m_ij = infinity when n_ij >= 4.

     A Cartan matrix with integral entries is said to be crystallographic.
     Possible integral values:
       m_ij   2  3  4  6  infinity
       n_ij   0  1  2  3    > 4

  3. Coxeter graph
     A Coxeter graph is an undirected edge-labelled graph corresponding to
     a Coxeter matrix M.  The vertices correspond to rows/cols of M.
     There is an edge  i ------ j  iff m_ij > 2.  We may omit labels equal to 3.
                          m_ij
     Once again we use 0 to represent infinity.

  4. Dynkin digraph (crystallographic groups only)
     A Dynkin digraph is a directed graph corresponding to a crystallographic
     Cartan matrix C.  The vertices correspond to rows/cols of M.
     There is an edge  i -------> j  iff  c_ij ne 0.  We may omit labels equal to 1.
                          -c_ij
     There is no Dynkin digraph corresponding to a Coxeter matrix or
     Coxeter graph.

  5. Dynkin diagram, Coxeter diagram (finite and affine groups only)
     In our case, the Dynkin (Coxeter) diagram is just a printout of the 
     Dynkin digraph (Coxeter graph) a finite or affine group, 
     together with its name.
     Vertices are numbered according to the system of Bourbaki.

          1   2      n-1  n
     A_n  o---o- ... -o---o

          1   2      n-1  n
     B_n  o---o- ... -o=>=o

          1   2      n-1  n
     C_n  o---o- ... -o=<=o

                        o n-1
          1   2        /
     D_n  o---o- ... -o
                       \
                        o n

          1   3   4   5   6
     E_6  o---o---o---o---o
                  |
                2 o


          1   3   4   5   6   7
     E_7  o---o---o---o---o---o
                  |
                2 o

          1   3   4   5   6   7   8
     E_8  o---o---o---o---o---o---o
                  |
                2 o

          1   2   3   4
     F_4  o---o=>=o---o


          1   2
     G_2  o=<=o
            3

     For types H and I_2(m) (m=5 or m>6) the
     Cartan matrix cannot be crystallographic

          1   2   3
     H_3  o---o---o
            5


          1   2   3   4
     H_4  o---o---o---o
            5


     I_2(m) o---o
              m
	      
     Corresponding to each finite crystallographic group there
     is an affine group.  Their Dynkin diagrams are:
	      
             1       2
     A~_1    o-------o
               infty

             1   2      n-1  n
     A~_n    o---o- ... -o---o
             |               |
	     --------o--------
	            n+1

             1 o   
                \       n-1  n
     B~_n      2 o- ... -o=>=o
                /
	   n+1 o


            n+1  1   2      n-1  n
     C~_n    o=>=o---o- ... -o=<=o


             1 o           o n-1
                \         /
     D~_n      2 o- ... -o
                /         \
           n+1 o           o n


            1   3   4   5   6
     E~_6   o---o---o---o---o
                    |
                    o 2
                    |
		    o 7

            8   1   3   4   5   6   7
     E~_7   o---o---o---o---o---o---o
                        |
                      2 o
	      
            1   3   4   5   6   7   8   9
     E~_8   o---o---o---o---o---o---o---o
                    |
                  2 o

            5   1   2   3   4 
     F~_4   o---o---o=>=o---o


            1   2   3
     G~_2   o=<=o---o
              6


  6. Cartan type (finite and affine groups only)
     A simple Cartan type is a pair <t, l> with t in
     {"A",...,"H","A~",..."E~"} or a triple <"I", l, m>, 
     where l is a list of rows/columns.  A compound Cartan type
     is a list of types.  Cartan types are for
     internal use only -- the users only see Cartan names.

  7. Cartan name (finite and affine groups only)
     A string describing a Cartan type.  Note that lowercase letters
     are allowed for input, but they will automatically be converted
     to uppercase.
     
*/





// =================================================
//
// Conversion functions for matrices and (di)graphs
//
// =================================================

// -------------------------------------------------
//
// Utilities
//
// These should become unnecessary in a future
// release, as they become standard Magma intrisics.
//

// This function returns the components of G, including labels
LabelledComponents := function( G )
  E := EdgeSet(G);
  f := func< x, y | Index(x)-Index(y) >;
  comps := [ Sort(Setseq(c),f) : c in Components(G) ];
  Comps := [];
  for comp in comps do
    Comp := EmptyGraph( #comp );
    for i in [1..#comp] do
      u := comp[i];
      if IsLabelled( u ) then
        AssignLabel( Comp, i, Label(u) );
      end if;
      for j in [i+1..#comp] do
        v := comp[j];
        if u adj v then
          e := E!{u,v};
          if IsLabelled( e ) then
            AddEdge( ~Comp, i, j, Label(e) );
          else
            AddEdge( ~Comp, i, j );
          end if;
        end if;
      end for;
    end for;
    Append( ~Comps, Comp );
  end for;
  return Comps, comps;
end function;

// Are G and H isomorphic as *edge-labelled* graphs.
// This function is very inefficient, but we will mostly be using it for
// small graphs.
IsIsomorphicLabelPreserving := function( G, H )
  EG := EdgeSet( G );    EH := EdgeSet( H );
  VG := VertexSet( G );  VH := VertexSet( H );
  sameLabels := func< e, f |
    ( not IsLabelled(e) and not IsLabelled(f) ) or
    ( IsLabelled(e) and IsLabelled(f) and Label(e) eq Label(f) ) >;
  image := (Category(G) eq GrphUnd)
    select func< e, iso | EH!{ iso(v) : v in EndVertices(e) } >
    else   func< e, iso | EH![ iso(v) : v in EndVertices(e) ] >;
  isLabelPreserving := func< iso |
    forall{ e : e in EG | sameLabels( e, image( e, iso ) ) } >;

  // find an isomorphism, not preserving labels
  isIso, iso := IsIsomorphic( G, H );
  if isIso then
    A, AVH := AutomorphismGroup( H );
    
    // composition of an isomorphism and an automorphism 
    compose := func< iso, a |
      hom< VG -> VH | v :-> Image( a, AVH, iso(v) ) >  >;

    for a in A do
      compIso := compose( iso, a );
      if isLabelPreserving( compIso ) then
        VHs := Vertices( H );
        ims := [ Position( VHs, compIso(VG.i) ) : i in [1..#VG] ];
        return true, ims;
      end if;
    end for;
    return false, _;
  else
    return false, _;
  end if;
end function;

// -------------------------------------------------
//
// Real injections
//

hasRealInj := function( k )
  if Category( k ) in {RngInt,FldRat,FldCyc} then
    return true;
  else 
    // this relies on the fact that real valued conjugates are always put first
    a := PrimitiveElement( k );
    return IsReal( Conjugates( a )[1] );
  end if;
end function;

stdRealInj := function( k )
  if Category( k ) in [ FldRat, RngInt ] then
    return Coercion( k, RealField() );
  else
    conjs := Conjugates( k.1 );
    idx := 1;

    // This is an attempt to choose the same injection used in 
    // CartanMatrix.  It works for all the finite types (H & I),
    // but may not work in general.
    if ISA( Category(k), FldCyc ) then
      // we need to ensure that there are no small complex errors for real elts
      return map< k -> ComplexField() |
        a :-> IsReal(a) select Real(im) else im
	where im is Conjugates( a )[idx] >;
    else
      realidx := [ idx : idx in [1..#conjs] | IsReal(conjs[idx]) ];
      if not IsEmpty( realidx ) then
        _, i := Maximum( [ Abs(conjs[idx]) : idx in realidx ] );
        idx := realidx[i];
      end if;
      return map< k -> RealField() | a :-> Real( Conjugates( a )[idx] ) >;
    end if;
  end if;
end function;


// Compare real injections
// 1st value: true, false, or an error message if the fields are incompatible
// 2nd value: a covering field
// 3rd value: covering injection
// 4th/5th values the maps into the covering field
cmpRealInj := function( inj1, inj2 )
  k1 := Domain( inj1 );  k2 := Domain( inj2 );

  // construct the covering field/injection
  if k1 cmpeq k2 or k2 cmpeq Rationals() or k2 cmpeq Integers() then
    K := k1;  inj := inj1;
  elif k1 cmpeq Rationals() or k1 cmpeq Integers() then
    K := k2; inj := inj2;
  elif Category( k1 ) eq Category( k2 ) then
    if k1 subset k2 then
      K := k2;  inj := inj2;
    elif k2 subset k1 then
      K := k1;  inj := inj1;
    elif Category( k1 ) eq FldCyc then
      n1 := CyclotomicOrder( k1 );  n2 := CyclotomicOrder( k2 );
      g,x,y := XGCD( n1, n2 );
      K := CyclotomicField( (n1*n2) div g );
      inj := hom< K -> ComplexField() | inj1(k1.1)^y * inj2(k2.1)^x >;
      inj := hom< K -> ComplexField() | x :->
        IsReal(x) select Real(inj(x)) else inj(x) >;
    else
      return "Incompatible base fields", _,_,_,_;
    end if;
  else
    return "Incompatible base fields", _,_,_,_;
  end if;
  
  // the maps into the covering field
  h1 := Coercion( k1, K );  h2 := Coercion( k2, K );
  
  // check the injections
  for i in [1,2] do
    k := (i eq 1) select k1 else k2;
    h := (i eq 1) select h1 else h2;
    injk := (i eq 1) select inj1 else inj2;
    gens := (Category(k) notin {FldCyc,FldNum}) select [] else Generators(k);
    for x in gens do
      conjs := Conjugates( x );
      _, pos1 := Minimum( [ Abs( inj(h(x)) - c ) : c in conjs ] );
      _, pos2 := Minimum( [ Abs( injk(x) - c ) : c in conjs ] );
      if pos1 ne pos2 then
        return false, _,_,_,_;
      end if;
    end for;
  end for;

  return true, K, inj, h1, h2;
end function;





// -------------------------------------------------
//
// Converting matrices
//

// Given n_ij = c_ij*c_ji, try to find an integer m_ij>2
// such that n_ij = 4cos^2(pi/m_ij).
//
// Note that cos^2(pi/m_ij) is always an algebraic number --
// this function does not use real approximation, except to check inequalities.
// Since e^(i pi/m_ij) = cos(pi/m_ij) + i sin(pi/m_ij)
// is a root of the m_ij-th cyclotomic polynomial,
// we need to test that n_ij satisfies
// 
findmij := function( nij, realinj )
  // When this function is called, nij is guaranteed to be real and positive
  case nij :
  when 0 : return true,2;
  when 1 : return true,3;
  when 2 : return true,4;
  when 3 : return true,6;
  when 4 : return true,0;
  else
    f := MinimalPolynomial( nij );
    P<x> := Parent( f );  F<y> := FieldOfFractions( P );
    phi := P!( y^Degree(f) * Evaluate( F!f, 2+y+y^-1 ) );
    cycl, n := IsCyclotomicPolynomial( phi );
    nr := realinj( nij );
    if cycl then
      // test that we have the correct solution
      pi := Pi( RealField() );
      return Abs(nr-4*Cos(pi/n)^2) lt Abs(nr-4*Cos(2*pi/n)^2), n;
    else
      return nr ge 4, 0;
    end if;
  end case;
end function;

// This returns the Coxeter matrix, or a string containing the appropriate
// error message.  It is used by IsCartanMatrix and CoxeterMatrix.
cartanToCoxeter := function( C : realinj:=false )
  n := Nrows( C );  k := BaseRing( C );
  if n eq 0 then
    return Matrix( Integers(), 0, 0, [Integers()|] ), stdRealInj(Integers());  
  end if;
  if not exists{ ct : ct in {RngInt,FldRat,FldCyc,FldNum} | 
  ISA( Category( k ), ct ) } then
    return "a Cartan matrix must be defined over integers, rationals, a cyclotomic field, or a number field", _;
  end if;
  if Category( realinj ) eq BoolElt then
    if hasRealInj( k ) then
      realinj := stdRealInj( k );
    else
      return "the base field has no injection into the real field", _;
    end if;
  end if;
  isReal := func< x | (Category( k ) eq FldCyc) select IsReal(x) else true >;
  for i in [1..n] do
    for j in [1..n] do
      si := IntegerToString(i);  sj := IntegerToString(j);
      if i eq j then 
        if C[i,j] ne 2 then
          return "The entry at position <" cat si cat "," cat si 
            cat "> must be 2", _;
        end if;
      else
        if not isReal( C[i,j] ) then
          return "The entry at position <" cat si cat "," cat sj 
            cat "> must be real", _;
        elif Category( realinj ) ne BoolElt and Real( realinj( C[i,j] ) ) gt 0 then
          return "The entry at position <" cat si cat "," cat sj 
            cat "> must be nonpositive", _;
        end if;
      end if;
    end for;
  end for;
  M := [1];
  for i in [2..n] do
    for j in [1..i-1] do
      si := IntegerToString(i);  sj := IntegerToString(j);
      if (C[i,j] eq 0) eq (C[j,i] ne 0) then
        return "The entries at positions <" cat si cat "," cat sj cat "> and <"
        cat sj cat "," cat si cat "> must both be zero or both be nonzero", _;
      end if;
      ok, mij := findmij( C[i,j] * C[j,i], realinj );
      if not ok then
        return "C[" cat si cat "," cat sj cat "] * C[" cat sj cat "," cat si cat
          "] must be greater than 4, or equal to 4cos^2(pi/m) for some integer m",
          _;
      end if;
      Append( ~M, mij );
    end for;
    Append( ~M, 1 );
  end for;
  return SymmetricMatrix(M), realinj;
end function;

intrinsic CoxeterMatrix( C::Mtrx : RealInjection:=false ) -> AlgMatElt
{The Coxeter matrix of the Cartan matrix C}
  M, _ := cartanToCoxeter( C : realinj:=RealInjection );
  error if Category( M ) ne AlgMatElt, M;
  return M;
end intrinsic;

//
// Given a polynomial f(x), its dual is 
//   f~(x) = x^d f(1/x)    d = deg(f).
// Also define
//   f^(x) = x^d f(x+1/x) 
// which is selfdual of degree 2d.
// 
// Suppose p is selfdual.
// Then p has even degree n=2d and there
// is a unique polynomial f st p=f^.
// The following function computes f given p.
//
unhat := function( p )
  F<x> := Parent( p );  ret := [];
  n := Degree( p ) div 2;
  for i in [1..n+1] do
    co := Coefficient( p, 2*n-i+1);
    p := p - co * (x^2+1)^(n-i+1) * x^(i-1);
    Append( ~ret, co );
  end for;
  return F!Reverse(ret);
end function;

// assuming x = xi+xi^-1 return [ xi^n+xi^-n : n in [1..power] ]
twocospis := function( x, power )
  ret := [ x ];  xton := x;
  for n in [2..power] do
    xton *:= x;  y  := xton;
    for i in [1..((n-1) div 2)] do
      y -:= Binomial(n,i) * ret[n-2*i];
    end for;
    if n mod 2 eq 0 then
      y -:= Binomial(n,n div 2);
    end if;
    ret[n] := y;
  end for;
  return ret;
end function;

intrinsic CartanMatrix( M::AlgMatElt[RngInt] : Symmetric := false, 
  BaseField := "NumberField" ) -> AlgMatElt, Map
{A Cartan matrix of the Coxeter matrix M}
  case BaseField :
  when "SparseCyclotomic", "Cyclotomic" :
    Cyclotomic := true;  Sparse := true;
  when "DenseCyclotomic" :
    Cyclotomic := true;  Sparse := false;
  when "NumberField" :
    Cyclotomic := false;
  else
    error "invalid base field parameter";
  end case;
  
  n := Ncols(M);
  if n eq 0 then  
    return Matrix( Integers(),0,0,[] ), stdRealInj( Integers() );  
  end if;
  require IsSymmetric( M ) : "Argument must be symmetric";
  require forall(i){ i : i in [1..n] | M[i,i] eq 1 } : 
    "Diagonal entry not 1 at position",i;
  require forall(i,j){ <i,j> : j in [i+1..n], i in [1..n-1] | M[i,j] eq 0 or M[i,j] gt 1 } :
    "Off-diagonal entry at <",i,",",j,"> must be 0 or greater than 1";

  // m is the lcm of the M[i,j] for which C[i,j] is not integral
  m := Lcm( [ Integers() | M[i,j] : j in [i+1..n], i in [1..n-1] | 
    M[i,j] notin (Symmetric select [0,2,3] else [0,2,3,4,6]) ] );

  // compute the field and real injection
  if m eq 1 then
    F := Integers();  twocospi:=[]; // twocospi is not used
  elif Cyclotomic then
    F := CyclotomicField( IsEven(m) select 2*m else m : Sparse:=Sparse );
    // xi is exp(2*pi/m) in the first conjugate map
    xi := IsEven(m) select F.1 else -(F.1)^((m+1) div 2);
    twocospi := func< mij | xi^n+xi^-n
      where n is (m div mij) >;
  else
    F := NumberField( unhat( CyclotomicPolynomial( 2*m ) ) );
    entries := twocospis( F.1, 2*m );
    twocospi := func< mij | entries[m div mij] >;
    conjs := Conjugates( entries[1] );
    realidx := [ idx : idx in [1..#conjs] | IsReal(conjs[idx]) ];
/*    pi := Pi( RealField() );
    _,i := Minimum( [ Abs(conjs[idx]-2*Cos(pi/(m))) : idx in realidx ] );
    realinj := map< F -> Re | a :-> Real( Conjugates( a )[realidx[i]] ) >;*/
  end if;
  realinj := stdRealInj( F );
  
  // compute the matrix
  C := MatrixAlgebra( F, n )!2;
  for i in [1..n-1] do
    for j in [i+1..n] do
      if Symmetric then
        cij := case< M[i,j] | 2:0, 3:-1, 0:-2, 
          default:-twocospi(M[i,j]) >;
        C[i,j] := cij;  C[j,i] := cij;
      else
        C[i,j] := case< M[i,j] | 2:0, 3:-1, 4:-2, 6:-3, 0:-4, 
          default:(IsOdd(M[i,j]) select 
	  -twocospi(M[i,j]) else -twocospi(M[i,j])^2) >;  
        C[j,i] := case< M[i,j] | 2:0, 
	  default:(IsOdd(M[i,j]) select C[i,j] else -1) >;
      end if;
    end for;
  end for;
  return C, realinj;

end intrinsic;

// -------------------------------------------------
//
// Checking matrices
//
intrinsic IsCoxeterMatrix( M::AlgMatElt ) -> BoolElt
{True iff M is a Coxeter matrix}
  n := Ncols(M);
  return Category(BaseRing(M)) eq RngInt and IsSymmetric( M ) and
    forall{ i : i in [1..n] | M[i,i] eq 1 } and
    forall{ <i,j> : j in [i+1..n], i in [1..n-1] | M[i,j] ge 2 or M[i,j] eq 0 };
end intrinsic;

intrinsic IsCartanMatrix( C::AlgMatElt : RealInjection := false ) -> 
  BoolElt, Map
{True iff C is a Cartan matrix}
  M, realinj := cartanToCoxeter( C : realinj:=RealInjection );
  if assigned realinj then 
    return Category( M ) eq AlgMatElt, realinj;
  else
    return Category( M ) eq AlgMatElt, _;
  end if;
end intrinsic;

// -------------------------------------------------
//
// Converting types
//
function removeTorusFromType( type : Isogenies := false )
  torpos := [ i : i in [#type..1 by -1] | type[i][1] eq "T" ];

  for p in torpos do
    Remove(~type, p);
    if (Type(Isogenies) ne BoolElt) then Remove(~Isogenies, p); end if;
  end for; 

  if (Type(Isogenies) ne BoolElt) then
    return type, Isogenies;
  else
    return type;
  end if;
end function;
function selectTorusFromType( type )
  return [* t : t in type | t[1] eq "T" *];
end function;
function addTorusToType( R, type )
  if Dimension(R) ne Rank(R) then 
    assert Dimension(R) gt Rank(R);
    mx := Maximum([ Maximum(t[2]) : t in type ]);
    Append(~type, <"T", [], Dimension(R)-Rank(R) >);
  end if;
  return type;
end function;


// -------------------------------------------------
//
// Checking graphs
//
intrinsic IsCoxeterGraph( G::GrphUnd ) -> BoolElt
{True iff G is a Coxeter graph}
  V := Vertices( G );  n := #V;
  L := Labels( EdgeSet( G ) );
  return //G eq StandardGraph(G) and
    (IsNull( L ) or Category( Universe( L ) ) eq RngInt ) and
    forall{ l : l in L | l eq 0 or l ge 3 };
end intrinsic;

intrinsic IsDynkinDigraph( D::GrphDir ) -> BoolElt
{True iff D is a Dynkin digraph}
  V := Vertices( D );  n := #V;
  L := Labels( EdgeSet( D ) );
  return //D eq StandardGraph(D) and
    (IsNull( L ) or Category( Universe( L ) ) eq RngInt ) and
    forall{ l : l in L | l eq 0 or l ge 2 } and
    forall{ <i,j> : j in [i+1..n], i in [1..n-1] |
      (V[i] adj V[j]) eq (V[j] adj V[i])  };
end intrinsic;

// -------------------------------------------------
//
// Converting (di)graphs to matrices
//
intrinsic CoxeterMatrix( G::GrphUnd ) -> AlgMatElt
{The Coxeter matrix of the Coxeter graph G}
//  require G eq StandardGraph(G) : "G must be a standard graph";
  V := VertexSet( G );  E := EdgeSet( G );  n := #V;  L := Labels( E );
  require IsNull( L ) or Category( Universe( L ) ) eq RngInt :"The labels must be integers";
  M := SymmetricMatrix( Integers(), [ i eq j select 1 else 2 : j in [1..i], i in [1..n] ] );
  for u in V do
    i := Index(u);
    for v in Neighbours(u) do
      j := Index(v);  e := E!{u,v};
      c := (IsLabelled(e)) select Label(e) else 3;
      require c eq 0 or c ge 3 : "The label on edge <",i,",",j,"> must be 0 or greater than 2";
      M[i,j] := c;
    end for;
  end for;
  return M;
end intrinsic;

intrinsic CartanMatrix( G::GrphUnd : Symmetric:=false, 
BaseField :="NumberField" ) -> AlgMatElt
{A Cartan matrix of the Coxeter graph G}
  return CartanMatrix( CoxeterMatrix( G ) :
    Symmetric:=Symmetric, BaseField:=BaseField );
end intrinsic;

intrinsic CartanMatrix( D::GrphDir ) -> AlgMatElt
{The crystallographic Cartan matrix of the Dynkin digraph D}
//  require D eq StandardGraph(D) : "G must be a standard graph";
  V := VertexSet( D );  E := EdgeSet( D );  n := #V;  L := Labels( E );
  require IsNull( L ) or Category( Universe( L ) ) eq RngInt :"The labels must be integers";
  C := MatrixAlgebra( Integers(), n )!2;
  // C := SparseMatrix(n,n,[<i,i,2>:i in [1..n]]); // diagonal scalar 2
  for u in V do
    i := Index(u);
    for v in OutNeighbours(u) do
      j := Index(v);  e := E![u,v];
      require v adj u : "There must be an edge <",j,",",i,"> if there is an edge <",i,",",j,">"; 
      C[i,j] := (IsLabelled(e)) select -Label(e) else -1;
      require C[i,j] lt 0 : "The label on edge <",i,",",j,"> must be greater than 0";
    end for;
  end for;
  return C;
end intrinsic;

intrinsic CoxeterMatrix( D::GrphDir ) -> AlgMatElt
{The Coxeter matrix of the Dynkin digraph D}
  return CoxeterMatrix( CartanMatrix( D ) );
end intrinsic;



// -------------------------------------------------
//
// Converting matrices to (di)graphs
//
intrinsic CoxeterGraph( M::AlgMatElt : RealInjection:=false) -> GrphUnd
{The Coxeter graph of the Coxeter (Cartan) matrix M}
  n := Ncols(M);
  if not IsCoxeterMatrix(M) then
    M := CoxeterMatrix( M : RealInjection:=RealInjection );  
  end if;
  G := Graph<n|>;
  for i in [1..n-1] do
    for j in [i+1..n] do
      m := M[i,j];
      if m eq 3 then
        AddEdge( ~G, i, j );
      elif m ne 2 then
        AddEdge( ~G, i, j, m );
      end if;
    end for;
  end for;
  return G;
end intrinsic;

// Note: there is no digraph corresponding to a Coxeter matrix
intrinsic DynkinDigraph( C::AlgMatElt ) -> GrphDir
{The Dynkin digraph of the crystallographic Cartan matrix C}
  n := Ncols(C);
  require IsCoercible( MatrixRing(Integers(),n), C ) : 
    "the Cartan matrix must be crystallographic";
  C := ChangeRing( C, Integers() );
  require forall{ i : i in [1..n] | C[i,i] eq 2 } :
    "a Cartan matrix must have 2s on the diagonal";
  D := Digraph<n|>;
  for i in [1..n] do
    for j in [1..i-1] cat [i+1..n] do
      if C[i,j] eq -1 then
        AddEdge( ~D, i, j );
      elif C[i,j] le -2 then
        AddEdge( ~D, i, j, -C[i,j] );
      elif C[i,j] gt 0 then
        error "not a Cartan matrix";
      end if;
    end for;
  end for;
  return D;
end intrinsic;

// -------------------------------------------------
//
// Converting Dynkin digraphs to Coxeter graphs
//
intrinsic CoxeterGraph( D::GrphDir ) -> GrphUnd
{The Coxeter graph of the Dynkin digraph D}
  require IsDynkinDigraph( D ) : "Not a Dynkin digraph";
  V := VertexSet( D );  E := EdgeSet( D );
  n := #V;  G := Graph<n|>;
  realinj := stdRealInj(Integers());
  for u in V do
    i := Index(u);
    for v in OutNeighbours(u) do
      j := Index(v);
      if i lt j then
        e := E![u,v];  f := E![v,u];
        nij := (IsLabelled(e)) select Label(e) else 1;
        nij *:= (IsLabelled(f)) select Label(f) else 1;
        if nij eq 1 then
          AddEdge( ~G, i, j );
        else
	  ok, mij := findmij( nij, realinj );
	  if ok then
            AddEdge( ~G, i, j, mij );
	  else
	    error "incorrect label";
	  end if;
        end if;
      end if;
    end for;
  end for;
  return G;
end intrinsic;


// =================================================
//
// Conversion functions for finite/affine group types
//
// =================================================

// -------------------------------------------------
//
// Converting types to (di)graphs
//
typeToCoxeterGraph := function( type )

  addPath := procedure( ~G, P )
    for i in [1..#P-1] do
      AddEdge( ~G, P[i], P[i+1] );
    end for;
  end procedure;

  addSimple := procedure( ~G, t )
    S := t[2];
    if #t[1] gt 1 and t[1][2] eq "~" then
      Prune(~S);
    end if;
    n := #S;
    case t[1][1]:
    when "A":
      addPath( ~G, S );
    when "B", "C":
      addPath( ~G, S );
      if n gt 1 then
        AssignLabel( G, S[n-1], S[n], 4 );
      end if;
    when "D":
      addPath( ~G, Prune(S) );
      if n gt 2 then
        AddEdge( ~G, S[n-2], S[n] );
      end if;
    when "E":
      addPath( ~G, Remove(S,2) );
      AddEdge( ~G, S[2], S[4] );
    when "F":
      addPath( ~G, S );
      AssignLabel( G, S[2], S[3], 4 );
    when "G":
      addPath( ~G, S );
      AssignLabel( G, S[1], S[2], 6 );
    when "H":
      addPath( ~G, S );
      AssignLabel( G, S[1], S[2], 5 );
    when "I":
      addPath( ~G, S );
      AssignLabel( G, S[1], S[2], t[3] );
    end case;
    if #t[1] gt 1 and t[1][2] eq "~" then
      S := t[2];
      n := #S;
      case t[1][1]:
      when "A":
        AddEdge( ~G, S[1], S[n] );
        if n eq 2 then
          AssignLabel( G, S[1], S[2], 0 );
        else
          AddEdge( ~G, S[n-1], S[n] );
        end if;
      when "B":
        AddEdge( ~G, S[2], S[n] );
      when "C":
        AddEdge( ~G, S[1], S[n], 4 );
      when "D":
        AddEdge( ~G, S[2], S[n] );
      when "E":
        if n eq 7 then
          AddEdge( ~G, S[2], S[n] );
        elif n eq 8 then
          AddEdge( ~G, S[1], S[n] );
        else
          AddEdge( ~G, S[n-1], S[n] );
        end if;
      when "F":
        AddEdge( ~G, S[1], S[n] );
      when "G":
        AddEdge( ~G, S[n-1], S[n] );
      end case;
    end if;
  end procedure;

  if #type eq 0 then  return Graph<0|>;  end if;
  G := EmptyGraph( Max( &cat[ t[2] : t in type ] ) );
  for t in type do
    addSimple( ~G, t );
  end for;
  return G;
end function;

typeToDynkinDigraph := function( type )
  addPath := procedure( ~G, P )
    for i in [1..#P-1] do
      AddEdge( ~G, P[i], P[i+1] );  AddEdge( ~G, P[i+1], P[i] );
    end for;
  end procedure;

  addSimple := procedure( ~G, t )
    S := t[2];
    if #t[1] gt 1 and t[1][2] eq "~" then
      Prune(~S);
    end if;
    n := #S;
    case t[1][1]:
    when "A":
      addPath( ~G, S );
    when "B":
      addPath( ~G, S );
      if n gt 1 then
        AssignLabel( G, S[n-1], S[n], 2 );
      end if;
    when "C":
      addPath( ~G, S );
      if n gt 1 then
        AssignLabel( G, S[n], S[n-1], 2 );
      end if;
    when "D":
      addPath( ~G, Prune(S) );
      if n gt 2 then
        AddEdge( ~G, S[n-2], S[n] );
        AddEdge( ~G, S[n], S[n-2] );
      end if;
    when "E":
      addPath( ~G, Remove(S,2) );
      AddEdge( ~G, S[2], S[4] );
      AddEdge( ~G, S[4], S[2] );
    when "F":
      addPath( ~G, S );
      AssignLabel( G, S[2], S[3], 2 );
    when "G":
      addPath( ~G, S );
      AssignLabel( G, S[2], S[1], 3 );
    end case;
    if #t[1] gt 1 and t[1][2] eq "~" then
      S := t[2];
      n := #S;
      case t[1][1]:
      when "A":
        AddEdge( ~G, S[1], S[n] );
        AddEdge( ~G, S[n], S[1] );
        if n eq 2 then
          AssignLabel( G, S[1], S[2], 2 );
          AssignLabel( G, S[2], S[1], 2 );
        else
          AddEdge( ~G, S[n-1], S[n] );
          AddEdge( ~G, S[n], S[n-1] );
        end if;
      when "B":
        AddEdge( ~G, S[2], S[n] );
        AddEdge( ~G, S[n], S[2] );
      when "C":
        AddEdge( ~G, S[n], S[1], 2 );
        AddEdge( ~G, S[1], S[n] );
      when "D":
        AddEdge( ~G, S[2], S[n] );
        AddEdge( ~G, S[n], S[2] );
      when "E":
        if n eq 7 then
          AddEdge( ~G, S[2], S[n] );
          AddEdge( ~G, S[n], S[2] );
        elif n eq 8 then
          AddEdge( ~G, S[1], S[n] );
          AddEdge( ~G, S[n], S[1] );
        else
          AddEdge( ~G, S[n-1], S[n] );
          AddEdge( ~G, S[n], S[n-1] );
        end if;
      when "F":
        AddEdge( ~G, S[1], S[n] );
        AddEdge( ~G, S[n], S[1] );
      when "G":
        AddEdge( ~G, S[n-1], S[n] );
        AddEdge( ~G, S[n], S[n-1] );
      end case;
    end if;
  end procedure;

  if #type eq 0 then  return Digraph<0|>;  end if;
  G := EmptyDigraph( Max( &cat[ t[2] : t in type ] ) );
  for t in type do
    addSimple( ~G, t );
  end for;
  return G;
end function;



// -------------------------------------------------
//
// Converting types to matrices
//
typeToCoxeter := function( type )
  return CoxeterMatrix( typeToCoxeterGraph( type ) );
end function;

isCrystType := function( type )
  return forall{ t : t in type | t[1][1] in "ABCDEFG" };
end function;

typeToCartan := function( type : Symmetric:=false, BaseField:="NumberField" )
  if Symmetric then
    return CartanMatrix( typeToCoxeterGraph( type ): Symmetric, BaseField:=BaseField );
  else
    if isCrystType( type ) then
      return CartanMatrix( typeToDynkinDigraph( type ) ), stdRealInj(Integers());
    else
      return CartanMatrix( typeToCoxeterGraph( type ) : BaseField:=BaseField );
    end if;
  end if;
end function;



// -------------------------------------------------
//
// Identifying types of (di)graphs and matrices
//

typeNonRed := procedure(~type, nonred)
    if not IsEmpty(nonred) then
        for i in [1..#type] do
            case type[i][1]:
            when "B":
                pos := #type[i][2];
            when "A":
                if #type[i][2] gt 1 then
                  continue;
                end if;
                pos := 1;
            when "C":
                if #type[i][2] gt 2 then
                  continue;
                end if;
                pos := 1;
            else
                continue;
            end case;
            r := type[i][2][pos];
            if r in nonred then
                if type[i][1] eq "C" then
                    Reverse(~type[i][2]);
                end if;
                type[i][1] := "BC";
                Exclude(~nonred,r);
            end if;
        end for;
    end if;
    if not IsEmpty(nonred) then
        error "Invalid set of non-reduced roots";
    end if;
end procedure;

// For diagnostic purposes the function returns the pair <"X",comp>
// when it detects that the submatrix described by comp is not an
// irreducible Cartan matrix.
coxeterGraphToType := function( G : nonred:={} )
  type := [* *];
  Comps, comps := LabelledComponents( G );
  for i in [1..#Comps] do
    Comp := Comps[i];  comp := comps[i];  
    L := Seqset( EdgeLabels( Comp ) ) diff {3};
    isLabelled := func< s, i | IsLabelled( EdgeSet( Comp )!{s[i],s[i+1]} ) >;
    injseq := func< s | [ Index(comp[Index(v)]) : v in s ] >;

    // Check that the graph is a tree
    if not IsTree( Comp ) then           // type A~  
      s := GirthCycle( Comp  );
      n := #comp;
      if #s eq n and IsEmpty( L ) then
        t := <"A~",injseq(s)>;
      else
        t := <"X", injseq(s) >;
      end if;
    else
      s := DiameterPath( Comp );         // the spine of the component
      n := #comp;
      if #s lt n-2 then
        t := <"X",injseq(s)>;
      elif #s eq n then                  // types A, A~1, B, F, H, I, C~, F~, G~
        if IsEmpty( L ) then             // type A
          t := <"A",injseq(s)>;
        elif n eq 2 then
	  if L eq {4} then               // type B2/C2
	    t := <"B",injseq(s)>;
	  elif L eq {6} then
	    t := <"G",injseq(s)>;        // type G2
          elif L eq {0} then
            t := <"A~",injseq(s)>;       // type A~1
	  else
            t := <"I",injseq(s),Rep(L)>; // type I
	  end if;
        elif L eq {4} then               // types B, F, C~, F~
          if isLabelled(s,1) then
            Reverse(~s);                 // move double bond to right end
          end if;
          if not exists{i : i in [2..n-2] | isLabelled(s,i) } then
	    if isLabelled(s,1) then
	      l := s[1];  Remove( ~s, 1 );  Append( ~s, l );
	      t := <"C~",injseq(s)>;
	    else
              t := <"B",injseq(s)>;
	    end if;
          elif n eq 4 and not isLabelled(s,1) and not isLabelled(s,3) then
            t := <"F",injseq(s)>;        // type F
	  elif n eq 5 then               // type F~
	    if isLabelled(s,2) then 
	      Reverse( ~s );
	    end if;
	    if [ isLabelled(s,i) : i in [1..4] ] eq [false,false,true,false] then
	      l := s[1];  Remove( ~s, 1 );  Append( ~s, l );
	      t := <"F~",injseq(s)>;
	    else
	      t := <"X", injseq(s)>; 
	    end if;
          else
            t := <"X",injseq(s)>;
          end if;
        elif L eq {5}  then              // type H
          if isLabelled(s,n-1) then
            Reverse(~s);                 // move double bond to left end
          end if;
          if not exists{i : i in [2..n-1] | isLabelled(s,i) }
          and #s in {3,4} then
            t := <"H",injseq(s)>;
          else
            t := <"X",injseq(s)>;
          end if;
	elif L eq {6} then               // type G~
	  if not isLabelled(s,1) then
	    Reverse(~s);
	  end if;
	  if n eq 3 and isLabelled(s,1) and not isLabelled(s,2) then
	    t := <"G~",injseq(s)>;
	  else
	    t := <"X",injseq(s)>;
	  end if;
        else
          t := <"X",injseq(s)>;
        end if;
      elif #s eq n-1 then                // types D, E, B~, E~7, E~8
        if IsEmpty( L ) then             // types D, E, E~7, E~8
          tail := Rep( { v : v in VertexSet(Comp) | v notin s } );
          nb := Neighbours( tail );
	  if #nb eq 1 then
	    fork := Position( s, Rep(nb) );
            if fork notin {n-2,3} then
              Reverse( ~s );                 // move fork to correct end
              fork := Position( s, Rep(nb) );
            end if;
	    if fork eq 4 and n eq 8 then            // type E~7
	      l := s[1];  Remove( ~s, 1 );  Insert( ~s, 2, tail );
	      t := <"E~",injseq(Append(s,l))>;        
            elif fork eq n-2 then          // type D
              t := <"D",injseq(Append(s,tail))>;
            elif fork eq 3 and (n in {6,7,8}) then // type E
              t := <"E",injseq(Insert(s,2,tail))>;
	    elif fork eq 3 and n eq 9 then // type E~8
	      t := <"E~",injseq(Insert(s,2,tail))>;
            else
              t := <"X",injseq(Append(s,tail))>;
            end if;
	  else
	    t := <"X",injseq(s)>;
	  end if;
	else                             // type B~
	  if not isLabelled(s,n-2) then
	    Reverse( ~s );
	  end if;
	  if L subset {4} and forall{ i : i in [1..n-3] | not isLabelled(s,i) } and isLabelled(s,n-2) then
	    tail := Rep( { v : v in VertexSet(Comp) | v notin s } );  
	    nb := Neighbours( tail );
	    if #nb eq 1 and Position( s, Rep(nb) ) eq 2 and not IsLabelled(EdgeSet( Comp )!{tail, Rep(nb)} ) then
  	      t := <"B~",injseq(Append(s,tail))>;
	    else
	      t := <"X",injseq(s)>;
	    end if;
          elif n eq 4 and L eq {4} and forall{ i : i in [1..n-2] | not isLabelled(s,i) } then
	    tail := Rep( { v : v in VertexSet(Comp) | v notin s } );  
	    nb := Neighbours( tail );
	    if #nb eq 1 and Position( s, Rep(nb) ) eq 2 then
              t := <"B~",injseq(Insert(s,3,tail))>;
	    else
	      t := <"X",injseq(s)>;
	    end if;
          else
            t := <"X",injseq(s)>;
	  end if; 
	end if;
      elif #s eq n-2 then                // types D~, E6~
        if not IsEmpty( L ) or n lt 5 then
	  t := <"X",injseq(s)>;
	else
          tail := [ v : v in VertexSet(Comp) | v notin s ];
          fork := [ Neighbours( v ) : v in tail ];
	  if &join(fork) subset { v : v in s } then  // type D~
	    if Position( s, Rep(fork[1]) ) notin {2} then
	      Reverse( ~s );
            end if;
	    if fork[1] eq {s[2]} and fork[2] eq {s[#s-1]} then
	      t := <"D~",injseq(s cat Reverse(tail))>;
	    else 
	      t := <"X",injseq(s)>;
	    end if;
	  else                           // type E6~
	    if n ne 7 then
	      t := <"X",injseq(s)>;
	    else
  	      if #fork[1] ne 2 then
	        Reverse( ~tail );  Reverse( ~fork );
	      end if;
	      if fork[2] eq {tail[1]} and fork[1] eq {s[3],tail[2]} then
	        Insert( ~s, 2, tail[1] );
	        t := <"E~",injseq(Append(s,tail[2]))>;
	      else
	        t := <"X",injseq(s)>;
	      end if;
	    end if; 
	  end if;
	end if;
      end if;
    end if;
    Append(~type,t);
  end for;
  typeNonRed(~type, nonred);
  return type;
end function;

dynkinDigraphToType := function( D : nonred:={} )
  if Category(D) eq SetEnum then  return [* *];  end if;
  type := coxeterGraphToType( CoxeterGraph( D ) ); // WITHOUT nonred !!! handle later !!!
  newtype := [* *];
  for t in type do
    case t[1]:
    when "H":
      newt := <"X",t[2]>;
    when "I":
      i := t[2][1];  j := t[2][2];
      if t[3] eq 6 then
        newt := IsLabelledEdge(D,j,i) select <"G",t[2]> else <"G",Reverse(t[2])>;
      elif t[3] eq 4 then
        newt := IsLabelledEdge(D,i,j) select <"B",t[2]> else <"B",Reverse(t[2])>;
      else
        newt := <"X",t[2]>;
      end if;
    when "B":
      n := #t[2];  i := t[2][n-1];  j := t[2][n];
      newt := IsLabelledEdge(D,i,j) select <"B",t[2]> else <"C",t[2]>;
    when "BC":
      n := #t[2];  i := t[2][n-1];  j := t[2][n];
      assert IsLabelledEdge(D,i,j);
      newt := t;
    when "F" :
      i := t[2][2];  j := t[2][3];
      newt := IsLabelledEdge(D,i,j) select <"F",t[2]> else <"F",Reverse(t[2])>;
    when "G":
      i := t[2][1];  j := t[2][2];
      newt := IsLabelledEdge(D,j,i) select <"G",t[2]> else <"G",Reverse(t[2])>;
    when "B~":
      l := t[2];  i := l[#l-2];  j := l[#l-1];
      newt := IsLabelledEdge(D,i,j) select <"B~",l> else <"X",l>;
    when "C~":
      l := t[2];  n := #l;  i1 := l[n-1];  j1 := l[n-2];  i2 :=l[n];  j2 := l[1];
      newt := (IsLabelledEdge(D,i1,j1) and IsLabelledEdge(D,i2,j2))
              select <"C~",l> else <"X",l>;
    when "G~":
      i := t[2][1];  j := t[2][2];
      newt := IsLabelledEdge(D,j,i) select <"G~",t[2]> else <"X",t[2]>;
    else
      newt := t;
    end case;
    Append( ~newtype, newt );
  end for;
  typeNonRed(~newtype, nonred);
  return newtype;
end function;

coxeterToType := function( M : nonred:={} )
  return coxeterGraphToType( CoxeterGraph( M ) : nonred:=nonred );
end function;

cartanToType := function( C : RealInjection:=false, nonred:={} )
  if IsCrystallographic( C ) then
    return dynkinDigraphToType( DynkinDigraph( C ) : nonred:=nonred );
  else
    return coxeterGraphToType( CoxeterGraph( C : RealInjection:=RealInjection) : nonred:=nonred  );
  end if;
end function;

forward numPosRootsOfType;

intrinsic NumPosRoots( C::AlgMatElt : Nonreduced:={} ) -> RngIntElt
{The number of positive roots of the root system with Cartan matrix C}
  return numPosRootsOfType( cartanToType( C : nonred:=Nonreduced ) );
end intrinsic;
intrinsic NumberOfPositiveRoots( C::AlgMatElt : Nonreduced:={} ) -> RngIntElt
{The number of positive roots of the root system with Cartan matrix C}
  return numPosRootsOfType( cartanToType( C : nonred:=Nonreduced ) );
end intrinsic;



isFiniteType := function( type )
  if forall(i){ i : i in [1..#type] | #type[i][1] eq 1 and type[i][1] ne "X" 
                                    or type[i][1] eq "BC" } 
  then return true,_;
  else return false,type[i];
  end if;
end function;

isFinAffType := function( type )
  return forall{ i : i in [1..#type] | type[i][1] ne "X" };
end function;

isAffineType := function( type )
  return forall{ i : i in [1..#type] |  type[i][1] ne "X" }
     and exists{ i : i in [1..#type] | #type[i][1] ne 1 };
end function;


// -------------------------------------------------
//
// Converting between types and names
//
typeToName := function( type )
  name := "";
  for t in type do
    name cat:= t[1] cat IntegerToString(#t[2]-((#t[1] eq 2 and t[1][2] eq "~") select 1 else 0));
    name cat:= (#t eq 2) select " " else ("(" cat IntegerToString(t[3]) cat ") ");
  end for;

  //Strip spaces at the end
  while (#name ne 0) and (name[#name] eq " ") do
	name := name[[1..#name-1]];
  end while;

  return name;
end function;

parseTypeString := function( str : allowtorus:=false)

  err := procedure( msg, str, ndx )
    error msg cat ":",str,"\n"," "^(#"Runtime error: "+#msg+ndx-2),"^";
  end procedure;

  // The index into str returned by the following functions
  // points to the next unprocessed character.

  skipSep := function( str, ndx )
    while ndx le #str and str[ndx] in " _\t" do ndx +:= 1; end while;
    return ndx;
  end function;

  getType := function( str, ndx )
    char := str[ndx];
    lcase := "abcdefghi";
    ucase := "ABCDEFGHI";
    if allowtorus then lcase cat:= "t"; ucase cat:= "T"; end if;
    if char   in  lcase then char := ucase[Position(lcase,char)]; end if;
    if char notin ucase then err( "Unexpected type", str, ndx+1 ); end if;
    // allow type BC but no other compound type
    if char eq "B" and #str gt ndx then
        if str[ndx+1] in "Cc" then char := "BC"; end if;
//        char2 := str[ndx+1];
//        if   char2 in lcase then char *:= ucase[Position(lcase,char2)];
//        elif char2 in ucase then char *:= char2; 
//        end if;
    end if;
    return char, ndx+#char;
  end function;

  getNumber := function( str, ndx )
    ndx := skipSep( str, ndx );
    num := 0;
    digits := "0123456789";
    if ndx gt #str or str[ndx] notin digits then
      err("Expecting a positive integer",str,ndx+1);
    end if;
    while ndx le #str and str[ndx] in digits do
      num := 10*num + StringToInteger(str[ndx]);
      ndx +:= 1;
    end while;
    return num, ndx;
  end function;

  checkRank := procedure( type, rank, ndx )
    case type:
    when "C~":
      if rank lt 2 then
        err("The rank must be at least 2 for type C~",str,ndx);
      end if;
    when "B~":
      if rank lt 3 then
        err("The rank must be at least 3 for type B~",str,ndx);
      end if;
    when "D~":
      if rank lt 4 then
        err("The rank must be at least 4 for type D~",str,ndx);
      end if;
    end case;
    case type[1]:
    when "A","B","C":
      if rank lt 1 then
        err("The rank must be at least 1",str,ndx);
      end if;
    when "D":
      if rank lt 1 then
        err("The rank must be at least 1",str,ndx);
      end if;
    when "E":
      if rank lt 6 or rank gt 8 then
        err("The rank must be 6, 7 or 8 for type E",str,ndx);
      end if;
    when "F":
      if rank ne 4 then
        err("For type F, the rank must 4",str,ndx);
      end if;
    when "G":
      if rank ne 2 then
        err("For type G, the rank must be 2",str,ndx);
      end if;
    when "H":
      if rank lt 3 or rank gt 4 then
        err("For type H, the rank must be 3 or 4",str,ndx);
      end if;
    when "I":
      if rank ne 2 then err("For type I, the rank must be 2",str,ndx); end if;
    when "T":
      if rank le 0 then err("For type T, the rank must be positive", str, ndx); end if;
    else
      err("internal error",str,ndx);
    end case;
  end procedure;

  getOrder := function( str, ndx )
    ndx := skipSep( str, ndx );
    if ndx gt #str or str[ndx] ne "(" then
      err("Expecting (",str,ndx+1);
    end if;
    order, ndx := getNumber( str, ndx+1 );
    ndx := skipSep( str, ndx );
    // As a small concession we assume a right bracket.
    // For strict parsing, replace the next code line by :-
    // if ndx gt #str or str[ndx] ne ")" then err("Expecting )",s,ndx); end if;
    // ndx +:= 1;
    if ndx le #str and str[ndx] eq ")" then ndx +:= 1; end if;
    return order, ndx;
  end function;

  getTilde := function( str, ndx );
    ndx := skipSep( str, ndx );
    affine := ndx le #str and str[ndx] eq "~";
    tilde := affine select "~" else "";
    if affine then ndx +:= 1; end if;
    return tilde, ndx;
  end function;

  // The list consists of tuples of the form < type, rank >
  // or, in the case of type I, < "I", order, 2 >,
  lst := [* *];
  ndx := 1;
  ndx := skipSep( str, ndx );
  while ndx le #str do
     t, ndx := getType( str, ndx );
     tilde, ndx := getTilde( str, ndx );
     if tilde eq "~" and (t in "HI" or t eq "BC") then
       err("Affine root system not available for type " cat t,str,ndx);
     end if;
     r, ndx := getNumber( str, ndx );
     rnkposn := ndx;
     if t eq "I" then
       m, ndx := getOrder( str, ndx );
       if m le 2 then
         err("The order must be at least 3",str,ndx-1);
       end if;
     end if;
     if tilde eq "" then
       tilde, ndx := getTilde( str, ndx );
       if tilde eq "~" and t in "HI" then
         err("Affine root system not available for type " cat t,str,ndx);
       end if;
     end if;
     t cat:= tilde;
     checkRank( t, r, rnkposn );
     if t eq "I" then Append( ~lst, < t, r, m > );
                 else Append( ~lst, < t, r > );
     end if;
     ndx := skipSep( str, ndx );
  end while;
  
  return lst;
end function;

nameToType := function( str : allowtorus:=false )
  lst := [* *]; n := 0;
  for t in parseTypeString( str : allowtorus:=allowtorus ) do
    if( t[1] eq "T" ) then 
      Append( ~lst,  <t[1], [ ], t[2] > );
    else
      m := n + t[2] + (#t[1] gt 1 and t[1][2] eq "~" select 1 else 0);
      Append( ~lst,
        #t eq 2 select <t[1], [n+1..m]> 
                else   <t[1], [n+1..m], t[3]>) ;
      n := m;
    end if;
  end for;
  return lst;
end function;

tnToType := function( t, n )
  error if t[1] notin "ABCDEFGHIabcdefghi"                           , "Invalid type", t;
  error if #t gt 2                                                   , "Invalid type", t;
  error if #t eq 2 and t ne "BC" and (t[2] ne "~" or t[1] in "HIhi") , "Invalid type", t;
  t := "ABCDEFGHIABCDEFGHI"[Position("ABCDEFGHIabcdefghi",t[1])] cat 
    ((#t eq 2) select "CC~"[Position("Cc~",t[2])] else "");
  if n le 0 then error "The rank must be at least 1"; end if;
  case t:
  when "E","E~":
    if (n lt 6 or n gt 8) then error "The rank must be 6, 7 or 8 for type",t; end if;
  when "F","F~":
    if (n ne 4) then error "The rank must be 4 for type",t; end if;
  when "G","G~":
    if (n ne 2) then error "The rank must be 2 for type",t; end if;
  when "C~":
    if (n lt 2) then error "The rank must be at least 2 for type",t; end if;
  when "B~":
    if (n lt 3) then error "The rank must be at least 3 for type",t; end if;
  when "D~":
    if (n lt 4) then error "The rank must be at least 4 for type",t; end if;
  when "I":
    if (n lt 3) then error "The order must be at least 3 for type",t; end if;
  end case;
  return (t eq "I") select [* <t,[1..2],n> *] else [* <t,[1..n+(#t eq 2 and t[2] eq "~" select 1 else 0)]> *];
end function;

// -------------------------------------------------
//
// Names of matrices and (di)graphs
//
intrinsic CartanName( M::AlgMatElt : RealInjection:=false, Nonreduced:={} ) -> MonStgElt
{The Cartan name of the Coxeter (Cartan) matrix M}
  if IsCoxeterMatrix(M) then
    type := coxeterToType( M : nonred:=Nonreduced );  str := "Coxeter";
  elif IsCartanMatrix(M) then
    type := cartanToType( M : RealInjection:=RealInjection, nonred:=Nonreduced );   str := "Cartan";
  else
    error "the given matrix is not a Coxeter or Cartan matrix";
  end if;
  error if exists(t){ t : t in type | t[1] eq "X" },
    "the component at rows and columns", t[2],
    "is not a finite or affine", str, "matrix";
  return typeToName( type );
end intrinsic;

intrinsic CartanName( G::GrphUnd : Nonreduced:={} ) -> MonStgElt
{The Cartan name of the Coxeter graph G}
  type := coxeterGraphToType( G : nonred:=Nonreduced );
  error if exists(t){ t : t in type | t[1] eq "X" },
  "the Coxeter group of the Coxeter graph is not finite or affine at component", t[2];
  return typeToName( type );
end intrinsic;

intrinsic CartanName( D::GrphDir : Nonreduced:={} ) -> MonStgElt
{The Cartan name of the Dynkin digraph D}
  type := dynkinDigraphToType( D : nonred:=Nonreduced );
  error if exists(t){ t : t in type | t[1] eq "X" },
  "the Coxeter group of the Dynkin digraph is not finite or affine at component", t[2];
  return typeToName( type );
end intrinsic;



// -------------------------------------------------
//
// Matrices and (di)graphs given by names
//
intrinsic CoxeterMatrix( N::MonStgElt ) -> AlgMatElt
{The Coxeter matrix with Cartan name N}
  return typeToCoxeter( nameToType( N ) );
end intrinsic;

intrinsic CartanMatrix( N::MonStgElt : Symmetric:=false,
BaseField:="NumberField" ) -> AlgMatElt
{The Cartan matrix with Cartan name N}
  return typeToCartan( nameToType( N ) : 
  Symmetric:=Symmetric, BaseField:=BaseField );
end intrinsic;

intrinsic CoxeterGraph( N::MonStgElt ) -> GrphUnd
{The Dynkin graph with Cartan name N}
  return typeToCoxeterGraph( nameToType( N ) );
end intrinsic;

intrinsic DynkinDigraph( N::MonStgElt ) -> GrphDir
{The Dynkin digraph with Cartan name N}
  type := nameToType( N );
  require isCrystType( type ) : "The Cartan type must be crystallographic";
  return typeToDynkinDigraph( type );
end intrinsic;

intrinsic IrreducibleCoxeterMatrix( X::MonStgElt, n::RngIntElt ) -> AlgMatElt
{The irreducible Coxeter matrix with Cartan name X_n (or X_2(n) for X=I)}
  return typeToCoxeter( tnToType( X, n ) );
end intrinsic;

intrinsic IrreducibleCartanMatrix( X::MonStgElt, n::RngIntElt : 
Symmetric:=false, BaseField:="NumberField" ) -> AlgMatElt
{The irreducible Cartan matrix with Cartan name X_n (or X_2(n) for X=I)}
  return typeToCartan( tnToType( X, n ) : 
  Symmetric:=Symmetric, BaseField:=BaseField );
end intrinsic;

intrinsic IrreducibleCoxeterGraph( X::MonStgElt, n::RngIntElt ) -> GrphUnd
{The irreducible Dynkin graph with Cartan name X_n (or X_2(n) for X=I)}
  return typeToCoxeterGraph( tnToType( X, n ) );
end intrinsic;

intrinsic IrreducibleDynkinDigraph( X::MonStgElt, n::RngIntElt ) -> GrphDir
{The irreducible Dynkin digraph with Cartan name X_n (or X_2(n) for X=I)}
  type := tnToType( X, n );
  require isCrystType( type ) : "The Cartan type must be crystallographic";
  return typeToDynkinDigraph( type );
end intrinsic;





// -------------------------------------------------
//
// Printing the Dynkin/Coxeter diagram
//
typeToDiagram := procedure( type : coxeter:=false )
  //type;
  isCryst := not coxeter;
  simpleToDiagram := procedure( type )
    t := type[1];
    lst := type[2];  n := #lst - (#t eq 2 and t[2] eq "~" select 1 else 0);
    printf "\n%o%o    ", t, n;
    case t:
    when "A":
      printf "%o", lst[1];
      for i := 2 to n do printf " - %o", lst[i]; end for;
      print "";
    when "B","BC":
      if n eq 1 then
        printf "%o", lst[1];
      else
        for i := 1 to n-2 do printf "%o - ", lst[i]; end for;
        if isCryst then
          printf "%o =>= %o\n", lst[n-1], lst[n];
        else
          printf "%o === %o\n", lst[n-1], lst[n];
        end if;
        if t eq "BC" then
          // print " "^(5+4*n) * "*";
        end if;
      end if;
    when "C":
      if n eq 1 then
        printf "%o", lst[1];
      else
        for i := 1 to n-2 do printf "%o - ", lst[i]; end for;
        if isCryst then
          printf "%o =<= %o\n", lst[n-1], lst[n];
        else
          printf "%o === %o\n", lst[n-1], lst[n];
        end if;
      end if;
    when "D":
      if n eq 1 then
        printf "%o", lst[1];
      elif n eq 2 then
        printf "%o   %o", lst[1], lst[2];
      elif n eq 3 then
        printf "%o --- %o --- %o", lst[2], lst[1], lst[3];
      else
        lst := [ IntegerToString(l) : l in lst ];
        k := &+[ #lst[i] : i in [1..n-2] ];
        printf " "^(k+3*(n-3)-4-#IntegerToString(n));  print lst[n-1];
        printf " "^(k+3*(n-3));  print "/";
        for i := 1 to n-3 do printf "%o - ", lst[i]; end for;
        print lst[n-2];
        printf " "^(k+3*(n-3));  print "\\";
        printf " "^(k+3*(n-3)+1);  print lst[n];
      end if;
    when "E", "E~":
      k := #IntegerToString(lst[1])+#IntegerToString(lst[3])+12;
      if t eq "E~" then k +:= 1; end if;
      if t eq "E~" and n eq 7 then 
        k +:= #IntegerToString(lst[8])+3;
	printf "%o - ", lst[8]; 
      end if;
      m := (t eq "E~" and n ne 8) select #lst-1 else #lst;
      printf "%o", lst[1];
      for i := 3 to m do printf " - %o", lst[i]; end for;
      printf "\n%o%o\n%o%o\n"," "^k,"|"," "^k,lst[2];
      if t eq "E~" and n eq 6 then 
        printf "%o%o\n%o%o\n"," "^k,"|"," "^k,lst[7];
      end if;
    when "F":
      printf "%o - %o %o %o - %o\n", lst[1],lst[2],(isCryst select "=>=" else "==="),lst[3],lst[4];
    when "G":
      if isCryst then
        printf "%o =<= %o\n", lst[1],lst[2];
        printf "%o%o\n", " "^(#IntegerToString(lst[1])+8),3;
      else
        printf "%o --- %o", lst[1],lst[2];
        printf "\n%o%o\n", " "^(#IntegerToString(lst[1])+8),6;
      end if;
    when "H":
      printf "%o --- %o - %o", lst[1],lst[2],lst[3];
      if n eq 4 then printf " - %o", lst[4]; end if;
      printf "\n%o5\n", " "^(#IntegerToString(lst[1])+8);
    when "I":
      printf "%o --- %o", lst[1],lst[2];
      printf "\n%o%o\n", " "^(#IntegerToString(lst[1])+8),type[3];
    when "A~":
      s := [ #IntegerToString( i ) : i in lst ];
      printf "%o", lst[1];
      if n eq 1 then
        printf " ------- %o\n", lst[2];
        printf "%o infty\n", " "^(#IntegerToString(n) + 7 + s[1]);
      else
        for i := 2 to n do printf " - %o", lst[i]; end for;
        printf "\n";
        k := #IntegerToString(n) + 5 + s[1];
        l := 3*(n-1) + &+[ Integers() | s[i] : i in [2..#s-2] ];
        printf "%o|%o|\n", " "^k, " "^l;
        l := l-2-s[#s];
        m1 := (l div 2) + 1;  m2 := (l div 2) + (l mod 2) + 1;
        printf "%o%o %o %o\n", " "^k, "-"^m1, lst[n+1], "-"^m2;
      end if;
    when "B~":
      s := [ #IntegerToString( i ) : i in lst ];
      w := Maximum( [s[1],s[2],s[n+1]] );
      k := #IntegerToString(n)+5;
      printf "%o%o\n", " "^(w-s[1]), lst[1];
      printf "%o %o\n", " "^(k+w), "\\";
      printf "%o   %o", " "^(k+w-s[2]), lst[2];
      for i := 3 to n-1 do printf " - %o", lst[i]; end for;
      printf " %o %o\n", (isCryst select "=>=" else "==="), lst[n];
      printf "%o /\n", " "^(k+w);
      printf "%o %o\n", " "^(k+w-s[n+1]), lst[n+1];
    when "C~":
      printf "%o %o %o", lst[n+1], (isCryst select "=>=" else "==="), lst[1];
      for i := 2 to n-1 do printf " - %o", lst[i]; end for;
      printf " %o %o\n", (isCryst select "=<=" else "==="), lst[n];
    when "D~":
      s := [ #IntegerToString( i ) : i in lst ];
      w := Maximum( [s[1],s[2],s[n+1]] );
      k := #IntegerToString(n)+5;
      l := 3*(n-3) + &+s[[3..n-3]]; if n eq 4 then l -:= 1;  end if;
      printf "%o%o %o%o\n", " "^(w-s[1]), lst[1], " "^l, lst[n-1];
      printf "%o %o%o/\n", " "^(k+w), "\\", " "^(l-1);
      printf "%o   %o", " "^(k+w-s[2]), lst[2];
      for i := 3 to n-2 do printf " - %o", lst[i]; end for;
      printf "\n%o /%o%o\n", " "^(k+w), " "^(l-1), "\\";
      printf "%o %o %o%o\n", " "^(k+w-s[n+1]), lst[n+1], " "^l, lst[n];
    when "F~":
      printf "%o - %o - %o %o %o - %o\n", 
      lst[5],lst[1],lst[2],(isCryst select "=>=" else "==="),lst[3],lst[4];
    when "G~":
      printf "%o %o %o - %o\n", lst[1],(isCryst select "=>=" else "==="),lst[2],lst[3];
      printf "%o%o\n", " "^(#IntegerToString(lst[1])+9),(isCryst select 3 else 6);
    end case;
  end procedure;
  for t in type do
    simpleToDiagram( t );
  end for;
end procedure;

intrinsic DynkinDiagram( N::MonStgElt )
{The Dynkin diagram with Cartan name N}
  type := nameToType( N );
  require isCrystType( type ) : "Cartan name must be crystallographic";
  typeToDiagram( type );
end intrinsic;

intrinsic CoxeterDiagram( N::MonStgElt )
{The Coxeter diagram with Cartan name N}
  type := nameToType( N );
  typeToDiagram( type : coxeter );
end intrinsic;

intrinsic DynkinDiagram( M::AlgMatElt )
{Print the Dynkin diagram of the Coxeter (Cartan) matrix M}
  if IsCoxeterMatrix(M) then
    type := coxeterToType( M );
    require isFinAffType( type ) :
    "The Coxeter group corresponding to the Coxeter matrix is not finite or affine";
    require isCrystType( type ) : "Cartan type must be crystallographic";
    typeToDiagram( type );
  else
    type := cartanToType( M );
    require isFinAffType( type ) :
    "The Coxeter group corresponding to the Cartan matrix is not finite or affine";
    require isCrystType( type ) : "Cartan type must be crystallographic";
    typeToDiagram( type );
  end if;
end intrinsic;

intrinsic CoxeterDiagram( M::AlgMatElt : RealInjection:=false )
{Print the Coxeter diagram of the Coxeter (Cartan) matrix M}
  if IsCoxeterMatrix(M) then
    type := coxeterToType( M );
    require isFinAffType( type ) :
    "The Coxeter group corresponding to the Coxeter matrix is not finite or affine";
    typeToDiagram( type : coxeter );
  else
    type := cartanToType( M : RealInjection:=RealInjection );
    require isFinAffType( type ) :
    "The Coxeter group corresponding to the Cartan matrix is not finite or affine";
    typeToDiagram( type : coxeter );
  end if;
end intrinsic;

intrinsic DynkinDiagram( G::GrphUnd )
{Print the Dynkin diagram of the Coxeter graph G}
  type := coxeterGraphToType( G );
  require isFinAffType( type ) :
  "The Coxeter group corresponding to the Coxeter graph is not finite or affine";
  require isCrystType( type ) : "Cartan type must be crystallographic";
  typeToDiagram( type );
end intrinsic;

intrinsic CoxeterDiagram( G::GrphUnd )
{Print the Coxeter diagram of the Coxeter graph G}
  type := coxeterGraphToType( G );
  require isFinAffType( type ) :
  "The Coxeter group corresponding to the Coxeter graph is not finite or affine";
  typeToDiagram( type : coxeter );
end intrinsic;

intrinsic DynkinDiagram( D::GrphDir )
{Print the Dynkin diagram of the Dynkin digraph D}
  type := dynkinDigraphToType( D );
  require isFinAffType( type ) :
  "The Coxeter group corresponding to the Dynkin digraph is not finite or affine";
  typeToDiagram( type );
end intrinsic;

intrinsic CoxeterDiagram( D::GrphDir )
{Print the Coxeter diagram of the Dynkin digraph D}
  type := dynkinDigraphToType( D );
  require isFinAffType( type ) :
  "The Coxeter group corresponding to the Dynkin digraph is not finite or affine";
  typeToDiagram( type : coxeter );
end intrinsic;





// ====================================================
//
// Operations and properties of matrices and (di)graphs
//
// ====================================================

intrinsic FundamentalGroup( C::AlgMatElt ) -> GrpAb
{The fundamental group of the crystallographic Cartan matrix C}
//  require IsCartanMatrix(C) : "matrix is not a Cartan matrix";
  require IsCrystallographic(C) : "matrix is not crystallographic";
  if Nrows(C) ne 0 then
    return StandardLattice( Ncols(C) ) / Lattice( C );
  else
    return AbelianGroup([]);
  end if;
end intrinsic;

intrinsic FundamentalGroup( D::GrphDir ) -> GrpAb
{The fundamental group of the Dynkin digraph D}
  return FundamentalGroup( CartanMatrix( D ) );
end intrinsic;

intrinsic FundamentalGroup( N::MonStgElt ) -> GrpAb
{The fundamental group of the Cartan name N}
  C := CartanMatrix( N );
  require IsCrystallographic( C ) :
    "Fundamental groups are only defined for crystallographic Cartan names";
  G := FundamentalGroup( C );  // lose mapping
  return G;
end intrinsic;

intrinsic IsCoxeterIrreducible( C::AlgMatElt ) -> BoolElt, SetEnum
{True iff the Coxeter (Cartan) matrix C is irreducible}
  G := CoxeterGraph( C );
  if IsConnected( G ) then
    return true, _;
  else
    return false, { Index(x) : x in Components( G )[1] };
  end if;
end intrinsic;

intrinsic IsCrystallographic( C::AlgMatElt ) -> BoolElt
{True iff the Cartan matrix C is crystallographic}
  require IsCartanMatrix(C) : "matrix is not a Cartan matrix";
  flag, _ := CanChangeUniverse(Eltseq(C),Integers());
  return flag;
//  return Category(BaseRing(C)) in [RngInt,FldRat] or
//     forall{ <i,j> : i in [1..Nrows(C)], j in [1..Ncols(C)] | C[i,j] in Integers() };
end intrinsic;


// ====================================================
//
// Operations on types
//
// ====================================================

// ----------------------------------------------------
//
// Testing isogeny
//
/*sortType := function( type )
// local perm;
  convertToInt := function( t )
    if #t eq 2 then  return < t[1], #t[2] >;
    else             return < t[1], #t[2], t[3] >;
    end if;
  end function;
  order := function(x,y)
    if x[1] ne y[1] then
      return StringToCode(x[1]) - StringToCode(y[1]);
    elif #x[2] ne #y[2] then
      return #x[2] - #y[2];
    else
      return 0;
    end if;
  end function;
  pairs := [ t : t in type | #t eq 2 ];
  Sort( ~pairs, order );
  triples := [ t : t in type | #t eq 3 ];
  Sort( ~triples, func<x,y|x[3]-y[3]> );
  rtOrder := &cat[ t[2] : t in pairs ] cat &cat[ t[2] : t in triples ];
  pairs :=   [ convertToInt( t ) : t in pairs ];
  triples := [ convertToInt( t ) : t in triples ];
  return pairs, triples, rtOrder;
end function;

isIsogenousTypes := function( type1, type2 : Cryst:=false  )
  p1, t1, r1 := sortType( standardiseType( type1 : Cryst:=Cryst ) );
  p2, t2, r2 := sortType( standardiseType( type2 : Cryst:=Cryst ) );
  if p1 eq p2 and t1 eq t2 then
    S := Sym( #r1 );
    return true, Eltseq( (S!r1)^-1 * S!r2 );
  else
    return false, _;
  end if;
end function;
*/


// ----------------------------------------------------
//
// Automorphisms of crystallographic finite types
//
standardiseType := function( type : Cryst:=false )
  i := 1;
  while i le #type do
    t := type[i];
    if (t[1] eq "B" or t[1] eq "C" or t[1] eq "D") and #t[2] eq 1 then
      type[i][1] := "A";
    elif t[1] eq "B" and #t[2] eq 2 and not Cryst then
      type[i] := < "I", 4, t[2] >;
    elif t[1] eq "C" and #t[2] eq 2 then
      if Cryst then
        type[i] := < "B", Reverse(t[2]) >;
      else
        type[i] := < "I", 4, t[2] >;
      end if;
    elif t[1] eq "D" and #t[2] eq 2 then
      for j in [#type..i+1 by -1] do  type[j+1] := type[j];  end for;
      type[i+1] := <"A",[t[2][2]]>;  type[i] := <"A",[t[2][1]]>;
      i +:= 1;
    elif t[1] eq "D" and #t[2] eq 3 then
      type[i][1] := "A";  type[i][2] := [t[2][2],t[2][1],t[2][3]];
    elif t[1] eq "G" and not Cryst then
      type[i] := < "I", 6, t[2] >;
    end if;
    i +:= 1;
  end while;
  return type;
end function;

typeAutos := function( type : p:=0 )
  type := standardiseType( type : Cryst );
  T := [];
  for t in type do  Append( ~T, t );  end for;
  n := &+[ #t[2] : t in T ];
  G := Sym(n);  gens := [ G | ];
  classes := { <t[1],#t[2]> : t in T };
  for c in classes do
    ts := [ t : t in T | t[1] eq c[1] and #t[2] eq c[2] ];
    t := ts[1];  l := t[2];
    case t[1]:
    when "A":
      if #l gt 1 then
        perm := [1..n];
        for i in [1..#l] do
          perm[l[i]] := l[#l-i+1];
        end for;
        Append( ~gens, perm );
      end if;
    when "B", "C":
      if p eq 2 and #l eq 2 then
        Append( ~gens, G!(l[1],l[2]) );
      end if;
    when "D":
      if #l gt 2 then
        Append( ~gens, G!(l[#l],l[#l-1]) );
      end if;
      if #l eq 4 then
        Append( ~gens, G!(l[1],l[3],l[4]) );
      end if;
    when "E":
      if #l eq 6 then
        Append( ~gens, G!(l[1],l[6])(l[3],l[5]) );
      end if;
    when "F":
      if p eq 2 then
        Append( ~gens, G!(l[1],l[4])(l[2],l[3]) );
      end if;
    when "G":
      if p eq 3 then
        Append( ~gens, G!(l[1],l[2]) );
      end if;
    end case;
    if #ts ge 2 then
      m := ts[2][2];  perm := [1..n];
      for i in [1..#l] do
        perm[l[i]] := m[i];  perm[m[i]] := l[i];
      end for;
      Append( ~gens, perm );
    end if;
    if #ts ge 3 then
      perm := [1..n];
      for j in [1..#ts] do
        l := ts[j][2];  
	m := (j lt #ts) select ts[j+1][2] else ts[1][2];
	for i in [1..#l] do
	  perm[l[i]] := m[i];
	end for;
      end for;
      Append( ~gens, perm );
    end if;
  end for;
  G := sub< G | gens >; 
  return G;
end function;      



// ----------------------------------------------------
//
// Number of positive roots
//
numPosRootsOfType := function( type )
  simpleNum := function( t )
    n := #t[2];
    case t[1]:
    when "A":
      return n*(n+1) div 2;
    when "B", "C":
      return n^2;
    when "BC":
      return n^2 + n; // have n short roots. their doubles are roots again
    when "D":
      return (n gt 1) select n*(n-1) else 1;
    when "E":
      case n:
      when 6: return 36;
      when 7: return 63;
      when 8: return 120;
      end case;
    when "F":
      return 24;
    when "G":
      return 6;
    when "H":
      case n:
      when 3: return 15;
      when 4: return 60;
      end case;
    when "I":
      return t[3];  //(t[3] mod 2 eq 0) select t[3] else 2*t[3];
    else
      return Infinity();
    end case;
  end function;
  num := 0;
  for t in type do  num +:= simpleNum(t);  end for;
  return num;
end function;

intrinsic NumPosRoots( N::MonStgElt ) -> RngIntElt
{The number of positive roots of the root system with Cartan name N}
  return numPosRootsOfType( nameToType( N ) );
end intrinsic;
intrinsic NumberOfPositiveRoots( N::MonStgElt ) -> RngIntElt
{The number of positive roots of the root system with Cartan name N}
  return numPosRootsOfType( nameToType( N ) );
end intrinsic;



// ----------------------------------------------------
//
// Dual
//
dualOfType := function( type )
  simpleDual := function( t )
    case t[1]:
    when "B":
      t[1] := "C";
    when "C":
      t[1] := "B";
    when "F", "G":
      Reverse( ~t[2] );
    end case;
    return t;
  end function;
  dual := [**];
  for t in type do
    Append( ~dual, simpleDual(t) );
  end for;
  return dual;
end function;



// ----------------------------------------------------
//
// Basic degrees (degrees of basic polynomial invariants)
//
// The second returned values are the "basic eigenvalues"
// used to compute orders of (twisted) finite goLts.
//
typeToBasicDegrees := function( typeseq : orbits:= false );
  if #typeseq eq 0 then
    return [Integers()|], [Integers()|];
  end if;
  deg := [];  evals := [];
  
  // the twist is broken into the internal part and the external part 
  // (for abs reducible types).
  flddeg := (orbits cmpeq false) select 1 else LCM( {#O:O in orbits} );
  F := (flddeg le 2) select Rationals() else CyclotomicField( flddeg );
  if flddeg eq 1 then
    intwists := [ 1 : Ctype in typeseq ];
    outtwists := [ <1,1> : Ctype in typeseq ];
  else
    comps := [ Seqset(Ctype[2]) : Ctype in typeseq ];
    intwists := [ Maximum( [#(O meet cmp) : O in orbits] ) : cmp in comps ];
    comporbits := { Setseq({i:i in [1..#comps]|not IsEmpty(O meet comps[i])}) : 
      O in orbits };
    outtwists := [ ];
    for i in [1..#typeseq] do
      _ := exists(corb){ corb : corb in comporbits | i in corb };
      outtwists[i] := < #corb, Position(corb,i)-1 >;
    end for;
  end if;
  
  alldeg := [Integers()|];  alleps := [F|];
  for idx in [1..#typeseq] do
    Ctype := typeseq[idx]; intwist := intwists[idx]; outtwist := outtwists[idx];
    if Category( Ctype[2] ) eq RngIntElt then
      n := Ctype[2];
    else
      n := #Ctype[2];
    end if;

    eps := [ RootOfUnity(outtwist[1],F)^outtwist[2] : i in [1..n] ];
    
    t := Ctype[1];
    case t:
    when "A":
      deg := [2..n+1];
      if intwist eq 2 then
        for i in [i : i in [1..n] | IsEven(i)] do
          eps[i] *:= -1;
        end for;
      end if;
    when "B","C","BC":
      deg := [2..2*n by 2];
      if intwist eq 2 then eps[2] *:= -1; end if;
    when "D":
      deg := (n ne 1) select [2..2*(n-1) by 2] cat [n] else [2];
      if intwist eq 2 then 
        eps[n] *:= -1;
      elif intwist eq 3 then
        omega := RootOfUnity(3,F);
        eps[2] *:= omega;  eps[4] *:= omega^2;
      end if;        
    when "E":
      if   n eq 6 then  deg := [2,5,6,8,9,12];
      elif n eq 7 then  deg := [2,6,8,10,12,14,18];
      else              deg := [2,8,12,14,18,20,24,30];
      end if;
      if intwist eq 2 then
        eps[2] *:= -1;  eps[5] *:= -1;
      end if;
    when "F":
      deg := [2,6,8,12];
      if intwist eq 2 then
        eps[2] *:= -1;  eps[4] *:= -1;
      end if;
    when "G":
      deg := [2,6];
      if intwist eq 2 then eps[2] *:= -1; end if;
    when "H":
      if n eq 3 then    deg := [2,6,10];
      else              deg := [2,12,20,30];
      end if;
    when "I":
      deg := [2,Ctype[3]];
    else
      error "illegal type " cat t;
    end case;

    alldeg cat:= deg;  alleps cat:= eps;
  end for;

  return alldeg, alleps;

end function;


// ----------------------------------------------------
//
// Coxeter group order
//
typeToOrder := function( type )
  for t in type do
    if t[1] eq "X" or #(t[1]) gt 1 and t[1][2] eq "~" then
      return Infinity();
    end if;
  end for;
  return &*typeToBasicDegrees( type );
end function;

intrinsic CoxeterGroupOrder( M::AlgMatElt : RealInjection:= false) -> RngIntElt
{The order of the Coxeter group with Coxeter (Cartan) matrix M}
  type := ( IsCoxeterMatrix(M) ) select coxeterToType(M) else 
    cartanToType(M: RealInjection:=RealInjection);
  return typeToOrder( type );
end intrinsic;

intrinsic CoxeterGroupOrder( G::GrphUnd )  -> RngIntElt
{The order of the Coxeter group with Coxeter graph G}
  return typeToOrder( coxeterGraphToType( G ) );
end intrinsic;

intrinsic CoxeterGroupOrder( D::GrphDir )  -> RngIntElt
{The order of the Coxeter group with Dynkin digraph D}
  return typeToOrder( dynkinDigraphToType( D ) );
end intrinsic;

intrinsic CoxeterGroupOrder( N::MonStgElt )  -> RngIntElt
{The order of the Coxeter group with Cartan name N}
  return typeToOrder( nameToType( N ) );
end intrinsic;


toMultiset := func< s |  {* x[1]^^x[2] : x in s *} >;
fromMultiset := func< s | [ <x,Multiplicity(s,x)> : x in MultisetToSet(s) ] >;

typeToFactoredOrder := function( type )
  for t in type do
    if t[1] eq "X" or #(t[1]) gt 1 then
      return Infinity();
    end if;
  end for;
  return fromMultiset( 
  &join{ toMultiset(Factorisation(d)) : d in typeToBasicDegrees( type ) } );
end function;

intrinsic CoxeterGroupFactoredOrder( M::AlgMatElt : RealInjection:= false ) -> RngIntElt
{The factored order of the Coxeter group with Coxeter (Cartan) matrix M}
  type := ( IsCoxeterMatrix(M) ) select coxeterToType(M) else 
    cartanToType(M: RealInjection:=RealInjection);
  return typeToFactoredOrder( type );
end intrinsic;

intrinsic CoxeterGroupFactoredOrder( G::GrphUnd )  -> RngIntElt
{The factored order of the Coxeter group with Coxeter graph G}
  return typeToFactoredOrder( coxeterGraphToType( G ) );
end intrinsic;

intrinsic CoxeterGroupFactoredOrder( D::GrphDir )  -> RngIntElt
{The factored order of the Coxeter group with Dynkin digraph D}
  return typeToFactoredOrder( dynkinDigraphToType( D ) );
end intrinsic;

intrinsic CoxeterGroupFactoredOrder( N::MonStgElt )  -> RngIntElt
{The factored order of the Coxeter group with Cartan name N}
  return typeToFactoredOrder( nameToType( N ) );
end intrinsic;


// ----------------------------------------------------
//
// Isomorphism and equivalence
//
/*isCartanEquivalent:= function( A, B, Crystallographic )
  if Crystallographic then
    return IsIsomorphicLabelPreserving( DynkinDigraph(A),
    DynkinDigraph(B) );
  else
    return IsIsomorphicLabelPreserving( CoxeterGraph(A),
    CoxeterGraph(B) );
  end if;
end function;*/

intrinsic IsCartanEquivalent( C1::AlgMatElt, C2::AlgMatElt ) -> BoolElt
{True iff the crystallographic Cartan matrices C1 and C2 are Cartan equivalent}
  require IsCrystallographic(C1) :
  "The first matrix is not a crystallographic Cartan matrix";
  require IsCrystallographic(C2) :
  "The second matrix is not a crystallographic Cartan matrix";
  return IsIsomorphicLabelPreserving( DynkinDigraph(C1), DynkinDigraph(C2) );
end intrinsic;

intrinsic IsCartanEquivalent( N1::MonStgElt, N2::MonStgElt ) -> BoolElt
{True iff the Cartan names N1 and N2 are Cartan equivalent}
  D1 := DynkinDigraph( N1 );  D2 := DynkinDigraph( N2 );
  ret := IsIsomorphicLabelPreserving( D1, D2 );  // discard 2nd return
  return ret;
end intrinsic;


intrinsic IsCoxeterIsomorphic( M1::AlgMatElt, M2::AlgMatElt ) -> BoolElt
{True if, and only if, M1 and M2 are Coxeter (Cartan) matrices of isomorphic
Coxeter groups}
  if IsCoxeterMatrix( M1 ) eq IsCoxeterMatrix( M2 ) then
    return IsIsomorphicLabelPreserving( CoxeterGraph( M1 ), CoxeterGraph( M2 ) );
  else
    error "the matrices must both be Coxeter matrices or both be Cartan matrices";
  end if;
end intrinsic;

intrinsic IsCoxeterIsomorphic( N1::MonStgElt, N2::MonStgElt ) -> BoolElt
{True if, and only if, N1 and N2 are Cartan names of isomorphic
Coxeter groups}
  ret := IsIsomorphicLabelPreserving( CoxeterGraph( N1 ), CoxeterGraph(   N2 ) );
  return ret;
end intrinsic;

// ----------------------------------------------------
//
// Predicates
//
isSimplyLacedType := function( type )
  return forall{ t : t in type | t[1] in "ADE" };
end function;

intrinsic IsSimplyLaced( M::AlgMatElt : RealInjection:=false ) -> BoolElt
{True iff the Coxeter (Cartan) matrix M is simply laced}
  n := Ncols( M );
  if not IsCoxeterMatrix( M ) then
    M := CoxeterMatrix( M : RealInjection:=RealInjection);  
    if Category( M ) ne AlgMatElt then
      error M;
    end if;  
  end if;
  return { M[i,j] : i in [j+1..n], j in [1..n] } subset {2,3};
end intrinsic;

intrinsic IsSimplyLaced( G::GrphUnd ) -> BoolElt
{True iff the Coxeter graph G is simply laced}
  require IsCoxeterGraph( G ) : "not a Coxeter graph";
  return Seqset( Labels( EdgeSet( G ) ) ) subset {3};
end intrinsic;

intrinsic IsSimplyLaced( D::GrphDir ) -> BoolElt
{True iff the Dynkin digraph D is simply laced}
  require IsDynkinDigraph( D ) : "not a Dynkin digraph";
  return Seqset( Labels( EdgeSet( D ) ) ) subset {1};
end intrinsic;

intrinsic IsSimplyLaced( N::MonStgElt ) -> BoolElt
{True iff the Cartan name N is simply laced}
  type := nameToType( N );
  require forall{ t : t in type | t[1] ne "X" } : "invalid Cartan name";
  return isSimplyLacedType( type );
end intrinsic;

// A test of positive definiteness, using the first conjugate
/*  Not used
isPositiveDefinite := function( A )
  c := Coefficients( MinimalPolynomial( A ) );
  if not forall{ a : a in c | IsReal(a) } then  return false;  end if;
  c := [ Real(ComplexField()!a) : a in c ];
  evals := Roots( PolynomialRing(RealField())!c );
  evals := [ a[1] : a in evals ];
  return forall{ a : a in evals | IsReal(a) and a gt 0 };
end function;
*/

intrinsic IsCoxeterFinite( M::AlgMatElt : RealInjection:=false ) -> BoolElt
{True iff the Coxeter group of Coxeter (Cartan) matrix M is finite}
  require IsCoxeterMatrix(M) or IsCartanMatrix(M) : "neither a Coxeter nor a Cartan matrix";
  type := ( IsCoxeterMatrix(M) ) select coxeterToType(M) else 
    cartanToType(M: RealInjection:=RealInjection);
  return isFiniteType( type );
end intrinsic;

intrinsic IsCoxeterFinite( G::GrphUnd ) -> BoolElt
{True iff the Coxeter group of the Coxeter graph G is finite}
  return IsCoxeterFinite( CoxeterMatrix( G ) );
end intrinsic;

intrinsic IsCoxeterFinite( D::GrphDir ) -> BoolElt
{True iff the Coxeter group of the Dynkin digraph D is finite}
  return IsCoxeterFinite( CartanMatrix( D ) );
end intrinsic;

intrinsic IsCoxeterFinite( N::MonStgElt ) -> BoolElt
{True iff N is the Coxeter group with Cartan name N is finite}
  type := nameToType( N );
  return Category( type ) ne BoolElt and isFiniteType( type );
end intrinsic;

intrinsic IsCoxeterAffine( M::AlgMatElt : RealInjection:=false ) -> BoolElt
{True iff the Coxeter group of the Coxeter (Cartan) matrix M is affine}
  type := ( IsCoxeterMatrix(M) ) select coxeterToType(M) else 
    cartanToType(M: RealInjection:=RealInjection);
  return isAffineType( type );
end intrinsic;

intrinsic IsCoxeterAffine( G::GrphUnd ) -> BoolElt
{True iff the Coxeter group of the Coxeter graph G is affine}
  type := coxeterGraphToType( G );
  return isAffineType( type );
end intrinsic;

intrinsic IsCoxeterAffine( D::GrphDir ) -> BoolElt
{True iff the Coxeter group of the Dynkin digraph D is affine}
  type := dynkinDigraphToType( D );
  return isAffineType( type );
end intrinsic;

intrinsic IsCoxeterAffine( N::MonStgElt ) -> BoolElt
{True iff N is the Cartan name of an affine Coxeter group}
  type := nameToType( N );
  return Category( type ) ne BoolElt and isAffineType( type );
end intrinsic;

/*extract := function( G, i )
  G -:= i;
  return StandardGraph( G ); // doesn't work
end function;

isFinAff := func< G | IsCoxeterFinite( G ) or IsCoxeterAffine( G ) >;

intrinsic IsCoxeterHyperbolic( G::GrphUnd ) -> BoolElt
{True iff the Coxeter group of the Coxeter graph G is hyperbolic}
  n := #VertexSet( G );
  return not isFinAff(G) and forall{ i : i in [1..n] | isFinAff( extract(G,i) ) };
end intrinsic;

intrinsic IsCoxeterCompactHyperbolic( G::GrphUnd ) -> BoolElt
{True iff the Coxeter group of the Coxeter graph G is compact hyperbolic}
  n := #VertexSet( G );
  return not isFinAff(G) and forall{ i : i in [1..n] | IsCoxeterFinite( extract(G,i) ) };
end intrinsic;
*/

extract := function( M, n, i )
  m := [];
  for j in [1..n] do
    for k in [1..n] do
      if j ne i and k ne i then
        Append( ~m, M[j,k] );
      end if;
    end for;
  end for;
  return Matrix( n-1, n-1, m );
end function;

isFinAff := func< M | IsCoxeterFinite( M ) or IsCoxeterAffine( M ) >;

intrinsic IsCoxeterHyperbolic( M::AlgMatElt ) -> BoolElt
{True iff the Coxeter group of the Coxeter matrix M is hyperbolic}
  require IsCoxeterMatrix( M ) : "Not a Coxeter matrix";
  n := Ncols( M );
  return not isFinAff(M) and forall{ i : i in [1..n] | isFinAff( extract(M,n,i) ) };
end intrinsic;
    
intrinsic IsCoxeterCompactHyperbolic( M::AlgMatElt ) -> BoolElt
{True iff the Coxeter group of the Coxeter matrix M is compact hyperbolic}
  require IsCoxeterMatrix( M ) : "Not a Coxeter matrix";
  n := Ncols( M );
  return not isFinAff(M) and forall{ i : i in [1..n] | 
  IsCoxeterFinite( extract(M,n,i) ) };
end intrinsic;
    
    
intrinsic IsCoxeterHyperbolic( G::GrphUnd ) -> BoolElt
{True iff the Coxeter group of the Coxeter graph G is hyperbolic}
  require IsCoxeterGraph( G ) : "Not a Coxeter matrix";
  return IsCoxeterHyperbolic( CoxeterMatrix( G ) );
end intrinsic;

intrinsic IsCoxeterCompactHyperbolic( G::GrphUnd ) -> BoolElt
{True iff the Coxeter group of the Coxeter graph G is compact hyperbolic}
  require IsCoxeterGraph( G ) : "Not a Coxeter graph";
  return IsCoxeterCompactHyperbolic( CoxeterMatrix( G ) );
end intrinsic;



// --------------------- eof --------------------------

