freeze;

////////////////////////////////////////////////////////////////////////
intrinsic IsCentral( L::AlgLie, x::AlgLieElt ) -> BoolElt
{True iff x is central in L}
  require IsCoercible( L, x ) : "Argument 2 does not lie in argument 1";  
  ok := forall{ b : b in Basis(L) | b*x eq 0 };
  return ok;
end intrinsic;

intrinsic IsCentral( L::AlgMatLie, x::AlgMatLieElt ) -> BoolElt
{True iff x is central in L}
  require IsCoercible( L, x ) : "Argument 2 does not lie in argument 1";  
  ok := forall{ b : b in Basis(L) | b*x eq 0 };
  return ok;
end intrinsic;

intrinsic IsCentral( L::AlgLie, M::AlgLie ) -> BoolElt
{True iff M is central in L}
  require M subset L :  "Argument 2 does not lie in argument 1";  
  ok := forall{ b : c in Basis(M), b in Basis(L) | b*c eq 0 };
  return ok;
end intrinsic;

intrinsic IsCentral( L::AlgMatLie, M::AlgMatLie ) -> BoolElt
{True iff M is central in L}
  require M subset L :  "Argument 2 does not lie in argument 1";  
  ok := forall{ b : c in Basis(M), b in Basis(L) | b*c eq 0 };
  return ok;
end intrinsic;


/////////////////////////////////////////////////////////////////////////
intrinsic Centre( L::AlgLie ) -> AlgLie
{The centre of the Lie algebra L}
  return Centralizer( L, L );
end intrinsic;


///////////////////////////////////////////////////////////////////////
intrinsic Centralizer( L::AlgLie, K::AlgLie ) -> AlgLie
{The centralizer of the subalgebra K in the Lie algebra L}   

  require IsCoercible( L, Zero(K) ) : "Argument 2 is not contained in argument 1";
  F := CoefficientRing( L );
  dL := Dimension( L );
  dK := Dimension( K );
  C := L;

  for i in [1..dK] do
    dC := Dimension(C);
//"i:", i, dC, dK;
    V := RMatrixSpace( F, dC, dL );

    eqs := [ ];
    for j in [1..dC] do
      eqs := Append( eqs, L!C.j*L!K.i );
    end for;
    eqs := V!eqs;

    sol := Kernel( eqs );
//"sol dim:", Dimension(sol);
    sol := [ L | C!Eltseq(sol.i) : i in [1..Dimension( sol ) ] ];
    C := sub< L | sol >;
  end for;
  return C;

end intrinsic;


intrinsic Centralizer( L::AlgLie, x::AlgLieElt ) -> AlgLie
{The centralizer of the element x in the Lie algebra L}
  require IsCoercible( L, x ) : "Argument 2 does not lie in argument 1";
  return Centralizer( L, sub< L | x > );
end intrinsic;



////////////////////////////////////////////////////////////////////////
intrinsic Normalizer(L::AlgLie, K::AlgLie) -> AlgLie, Map
{The normalizer of ideal K in the Lie algebra L}

// "Normalizer", Dimension(L), Dimension(K);

    require IsCoercible(L, Zero(K)) and K subset L:
	"Argument 2 is not contained in argument 1";

    if K eq L then
	return L, Coercion(L, L);
    end if;

// /*

    /*
    New fast algorithm by Allan, Aug 2012.
    */

    mor := Morphism(K, L);
    n := Dimension(L);
    N := 1;
// "Mat loop"; time
    for i := 1 to Nrows(mor) do
	mat := LeftMultiplicationMatrix(L!mor[i]);
	if N cmpne 1 then
	    mat := N * mat;
	end if;
	if IsZero(mat) then
	    continue;
	end if;
	r := Nrows(mat);
	mat := VerticalJoin(mat, mor);
//"mat:", mat;
	ker := KernelMatrix(mat);
	delete mat;
	ker := ColumnSubmatrix(ker, 1, r);
//"ker:", ker; // IsUnit(ker);
	if Nrows(ker) lt r then
	    if N cmpeq 1 then
		N := ker;
	    else
		N := ker * N;
	    end if;
	    if IsZero(N) then
		break;
	    end if;
	end if;
//printf "i: %o, r: %o, ker dim: %o, N dim: %o\n", i, r, Nrows(ker), N cmpeq 1 select n else Nrows(N);
	delete ker;
    end for;

    if N cmpeq 1 then
	return L, Coercion(L, L);
    end if;

    N := [L ! N[i]: i in [1 .. Nrows(N)]];
// "Final sub<>"; time
    return sub<L | N: Basis>;
//*/

/// OLD original algorithm:

    tt:= BasisProducts( L );
    n:= Dimension( L );
    m:= Dimension( K );
    F:= CoefficientRing( L );

    eqs:= [ ];
    Vn:= VectorSpace( F, n );

    for i in [1..m] do
      lv:= Vn!(L!K.i);
      for p in [1..n] do
  // FIX THIS!
	eqs cat:= [ InnerProduct( lv, Vn![ tt[j][k][p] : k in [1..n] ] ) :
			j in [1..n] ];

	bv:= [ Zero( F ) : j in [1..m^2] ];
	for k in [1..m] do
	  bv[(i-1)*m+k]:= Eltseq(L!K.k)[p];
	end for;
	eqs cat:= bv;
      end for;
    end for;

    Vnm:= VectorSpace( F, n*m );
    Vnm2:= VectorSpace( F, n+m^2 );
    H:= Hom( Vnm, Vnm2 );
    eqs:= Transpose(H!eqs);

    sol:= Kernel( eqs );
    sol:= [ L![ Eltseq(sol.i)[j] : j in [1..n] ] : i in [1..Dimension(sol)] ];
     
    return sub< L | sol : Basis >;

end intrinsic; 


////////////////////////////////////////////////////////////////////////
intrinsic DerivedSeries( L::AlgLie ) -> SeqEnum
{The derived series of the Lie algebra L}

  if assigned L`DerivedSeries then return L`DerivedSeries; end if;

  dser:= [ L ];
  I:=L;
  ready:=false;
  while not ready do
    J:= I*I;
    if J eq I then
      ready:=true;
    else
      Append( ~dser, J );
      I:= J;
    end if;
  end while;
  L`DerivedSeries:= dser;
  return dser;

end intrinsic; 


////////////////////////////////////////////////////////////////////////
intrinsic LowerCentralSeries( L::AlgLie ) -> SeqEnum
{The lower central series of the Lie algebra L}

  if assigned L`LowerCentralSeries then return L`LowerCentralSeries; end if;

  lser:= [ L ];
  I:=L;
  ready:=false;
  while not ready do
    J:= L*I;
    if J eq I then
      ready:=true;
    else
      Append( ~lser, J );
      I:= J;
    end if;
  end while;
  L`LowerCentralSeries:= lser;
  return lser;

end intrinsic; 


////////////////////////////////////////////////////////////////////////
intrinsic UpperCentralSeries( L::AlgLie ) -> SeqEnum
{The upper central series of the Lie algebra L}

  if assigned L`UpperCentralSeries then return L`UpperCentralSeries; end if;
  I:= Center( L );
  cser:= [ I ];
  ready:= Dimension( I ) eq 0;
  bas:= [ I.i : i in [1..Dimension(I)] ];

  while not ready do
    K,f:=quo< L | I >;
    J:= Centre( K );
    if Dimension( J ) eq 0 then
      ready:=true;
    else
      bas1:= [ J.i@@f : i in [1..Dimension(J)] ];
      bas1 cat:= bas;
      I:=ideal< L | bas1 >;
      Append( ~cser, I );
      bas:= bas1;
    end if;
  end while;  
  L`UpperCentralSeries:= cser;  
  return cser;

end intrinsic; 


////////////////////////////////////////////////////////////////////////
intrinsic AdjointMatrix( L::AlgLie, x::AlgLieElt ) -> AlgMatLieElt
{The adjoint matrix corresponding to the element x of the Lie algebra L}
  
  require IsCoercible(L, x): "Argument 2 must be coercible into argument 1";

  F:= CoefficientRing( L );
  A:= MatrixLieAlgebra( F, Dimension( L ) );

  mat:= [ ];
  for i in [1..Dimension(L)] do
    mat cat:= Eltseq( L.i*x );
  end for;

  return A!mat;

end intrinsic;


//////////////////////////////////////////////////////////////////////////////
intrinsic IsSolvable( L::AlgLie ) -> BoolElt
{Test whether the Lie algebra L is solvable}

  if assigned L`IsSolvable then return L`IsSolvable; end if;
  dser:=DerivedSeries( L );
  b:= Dimension( dser[ #dser ] ) eq 0;
  L`IsSolvable:= b;
  return b;

end intrinsic;

// IsSoluble defined at c-level

//////////////////////////////////////////////////////////////////////////////
intrinsic IsNilpotent( L::AlgLie ) -> BoolElt
{Test whether the Lie algebra L is nilpotent}

  if assigned L`IsNilpotent then return L`IsNilpotent; end if;
  dser:= LowerCentralSeries( L );
  b:= Dimension( dser[ #dser ] ) eq 0;
  L`IsNilpotent:= b;
  return b;

end intrinsic;

