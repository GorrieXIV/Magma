freeze;

//
//  Cartan subalgebras
//
//  A Cartan subalgebra of the Lie algebra L is by definition a nilpotent
//  subalgebra equal to its own normalizer in L.
//


intrinsic IsCartanSubalgebra( L::AlgLie, H::AlgLie ) -> BoolElt
{True iff H is a Cartan subalgebra of L}

    require ISA( Category(BaseRing(L)), Fld ) : 
      "The Lie algebra must be defined over a field";
      
    require ExistsCoveringStructure(L,H) and H subset L :
      "Not a subalgebra";

    ret := IsNilpotent( H ) and Normaliser( L, H ) eq H;
    if ret and not assigned L`CartanSubalgebra then
      L`CartanSubalgebra := H;
    end if;

    return ret;

end intrinsic;





//  By defintion, an Engel subalgebra of L is the generalized eigenspace
//  of a non nilpotent element, corresponding to the eigenvalue 0.
//  In a restricted Lie algebra of characteristic p we have that every Cartan
//  subalgebra of an Engel subalgebra of L is a Cartan subalgebra of L.
//  Hence in this case we construct a decreasing series of Engel subalgebras.
//  When it becomes stable we have found a Cartan subalgebra.
//  On the other hand, when L is not restricted and is defined over a field
//  F of cardinality greater than the dimension of L we can proceed as
//  follows.
//  Let a be a non nilpotent element of L and K the corresponding
//  Engel subalgebra.  Furthermore, let b be a non nilpotent element of K.
//  Then there is an element c \in F such that a + c ( b - a ) has an
//  Engel subalgebra strictly contained in K
//  (see Humphreys, proof of Lemma A, p 79).
//



intrinsic CartanSubalgebra( L::AlgLie ) -> AlgLie
{The Cartan subalgebra of the Lie algebra L}

    if assigned L`CartanSubalgebra then return L`CartanSubalgebra; end if;

    n:= Dimension( L );
    F:= CoefficientRing( L );

    require ISA( Category(F), Fld ) : 
      "The Lie algebra must be defined over a field";

    if Characteristic( F ) gt 0 and n ge #F then
      K:= L;
      f:= hom< L -> L | Morphism(L,L) >;
      while true do

        a:= NonNilpotentElement( K );

        if a eq Zero(K) then
          // K is a nilpotent Engel subalgebra, hence a Cartan subalgebra.
          L`CartanSubalgebra:= K;
          return K;
        end if;

        // a is a non nilpotent element of K.
        // We construct the generalized eigenspace of this element w.r.t.
        // the eigenvalue 0.  This is a subalgebra of K and of L.

        A:= AdjointMatrix( K, a);
	MatAlg:= MatrixAlgebra( F, Nrows(A) );
	A := MatAlg!A;
        A:= A ^ Dimension( K );
        V:= VectorSpace( F, Dimension( K ) );
        bas:= Kernel( A ); 
        bas:= [ K!Eltseq(bas.i) : i in [1..Dimension(bas)] ];
// AKS: VERY SLOW!!! :
        K,f:= sub< L | [ f(bas[i]) : i in [1..#bas] ] : Basis >;

      end while;

    else
      // We start with an Engel subalgebra. If it is nilpotent
      // then it is a Cartan subalgebra and we are done.
      // Otherwise we make it smaller.

      a:= NonNilpotentElement( L );
      if a eq Zero(L) then
        // L is nilpotent.

        L`CartanSubalgebra:= L;
        return L;
      end if;

      // K will be the Engel subalgebra corresponding to a.
      V:= VectorSpace( F, n );
      A:= AdjointMatrix( L, a);
      MatAlg:= MatrixAlgebra( F, Nrows(A) );
      A := MatAlg!A;
      A:= A ^ n;
      bas:= Kernel( A );
      bas:= [ L!Eltseq(bas.i) : i in [1..Dimension(bas)] ];
      K,f:= sub< L | bas : Basis >;

      // We locate a nonnilpotent element in this Engel subalgebra.
      b:= f( NonNilpotentElement( K ) );

      // If b = 0 then K is nilpotent and we are done.
      ready:= ( b eq Zero(L) );

      while not ready do

        // We find an element a + c*(b-a) such that the Engel subalgebra
        // belonging to this element is properly contained in the Engel 
        // subalgebra belonging to a.
        // We do this by checking a few values of c
        // (At most n values of c will not yield a smaller subalgebra.)
        sp:= sub< V | [V!Eltseq( f( K.i ) ) : i in [1..Dimension(K)] ] >;
        found:= false;

        cn := 0; 
        if IsFinite(F) then gF := Generator(F); end if;

        while not found do
          if IsFinite(F) then
	        c := (cn eq 0) select Zero(F) else gF^cn;
          else
            c := cn;
          end if;
          cn +:= 1;
          newelt:= a+c*(b-a);

          // Calculate the Engel subalgebra belonging to newelt.
          A:= AdjointMatrix( L, newelt);
	      MatAlg:= MatrixAlgebra( F, Nrows(A) );
	      A := MatAlg!A;
          A:= A ^ n;
          bas:= Kernel( A ); 
          bas:= [ L!Eltseq(bas.i) : i in [1..Dimension(bas)] ];

          // We have found a smaller subalgebra if the dimension is smaller
          // and new basis elements are contained in the old space.

          found:= #bas lt Dimension( K );
          i:= 1;
          while i le #bas and found do
            if not V!Eltseq(bas[i]) in sp then
              found:= false;
            end if;
            i:= i+1;
          end while;
        end while;

        a:= newelt;
        K,f:= sub< L | bas : Basis >;
        b:= f( NonNilpotentElement( K ) );

        // If b = 0 then K is nilpotent and we are done.
        ready:= b eq Zero(L);

      end while;

    end if;
      L`CartanSubalgebra:= K;
      return K;

end intrinsic;



//
//  Splitting Cartan subalgebra
//
//  For some purposes we need our Cartan subalgebra to be splitting.
//  That is, we need it to be simultaneously triangularisable over
//  the base field (this is always true over an extension).
//
//  If a Lie algebra has a splitting CSA, it is called split.
//
//  We only provide basic support for this at present.
//

isSplitPol := func< f | &+[ t[2] : t in Factorisation(f) ] eq Degree( f ) 
>;

intrinsic IsSplittingCartanSubalgebra( L::AlgLie, H::AlgLie ) -> BoolElt
{True iff H is a splitting Cartan subalgebra of L}

    if not IsCartanSubalgebra( L, H ) then  return false;  end if;
  
    B := ChangeUniverse( Basis( H ), L );
    ad := AdjointRepresentation( L : ComputePreImage := false);
    return forall{ b : b in B | 
      isSplitPol( CharacteristicPolynomial(ad(b)) ) };

end intrinsic;

intrinsic SplittingCartanSubalgebra( L::AlgLie ) -> AlgLie
{A splitting Cartan subalgebra for L}

    if not assigned L`SplittingCartanSubalgebra then
      H := CartanSubalgebra( L );
      if IsSplittingCartanSubalgebra( L, H ) then
        L`SplittingCartanSubalgebra := H;
      elif IsReductive( L ) and IsFinite( CoefficientRing( L ) ) then
        L`SplittingCartanSubalgebra := SplitMaximalToralSubalgebra( L );
      else
        error "Error:  Unable to compute splitting Cartan subalgebra";
      end if;
    end if;
    
    return L`SplittingCartanSubalgebra;
end intrinsic;


