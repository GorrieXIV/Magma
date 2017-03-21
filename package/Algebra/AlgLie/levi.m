freeze;

//
//   LeviSubalgebra( L )
//
//  A Levi subalgebra of L is a semisimple subalgebra complementary to
//  the solvable radical R. We find a Levi subalgebra of L by first
//  computing a complementary subspace to R. This subspace is a Levi
//  subalgebra modulo R. Then we change the basis vectors such that they
//  form a basis of a Levi subalgebra modulo the second term of the derived
//  series of R after that we consider the third term of the derived series,
//  and so on.
//
intrinsic HasLeviSubalgebra( L::AlgLie ) -> BoolElt, AlgLie
{A Levi subalgebra of the Lie algebra L}

    if assigned L`LeviSubalgebra then return true,L`LeviSubalgebra; end if;

    R:= SolvableRadical( L );
    if Dimension( R ) eq 0 then
       L`LeviSubalgebra:= L;
       return true,L;
    elif Dimension( R ) eq Dimension( L ) then
      levi:= sub< L | [Zero(L)] >;
      L`LeviSubalgebra:= levi;
      return true,levi;
    end if;  
 
    s:= Dimension( L ) - Dimension( R );

    // bb will be a basis of a complement to R in L.

    F:= CoefficientRing( L );
    V:= VectorSpace( F, Dimension( L ) );
    bas:= [ Eltseq( L!R.i ) : i in [1..Dimension(R)] ];
    W:= sub< V | [ V!bas[i] : i in [1..#bas] ] >;
    bb:= [ ];
    for k in [1..Dimension(L)] do
      if #bb eq s then
        break;
      elif not (V!Eltseq(L.k) in W) then
        Append( ~bb, L.k );
        Append( ~bas, Eltseq( L.k ) );
        W:= sub< V | [ V!bas[i] : i in [1..#bas] ] >;        
      end if;
    end for;

    W:= sub< V | [ V!Eltseq( bb[i] ) : i in [1..#bb] ] >;
    subalg:= true;    
    for i in [1..#bb] do 
      for j in [i+1..#bb] do
        x:= V!Eltseq( bb[i]*bb[j] );
        if not (x in W) then
          subalg:= false;
          break;
        end if;
      end for;
    end for;

    if subalg then
      levi:= sub< L | bb : Basis >;
      L`LeviSubalgebra:= levi;
      return true,levi;
    end if;    

    ser:= DerivedSeries( R );

    // We now calculate a basis of R such that the first k1 elements
    // form a basis of the last nonzero term of the derived series ser,
    // the first k2 ( k2>k1 ) elements form a basis of the next to last
    // element of the derived series, and so on.

    p:= #ser ;
    i:= p-1;
    Rbas:= [ L!( ser[p-1].l )  : l in [1..Dimension(ser[p-1])] ];
    bas:= [ V!Eltseq( Rbas[l] ) : l in [1..#Rbas] ];
    W:= sub< V | bas >;
    while #Rbas lt Dimension(R) do
      if #Rbas eq Dimension(ser[i]) then
        i:= i-1;
        k:= 1;
      else
        x:= V!Eltseq( L!( ser[i].k )  );
        if not x in W then
          Append( ~Rbas, L!( ser[i].k )  );
          Append( ~bas, x );
          W:= sub< V | bas >;
        end if;
        k:= k+1;
      end if;
    end while;

    levi:= bb;
    bb cat:=Rbas;

    // So now bb is a list of basis vectors of L such that
    // the first elements form a basis of a complement to R
    // and the remaining elements are a basis for R of the form
    // described above.
    // We now calculate a structure constants table of the Levi
    // subalgebra w.r.t. this basis.

    bas:= [ Eltseq( bb[i] ) : i in [1..#bb] ];
    W:= VectorSpaceWithBasis([V | bas[i] : i in [1..#bas] ]);
    T:= [ [] : i in [1..s] ];
    for i in [1..s] do
      for j in [i+1..s] do
        cf:= Coordinates( W, V!Eltseq( levi[i]*levi[j] ) );
        cf:= [ cf[l] : l in [1..s] ];
        klist:=[]; cflist:= [ ];
        for l in [1..s] do
          if cf[l] ne Zero(F) then
             Append( ~klist, l ); Append( ~cflist, cf[l] );
          end if;
        end for;
        T[i][j]:= [* klist,cflist *];
      end for;
    end for;

    // Now levi is a Levi subalgebra modulo R.
    // The loop modifies this modulo statement.
    // After the first round levi will be a Levi subalgebra modulo
    // the second element of the derived series.
    // After the second step levi will be a Levi subalgebra modulo
    // the third element of the derived series.
    // And so on.

    for a in [1..p-1] do

      // comp will be a basis of the complement of the a+1-th element
      // of the derived series in the a-th element of the derived series.
      // B will be a basis of the a-th term of the derived series,
      // such that the basis elements of the complement come first.
      // So if we have an element v of the a-th term of the derived series,
      // then by taking the coefficients w.r.t. B, we can easily find
      // the part that belongs to comp.
      // The equations we have are vector equations in the space comp,
      // i.e., in the quotient of two elements of the derived series.
      // But we do not want to work with this quotient directly.

      comp:= [ Rbas[i] : i in [Dimension(ser[a+1])+1..Dimension(ser[a])] ];
      dim:= #comp;
      bb:= comp;
      bb cat:= [ Rbas[i] : i in [1..Dimension( ser[a+1] )] ];
      bb:= [ Eltseq( bb[i] ) : i in [1..#bb] ];
      W:= VectorSpaceWithBasis([V | bb[i] : i in [1..#bb] ]);

      cf:= [ Coordinates( W, V!Eltseq(comp[i]) ) : i in [1..#comp] ];
      cf:= [ [cf[i][j] : j in [1..dim]] : i in [1..#cf] ];
      V1:= VectorSpace( F, s*dim );
      V2:= VectorSpace( F, dim*s*(s-1) div 2 );
      eqs:= Zero( Hom(V1,V2) );
      rl:= [];
      for i in [1..s] do
        for j in [i+1..s] do
          cij:= T[i][j];
          for k in [1..dim] do

            cf1:= Coordinates( W, V!Eltseq(levi[i]*comp[k]) );
            cf2:= Coordinates( W, V!Eltseq(comp[k]*levi[j]) );
            cf1:= [ cf1[l] : l in [1..dim] ];
            cf2:= [ cf2[l] : l in [1..dim] ];

            for l in [1..dim] do
              eqno:=(i-1)*(2*s-i)*dim div 2+(j-i-1)*dim+l;

              eqs[(j-1)*dim+k][eqno]:= eqs[(j-1)*dim+k][eqno]+cf1[l];
              eqs[(i-1)*dim+k][eqno]:= eqs[(i-1)*dim+k][eqno]+cf2[l];

              for m in [1..#cij[1]] do
                r:=cij[1][m];
                eqs[(r-1)*dim+k][eqno]:= eqs[(r-1)*dim+k][eqno]-
                                           cij[2][m]*cf[k][l];
              end for;
            end for;
          end for;

          x:= Zero(L);
          for m in [1..#cij[1]] do
            x:= x+cij[2][m]*levi[cij[1][m]];
          end for;
          x:= x-levi[i]*levi[j];
          co:= Coordinates( W, V!Eltseq(x) );
          co:= [ co[l] : l in [1..dim] ];
          rl cat:= co;
        end for;
      end for;

      yn,sol:= IsConsistent( eqs, V2!rl );
      if not yn then return yn,_; end if;

      for i in [1..s] do
        for j in [1..dim] do
          levi[i]:=levi[i]+sol[(i-1)*dim+j]*comp[j];
        end for;
      end for;
    end for;

    K:=sub< L | levi : Basis >;
    L`LeviSubalgebra:= K;
    return true,K;
    
end intrinsic;



