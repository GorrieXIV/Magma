
freeze;


// The matrix of the Killing form.
//

intrinsic KillingMatrix( L::AlgLie ) -> ModMatFldElt
{The matrix of the Killing form of L}

    return KillingForm( L );

/* I have removed this function, it already exists as KillingForm -- SHM
    if assigned L`KillingMatrix then  return L`KillingMatrix; end if;

    n:= Dimension( L );
    Kmat:= Zero( MatrixRing( CoefficientRing(L), n ) );
    adL:= [ AdjointMatrix( L, L.i ) : i in [1..n] ];
    for i in [1..n] do
      for j in [i..n] do
        Kmat[i][j]:= Trace( adL[i]*adL[j] );
        if i ne j then Kmat[j][i]:= Kmat[i][j]; end if;
      end for;
    end for;

    L`KillingMatrix:= Kmat;
    return Kmat;
*/

end intrinsic;


//
//  DirectSumDecomposition( L )
//
//  This function calculates a list of ideals of L such that L is equal
//  to the direct sum of them.
//  The existence of a decomposition of L is equivalent to the existence
//  of a nontrivial idempotent in the centralizer of ad L in the full
//  matrix algebra M_n(F). In the general case we try to find such
//  idempotents.
//  In the case where the Killing form of L is nondegenerate we can use 
//  a more elegant method. In this case the action of the Cartan
//  subalgebra will identify the direct summands.
//
intrinsic DirectSumDecomposition( L::AlgLie ) -> SeqEnum
{The decomposition of L as a direct sum of indecomposable ideals}

    if assigned L`DirectSumDecomposition then 
      return L`DirectSumDecomposition;
    end if;

    n:= Dimension( L );
    if n eq 0 then
	L`DirectSumDecomposition := [];
	return L`DirectSumDecomposition;
    elif n eq 1 then
	L`DirectSumDecomposition := [L];
	return L`DirectSumDecomposition;
    end if;

    F:= CoefficientRing( L );
    Kmat:= KillingMatrix( L );

    if Rank( Kmat) eq n then

      // The algorithm works as follows.
      // Let H be a Cartan subalgebra of L.
      // First we decompose L into a direct sum of subspaces B[i]
      // such that the minimum polynomial of the adjoint action of an
      // element of H restricted to B[i] is irreducible.
      // If L is a direct sum of ideals, then each of these subspaces
      // will be contained in precisely one ideal.
      // If the field F is big enough then we can look for a splitting
      // element in H.
      // This is an element h such that the minimum polynomial of ad h
      // has degree dim L - dim H + 1.
      // If the size of the field is bigger than 2*m then there is a 
      // powerful randomised algorithm (Las Vegas type) for finding such
      // an element. We just take a random element from H and with
      // probability > 1/2 this will be a splitting element. 
      // If the field is small, then we use decomposable elements 
      // instead.
      
      H:= CartanSubalgebra( L );

      m:= (( n - Dimension(H) ) * ( n - Dimension(H) + 2 )) / 8;
      m:= IntegerRing()!m;

      // It seems that this next condition is not enough to guarantee
      // an abundance of splitting elements.
      // I have added code to keep track of how many random trials we use
      // and if this exceeds 20 then go to the other method.
      // Bill Unger 6 Aug 2012.
      //
      // The problem seems to be with non-prime fields that are big enough
      // to pass the 2*m lt #F test, but the prime field isn't big enough.
      // The coefficients used to generate the random elements were all from
      // the prime field. I will change this to use random field elts when
      // F is a finite field. So, the condition is enough provided we take
      // a better random element generator.
      // Bill Unger 7 Aug 2012.

      use_splitting_elt := (Characteristic(F) eq 0 or 2*m lt #F) and
	    ( not Characteristic( F ) in [2,3] );

      if use_splitting_elt then

	set := IsFinite(F) select F else  [ -m .. m ];
	count := 0;
        while use_splitting_elt do 
          x:= &+[ Random( set )*H.i : i in [1..Dimension(H)] ];
          M:= Matrix(AdjointMatrix( L, L!x ));
          f:= MinimalPolynomial( M );
          if Degree( f ) eq n - Dimension( H ) + 1 then
	      break;
	  end if;
	  count +:= 1;
	  use_splitting_elt := count lt 30;
	end while;

      end if;

      if use_splitting_elt then
      // We decompose the action of the splitting element:

        facs:= Factorization( f );
        B:= [];
        V:= VectorSpace( F, n );
        W:= sub< V | [V!Eltseq( L!H.i ) : i in [1..Dimension(H)] ] >;
        for p in facs do
          b:= NullSpace( Evaluate( p[1], M ) );
          if not V!Eltseq( b.1 ) in W then
            Append( ~B, [ L!Eltseq( b.i ) : i in [1..Dimension(b)] ] );
          end if;
        end for;

      else

       // (Bill U 6/8/12) Either use_splitting_elt has failed or 
       // Here L is a semisimple Lie algebra over a small field or a
       // field of characteristic 2 or 3. This means that 
       // the existence of splitting elements is not assured. So we work
       // with decomposable elements rather than with splitting ones. 
       // A decomposable element is an element from the associative
       // algebra T generated by ad H that has a reducible minimum 
       // polynomial. Let V be a stable subspace (under the action of H)
       // computed in the process. Then we proceed as follows.
       // We choose a random element from T and restrict it to V. If
       // this element has an irreducible minimum polynomial of degree 
       // equal to the dimension of the associative algebra T restricted 
       // to V, then V is irreducible. On the other hand,
       // if this polynomial is reducible, then we decompose V. 

       // bas will be a basis of the associative algebra generated by 
       // ad H. The computation of this basis is facilitated by the fact 
       // that in most cases we know the dimension of this algebra.

        bas:= [ Matrix(AdjointMatrix( L, L!H.i )) : i in [1..Dimension(H)] 
];
        V:= RMatrixSpace( F, n, n );
        W:= sub< V | [ V!bas[i] : i in [1..#bas] ] >;
  
        k:=1; l:=1;
        while k le #bas do
          if #bas eq n-Dimension(H) then break; end if;
          M:= bas[ k ]*bas[ l ];
          if not V!M in W then
            Append( ~bas, M );
            W:= sub< V | [ V!bas[i] : i in [1..#bas] ] >;            
          end if;
          if l lt #bas then l:=l+1; 
                       else k:=k+1; l:=1;
          end if;
        end while;
        Append( ~bas, bas[1]^0);

       // Now B will be a list of (bases of) subspaces of L stable under
       // H. We stop once every element from B is irreducible. We
       // start with B= [ a basis of H*L ].

        b:= [ ];
        V:= VectorSpace( F, n );
        W:= sub< V | V!Eltseq( Zero( L ) ) >;
        k:=1; l:=1;
        while #b lt n-Dimension( H ) do
          x:= ( L!H.k )*L.l;
          if not V!Eltseq(x) in W then 
            Append( ~b, x );
            W:= sub< V | [V!Eltseq( b[i] ) : i in [1..#b] ] >;
          end if;
          if l lt n then l:=l+1;
                    else k:=k+1; l:=1;
          end if;
        end while;

        B:= [b];
        k:= 1; 
        mps:= Hom( V, V );

        while k le #B  do

          if #B[k] eq 1 then
            k:=k+1;
          else

            M:= &+[ Random( F )*bas[i] : i in [1..#bas] ];
            M:= mps!M;
  
           // Now we restrict M to the space B[k].

            mat:= [ ];
            W:= VectorSpaceWithBasis([V | 
                           Eltseq(B[k][i]) : i in [1..#B[k]]]);
            for e in B[k] do
              x:= (V!Eltseq( e ))*M;
              mat cat:= Coordinates( W, x );
            end for;

            M:= MatrixAlgebra(F,#B[k])!mat;
            f:= MinimalPolynomial( M );
            facs:= Factorization( f );

            if #facs eq 1 then

           // We restrict the basis bas to the space B[k]. If the length
           // of the result is equal to the degree of f then B[k] is
           // irreducible. 

              sp:= RMatrixSpace( F, #B[k], #B[k] );
              spres:= sub< sp | Zero(sp)>;
              bb:=[];
              for j in [1..#bas] do              
                mat:= [ ];
                for e in B[k] do
                  x:= (V!Eltseq( e ))*mps!bas[j];
                  mat cat:= Coordinates( W, x );
                end for;

                if not sp!mat in spres then
                  Append( ~bb, mat );
                  spres:= sub< sp | [ sp!bb[s] : s in [1..#bb] ] >;
                end if;

              end for;

              if #bb eq Degree(f) then
  
                // The space is irreducible.
  
                k:=k+1;
  
              end if;
            else

              // We decompose B[k] and we substitute the new spaces for
              // B[k];
              
              Bnew:= Remove( B, k );

              for p in facs do
                b:= NullSpace( Evaluate( p[1], M ) );
                b:= [ &+[ Eltseq(b.i)[j]*B[k][j] : j in [1..#B[k]] ] :
                       i in [1..Dimension(b)]  ];
                Append( ~Bnew, b );
              end for;
        
              B:=Bnew;

            end if;
           end if;

        end while;

      end if;

      // Now the pieces in B are grouped together.

      ideals:=[]; spaces:= [* *]; 
      k:=1;
      V:= VectorSpace( F, n );

      while k le #B do

        // Check whether B[k] is contained in any of
        // the ideals obtained so far.

        contained := false;
        i:=1;
        while not contained and i le #spaces do
          if V!Eltseq(B[k][1]) in spaces[i] then
            contained:= true;
          end if;
          i:=i+1;
        end while;

        if contained then     

          k:=k+1;

        else

          // B[k] generates a new ideal.
          
          id,g:= ideal< L | B[k] >;
          sp:= sub< V | [ V!Eltseq( g(id.s) ) : s in [1..Dimension(id)] ]>;
          Append( ~ideals, id );
          Append( ~spaces, sp ); 
          k:= k+1;

        end if;

      end while;

      L`DirectSumDecomposition:= ideals;
      return ideals;

    else

      // First we try to find a central component, i.e., a decomposition
      // L=I_1 \oplus I_2 such that I_1 is contained in the center of L.
      // Such a decomposition exists if and only if the center of L is
      // not contained in the derived subalgebra of L.

      C:= Center( L );

      if Dimension( C ) eq Dimension( L ) then
        
        //Now L is abelian; hence L is the direct sum of dim L ideals.

        ideals:=[];
        for i in [1..n] do
          I:=ideal< L | L.i : Basis>;
          Append( ~ideals, I );
        end for;

        L`DirectSumDecomposition:= ideals;
        return ideals;

      end if; 
                

      if 0 lt Dimension( C ) then

        D:= L*L;
        CD:= C meet D;

        if Dimension( CD ) lt Dimension( C ) then

          // The central component is the complement of CD in C.

          B1:=[];
          k:=1;
          V:= VectorSpace( F, Dimension(C) );
          W:= sub< V | [V!Eltseq(C!CD.i) : i in [1..Dimension(CD)]] >;
          U:= Complement( V, W );
          B1:= [  &+[ Eltseq(U.i)[j]*C.j : j in [1..Dimension(C)] ] :
                    i in [1..Dimension(U)] ];
          B1:= [ L!B1[i] : i in [1..#B1] ];

          // The second ideal is a complement of the central component
          // in L containing D.

          B2:= [ L!D.i : i in [1..Dimension(D)] ];
          k:= 1;
          b:= B1 cat B2;
          V:= VectorSpace( F, n );
          b:= [ V!Eltseq(b[i]) : i in [1..#b] ];
          W:= sub< V | b >;
       
          while #b ne n do
            if not V!Eltseq(L.k) in W then
              Append( ~B2, L.k );
              Append( ~b, V!Eltseq(L.k) );
              W:= sub< V | b >;
            end if;
            k:= k+1;
          end while;

          ideals1:=[];
          for i in [1..#B1] do
            I:=ideal< L | B1[i] : Basis >;
            Append( ~ideals1, I );
          end for;          

         // We continue the decomposition for the second part.

          L1:= ideal< L | B2 : Basis >;
          n:= Dimension( L1 );

        else

          L1:=L; ideals1:=[];

        end if;

      else

        L1:=L; ideals1:=[];

      end if;

      // Now we are in the situation where L1 does not have a central
      // component and compute the centralizer of ad L1 in M_n(F).

      An:= MatrixAlgebra( F, n );
      ad:= sub< An | [ AdjointMatrix( L1, L1.i ) : i in [1..n]] >;

      centralizer:= Centralizer( An, ad );
      Rad:= JacobsonRadical( centralizer );
      if Dimension( centralizer ) - Dimension( Rad ) eq 1 then
        // Now L1 is simple.

        ideals:= [L1] cat ideals1;
        L`DirectSumDecomposition := ideals;
        return ideals;

      end if;

      // Let Q be the semisimple commutative associative algebra
      // centralizer/Rad.
      // We calculate a complete set of orthogonal idempotents in Q
      // and then lift them to centralizer.
      // The orthogonal idempotents in Q correspond to the decomposition
      // of Q as a direct sum of simple ideals. Now ids will contain
      // a list of ideals of Q such that the direct sum of these equals
      // Q. The variable idpots will contain the idempotents 
      // corresponding to the ideals in ids.
      // The algorithms has two parts: one for small fields (of size
      // less than 2*Dimension( Q ), and one for big fields. 
      // If the field is big, then using a Las Vegas algorithm we find a
      // splitting element (this is an element that generates Q). By
      // factoring the minimal polynomial of such element we can find a
      // complete set of orthogonal idempotents in one step.
      // However, if the field is small splitting elements might not
      // exist.
      // In this case we use decomposable elements (of which the minimum
      // polynomial factors into two (or more) relatively prime factors.
      // Then using the same procedure as for splitting elements we can
      // find some idempotents. But in this case the corresponding
      // ideals might split further. So we have to find decomposable 
      // elements in these and so on. 
      // Decomposable elements are found as follows: first we calculate
      // the subalgebra of all elements x such that x^q=x
      // (where q=Size( F )).
      // This subalgebra is a number of copies of the ground field. So
      // any element independent from 1 of this subalgebra will have a
      // minimum polynomial that splits completely. On the other hand, 
      // if 1 is the only basis vector of this subalgebra than the 
      // original algebra was simple.
      // For a more elaborate description we refer to "W. Eberly and M.
      // Giesbrecht, Efficient Decomposition of Associative Algebras,
      // Proceedings of ISSAC 1996."

      Q,hm:= quo< centralizer | Rad >;
      idpots:= [ One( Q ) ];
      ids:= [ Q ];

      // The variable k will point to the first element of ids that 
      // still has to be decomposed.

      k:=1;

      if Characteristic(F) eq 0 or #F gt 2*Dimension( Q )^2 then
        set:= [ One(F)*i : i in [ 0 .. 2*Dimension(Q)^2 ] ];
      else
        set:= [ ];
      end if;

      repeat

        if #set gt 1 then 

          // We are in the case of a big field.

          repeat

            // We try to find an element of Q that generates it.
            // If we take the coefficients of such an element randomly
            // from a set of 2*Dimension(Q)^2 elements,
            // then this element generates Q with probability > 1/2

            e:= &+[ Random( set )*Q.i : i in [1..Dimension(Q)] ];
            f:= MinimalPolynomial( e );

          until Degree( f ) eq Dimension( Q );

        else
  
          // Here the field is small.

          q:= #F;
 
        // sol will be a basis of the subalgebra of the k-th ideal
        // consisting of all elements x such that x^q=x.
        // If the dimension of sol is 1
        // then the ideal is simple and we proceed to the next one. If
        // all ideals are simple then we quit the loop.

          sol:= [ ];
          while #sol lt 2 and k le #ids  do
            bQ:= Basis( ids[k] );
            eqs:= [ ];
            for i in [1..Dimension( ids[k] )] do
              eqs cat:= Coordinates( ids[k], bQ[i]^q-bQ[i] );
            end for;
            V:= VectorSpace( F, Dimension(ids[k]) );
            eqs:= Hom(V,V)!eqs;
            sol:= NullSpace( eqs );
            sol:= [ ids[k]!Eltseq(sol.i) : i in [1..Dimension(sol)] ];
            if #sol eq 1 then k:=k+1; end if;
          end while; 

          if k gt #ids then break; end if;
    
          V:= VectorSpace( F, Dimension( ids[k] ) );
          W:= sub< V | V!Eltseq( One( ids[k] ) ) >;
          e:= sol[1];
          if V!Eltseq(e) in W then e:=sol[2]; end if;

        // We calculate the minimum polynomial of e.

          f:= MinimalPolynomial(e);

        end if;

        facs:= Factorization( f );

      // Now we find elements h1,...,hs such that hi = 1 mod facs[i] and
      // hi = 0 mod facs[j] if i ne j.
      // This is possible due to the Chinese remainder theorem.

        hlist:= [ ];
        for i in [1..#facs] do
          cf:= [ Zero( F ) : i in [1..#facs] ];
          cf[i]:= One(F);
          j:= 1;
          c:= cf[1];
          p:= facs[1][1];
          while j lt #facs do
            j:= j + 1;
            gcd,g1,g2:= XGCD( p, facs[j][1] );
            c:= p*( ( g1*(cf[j]-c) div gcd ) mod facs[j][1] )+ c;
            p:= p*facs[j][1] div gcd;
          end while;

          Append( ~hlist, c mod p );

        end for;

      // Now a set of orthogonal idempotents is given by hi(e).

        _,phi:= RegularRepresentation( ids[k] );
        id:= [ Evaluate( hlist[i], phi(e) )@@phi : i in [1..#hlist] ];

        if #set eq 0 then

        // We are in the case of a small field;
        // so we append the new idempotents and ideals
        // (and erase the old ones). (If E is an idempotent, 
        // then the corresponding ideal is given by E*Q*E.)

          idpots1:= Remove( idpots, k );
          ids1:= Remove( ids, k );

          bQ:= Basis( ids[k] );      
          for i in [1..#id] do
            bb:= [ id[i]*bQ[j]*id[i] : j in [1..#bQ] ];
            IQ:= ideal< ids[k] | bb >;
            Append( ~ids1, IQ );
            Append( ~idpots1, Q!id[i] );
          end for;

          ids:= ids1;
          idpots:= idpots1;

        else

        // Here the field is big so we found the complete list of
        // idempotents in one step.
          
          idpots:= id;
          k:= #ids+1;

        end if;

        while k le #ids and Dimension( ids[k] ) eq 1 do 
          k:=k+1; 
        end while;

      until k gt #ids;

      id:= [ idpots[i]@@hm : i in [1..#idpots] ]; 
   
      // Now we lift the idempotents to the big algebra centralizer.
      // The first idempotent is lifted as follows:
      // We have that id[1]^2-id[1] is an element of Rad.
      // We construct the sequences e_{i+1} = e_i + n_i - 2e_in_i,
      // and n_{i+1}=e_{i+1}^2-e_{i+1}, starting with e_0=id[1].
      // It can be proved by induction that e_q is an idempotent in A
      // because n_0^{2^q}=0.
      // Now E will be the sum of all idempotents lifted so far.
      // Then the next lifted idempotent is obtained by setting
      // ei:=id[i]-E*id[i]-id[i]*E+E*id[i]*E;
      // and lifting as above. It can be proved that in this manner we
      // get an orthogonal system of primitive idempotents.

      E:= Zero( F )*id[1];
      for i in [1..#id] do
        ei:= id[i]-E*id[i]-id[i]*E+E*id[i]*E;
        q:= 0;
        while 2^q le Dimension( Rad ) do
          q:= q+1;
        end while;
        ni:= ei*ei-ei;
        for j in [1..q] do
          ei:= ei+ni-2*ei*ni;
          ni:= ei*ei-ei;
        end for;
        id[i]:= ei;
        E:= E+ei;
      end for;

      // For every idempotent of centralizer we calculate
      // a direct summand of L1.

      ideals:= [ ]; 
      for i in [1..#id] do
        I:= ideal< L1 | [L1!Eltseq(id[i][j]) : j in [1..n]] >;
        Append( ~ideals, I );
      end for;

      if ideals1 ne [] then
        ideals cat:= ideals1;
      end if;

      L`DirectSumDecomposition:= ideals;
      return ideals;

    end if;

end intrinsic;

intrinsic IndecomposableSummands( L::AlgLie ) -> SeqEnum
{The decomposition of L as a direct sum of indecomposable ideals}
  return DirectSumDecomposition( L );
end intrinsic;
