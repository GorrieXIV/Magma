
freeze;


// This file contains functions for computing a faithful module of 
// a Lie algebra; the Lie algebra is required to be either solvable, or 
// have a Levi subalgebra (so modular Lie algebras, which are not 
// solvable, not semisimple, and do not have a Levi subalgebra, and
// have a non-trivial centre are excluded).

// First we have three functions for computing a series of subalgebras of 
// a Lie algebra, such that the first subalgebra is abelian and the last 
// is equal to the Lie algebra. Every subalgebra is the semidirect sum of 
// the previous one with a subalgebra (which in the solvable case is 
// always 1-dimensional).  
series_nilp:= function( L )

      
     lowc:= Reverse( LowerCentralSeries( L ) );
     ss:= [ [ L!( lowc[2].i ) : i in [1..Dimension(lowc[2])] ] ]; 

     bid:= ss[1];
     id:= ideal< L | ss[1] >;
     no_elts:= #ss[1];
     d:= 2;
     while no_elts lt Dimension( L ) do

           for i in [1..Dimension(lowc[d+1])] do
               if not lowc[d+1].i in id then
                  Append( ~ss, [ lowc[d+1].i ] );
                  Append( ~bid, lowc[d+1].i );
                  id:= ideal< L | bid >;
                  no_elts:= no_elts+1;
               end if;
           end for;
           d:= d+1;
     end while;

     return ss;

end function;

series_solv:= function( L )

     N:= NilRadical( L );
     sN:= series_nilp( N );
     ss:= [ [ L!u : u in s ] : s in sN ];
     
     der:= Reverse( DerivedSeries( L ) );
     d:= 2;
     is_contained:= true;
     while is_contained do
           d:= d+1;
           is_contained:= &and[ der[d].i in N : i in [1..Dimension(der[d])] ];
     end while;
     
     id:= N;
     bid:= [ L!u : u in Basis(N) ];
     while d le #der do
           for x in Basis( der[d] ) do
               if not x in id then
                  Append( ~ss, [ L!x ] );
                  Append( ~bid, L!x );
                  id:= ideal< L | bid >;
               end if;
           end for; 

           d:= d+1;
     end while;

     return ss;

end function;

series_gen:= function( L )

     R:= SolvableRadical( L );
     _,K:= HasLeviSubalgebra( L );
     if IsNilpotent( R ) then
        sR:= series_nilp( R );
     else
        sR:= series_solv( R ); 
     end if;
     ss:= [ [ L!u : u in s ] : s in sR ];
     Append( ~ss, [ L!u : u in Basis(K) ] );
     return ss;

end function;

// Now we have a function for extending a representation;
// U is the uea of L, and we have a representation of the
// subalgebra spanned by L.1,...,L.{ind1-1}, given by the matrices
// in the list `mats'. This representation
// is extended to the subalgebra spanned by L.1,..,L.ind2.

extend_rep:= function( U, L, mats, ind1, ind2 )
 
     // Let K be the subalgebra spanned by L.k for 1 <= k < ind1.
     // If ind1 = ind2 then set ind = ind1, and x = L.ind;
     // In that case we first see whether there is a y\in K such that 
     // [x-y,K]=0, and [x-y,x] = 0. 
     // Otherwise (i.e., we extend by the Levi subalgebra) we jump
     // immediately to the piece using coefficient spaces.

     F:= CoefficientField( L );
     n:= NumberOfRows( mats[1] );

     oneF:= One( F );
     zeroF:= Zero( F );
     oneU:= One( U );

     if ind1 eq ind2 then
        ind:= ind1;

        eqs:= ZeroMatrix( F, ind-1, ind^2 );
        for i in [1..ind-1] do
            for j in [1..ind] do
                cc:= Coordinates( L, L.i*L.j );
                for k in [1..ind] do
                    eqs[ i ][ (j-1)*ind+k ]:= cc[k];
                end for;
            end for;
        end for;

        rhs:= Vector( [ zeroF : i in [1..ind^2] ] );
        for j in [1..ind] do
            cc:= Coordinates( L, L.ind*L.j );
            for k in [1..ind] do
                rhs[ (j-1)*ind + k ]:= cc[k];
            end for;
        end for;     

        bool,sol:= IsConsistent( eqs, rhs );
     else
        bool:= false;
     end if;
        
     if bool then
        // y will be the matrix of the element represented by `sol':
        for i in [1..ind-1] do
            if i eq 1 then
               y:= sol[1]*mats[1];
            else
               y:= y + sol[i]*mats[i];
            end if;
        end for;

        new_mats:= [ ];
        for i in [1..ind-1] do
            // from nxn matrices we make n+2 x n+2 matrices.
            mat:= ZeroMatrix( F, n+2, n+2 );
            for j in [1..n] do
                for k in [1..n] do
                    mat[j][k]:= mats[i][j][k];
                end for;
            end for;

            Append( ~new_mats, mat );
        end for;
            
        // we add the matrix of the ind-th element:

        mat:= ZeroMatrix( F, n+2, n+2 );
        for j in [1..n] do
            for k in [1..n] do
                mat[j][k]:= y[j][k];
            end for;
        end for;
        mat[n+1][n+2]:= oneF;
        Append( ~new_mats, mat );
        return new_mats, true;

     else  // We construct the coefficient space, and the module
           // generated by it.

        trans_mats:= [ Transpose(x) : x in mats ];

        deg:= 0;
        d_set:= [ oneU ];
        d_set_degs:= [ d_set ];
        d_set_lens:= [ 1 ];

        old_deg:= [ oneU ];
        u_mats:= [ mats[1]^0 ];

        ff:= [ ];
        vv:= [ ];

        done:= false;
        while not done do
              deg:= deg+1;

              // add all monomials of degree `deg'...
              new_deg:= {@@};
              for mon in old_deg do
                  dd:= [ Degree( mon, i ) : i in [1..ind1-1] ];
                  for i in [1..ind1-1] do
                      new_mon:= oneU;
                      new_mat:= mats[1]^0;
                      for j in [1..ind1-1] do
                          if i eq j then 
                             new_mon:= new_mon*U.j^( dd[j]+1 );
                          else
                             new_mon:= new_mon*U.j^dd[j];
                          end if;
                      end for;
                      Include( ~new_deg, new_mon );
                  end for; 
              end for;
              old_deg:= IndexedSetToSequence( new_deg );
              d_set cat:= old_deg;
              Append( ~d_set_degs, old_deg );
              Append( ~d_set_lens, #old_deg );

              // Get the matrices of the new elements (in old_deg):
              for mon in old_deg do
                  mat:= mats[1]^0;
                  for i in [1..ind1-1] do
                      mat:= mat*mats[i]^Degree( mon, i );
                  end for;
                  Append( ~u_mats, mat );
              end for;

              // get the coefficient vectors of the coefficient funcs:
              // ff will contain the functions, a function is represented
              // by a triple [* list, i, j *], where list is of the form
              // [ k1, k2, .., kr ]; this represents the function
              // x_k1^(x_k2^...(x_kr^c_{ij})...), where c_{ij} is the
              // ij-th coefficient.
              // vv will contain the corresponding values on the monomials
              // in d_set.
              ff:= [ ];
              vv:= [ ];
              V:= VectorSpace( F, #d_set );
              S:= sub< V | >;
              for i in [1..n] do
                  for j in [1..n] do
                      v:= Vector( F, [ x[i][j] : x in u_mats ] );
                      if not v in S then
                         bS:= [ V | x : x in Basis( S ) ];
                         Append( ~bS, V!v );
                         S:= sub< V | bS >;
                         Append( ~ff, [* [ ], i, j *] );
                         Append( ~vv, v );
                      end if;
                  end for;
              end for; 

              // Let the element L.i for ind1 <=i <= ind2 
              // act on S (spinning algorithm):
              old_vecs:= vv;
              old_ff:= ff;
              while #old_vecs gt 0 do

                    new_vecs:= [ ];
                    new_ff:= [ ];
                    for k in [1..#old_vecs] do
                        w:= old_vecs[k];

                        if #old_ff[k][1] eq 0 then
                           bound:= ind2;
                        else
                           bound:= old_ff[k][1][1];
                        end if;


                        for i in [ind1..bound] do
                            // let L.i act on old_ff[k]...

                            v:= [F| ];

                            for a in d_set do
                                b:= a*U.i - U.i*a;
                                mb:= Monomials( b );
                                cb:= Coefficients( b );
                                val:= zeroF;
                                for i in [1..#mb] do
                                    dm:= TotalDegree(mb[i]);
                                    pp:= Index( d_set_degs[dm+1], mb[i] );
                                    pp:= pp + &+[d_set_lens[q] : q in [1..dm]];
                                    val:= val + cb[i]*w[ pp ];
                                end for;
                                Append( ~v, val );
                            end for;
                            v:= Vector( F, v );
                            if not v in S then
                               bS:= [ V | x : x in Basis( S ) ];
                               Append( ~bS, v );
                               S:= sub< V | bS >;
                               f:= old_ff[ k ];
                               f[1]:= [ i ] cat f[1]; 
                               Append( ~ff, f );
                               Append( ~vv, v );
                               Append( ~new_vecs, v );
                               Append( ~new_ff, f );
                            end if;
                        end for;
                    end for;
                    old_vecs:= new_vecs;
                    old_ff:= new_ff;
              end while;

              // Now S is the extension module, compute matrices:
              S:= VectorSpaceWithBasis( [ V!v : v in vv ] );
              new_mats:= [ ];
              for i in [1..ind1-1] do
                  mat:= [ ];
                  for k in [1..#vv] do
                      w:= vv[k];
                      v:= [ ];
                      for a in d_set do
                          b:= a*U.i;
                          mb:= Monomials( b );
                          cb:= Coefficients( b );
                          val:= zeroF;
                          for j in [1..#mb] do
                              dm:= TotalDegree(mb[j]);
                              if dm le deg then 
                                 pos:= Index( d_set_degs[dm+1], mb[j] );
                                 pos:= pos + &+[d_set_lens[q] : q in [1..dm]];
                              else
                                 pos:= 0;
                              end if;
        
                              if pos gt 0 then
                                 val:= val + cb[j]*w[ pos ];
                              else
                                 // we have to inspect ff[k]...
                                 // We have that ff[k] = y1..ys ^ c_{ij}
                                 // we use that to compute ff[k]( mb[j] ).
                                 f:= ff[k];
                                 exp:= #f[1];
                                 c:= mb[j];
                                 for q in [1..exp] do
                                     c:= c*U.f[1][q]-U.f[1][q]*c;
                                 end for;

                                 // Get the  matrix of c...

                                 mc:= Monomials( c );
                                 cc:= Coefficients( c );

                                 val_1:= zeroF;
                                 for l in [1..#ff] do
                                     if #ff[l][1] eq 0 and 
                                        ff[l][2] eq f[2] and
                                        ff[l][3] eq f[3] then
                                        pos:= l;
                                        break l;
                                     end if;
                                 end for;

                                 for l in [1..#mc] do
                                     dm:= TotalDegree(mc[l]);
                                     if dm le deg then 
                                        pos_1:= Index(d_set_degs[dm+1],mc[l]);
                                        pos_1:= pos_1 + 
                                            &+[d_set_lens[q] : q in [1..dm]];
                                     else
                                        pos_1:= 0;
                                     end if;
                                   
                                     if pos_1 gt 0 then
                                        val_1:= val_1 + cc[l]*vv[pos][pos_1];
                                     else
                                        ej:= Vector( F, [ 0 : r in [1..n] ] );
                                        ej[f[3]]:= oneF;
                                        is_zero:= false;
                                        for r in [ind1-1..1 by -1] do
                                            exp:= Degree( mc[l], r );
                                            for q in [1..exp] do
                                                ej:= ej*trans_mats[r];
                                                is_zero:= IsZero( ej );
                                                if is_zero then
                                                   break q;
                                                end if; 
                                            end for;
                                            if is_zero then
                                               break r;
                                            end if;
                                        end for;
                                        if not is_zero then
                                           val_1:= val_1 + cc[l]*ej[ f[2] ];
                                        end if;
                                     end if; 
                                 end for;       
                                 val:= val + cb[j]*val_1;
                              end if;
                          end for;
                          Append( ~v, val );
                      end for;

                      Append( ~mat, Coordinates( S, V!v ) );
                  end for;
                  Append( ~new_mats, Transpose( Matrix( F, mat ) ) );
              end for;

              // compute the matrices of L.i, for ind1 <= i <= ind2:
              for i in [ind1..ind2] do
                  mat:= [ ];
                  for k in [1..#vv] do
                      w:= vv[k];
                      v:= [ ];
                      for a in d_set do
                          b:= a*U.i-U.i*a;
                          mb:= Monomials( b );
                          cb:= Coefficients( b );
                          val:= zeroF;
                          for j in [1..#mb] do
                              dm:= TotalDegree(mb[j]);
                              pos:= Index( d_set_degs[dm+1], mb[j] );
                              pos:= pos + &+[d_set_lens[q] : q in [1..dm]];
                              val:= val + cb[j]*w[ pos ]; 
                          end for;
                          Append( ~v, val );
                      end for;
                      Append( ~mat, Coordinates( S, V!v ) );
                  end for;
                  Append( ~new_mats, Transpose( Matrix( F, mat ) ) );
              end for;

              // we check whether this is a representation,
              // and whether it is faithful, if not we increase
              // deg and return to the beginning.

              done:= true;
              for i in [1..ind2] do
                  for j in [i+1..ind2] do
                      // a will be the matrix of L.i*L.j
                      cf:= Coordinates( L, L.i*L.j );
                      a:= 0*new_mats[1];
                      for k in [1..ind2] do
                          a := a + cf[k]*new_mats[k];
                      end for;
                      if a ne new_mats[i]*new_mats[j] - new_mats[j]*new_mats[i]
                              then
                         done:= false;
                         break j;
                      end if;
                  end for;
                  if not done then break i; end if;
              end for;

              if done then 
                 // If the `new' elements do not form a Levi
                 // subalgebra, we also check faithfulness...
                 sp:= KMatrixSpace( F, NumberOfColumns( new_mats[1] ),
                                       NumberOfColumns( new_mats[1] ) );
                 sp_1:= sub< sp | [ sp!x : x in new_mats ] >;
                 if Dimension( sp_1 ) lt ind2 then
		    is_faithful:= false;
                    if ind1 eq ind2 then 
                       // i.e., non-Levi case, we have to continue...
                       done:= false;
                    end if;
                 else
                    is_faithful:= true;
                 end if;
              end if;

        end while;
        return new_mats, is_faithful;

     end if;

end function;

// Now we put it together in a function for computing a module.
// Strategy: first compute the `series'; then produce a `nice' basis
// of L (by taking the elements of the `series'). Create a different
// Lie algebra wrt that basis, and a map from the old Lie algebra
// into the new one, make a rep of the new one.

con_rep:= function( L );


     F:= CoefficientRing( L );
     dim:= Dimension( L );

     // first we check whether there is no centre...
     if Dimension( Centre(L) ) eq 0 then
        
        M:= VectorSpace( F, dim );
        rho:= function( x, v )
              return M!( x*L!v );
	end function;
        return Module( L, 
            map< CartesianProduct( L, M ) -> M | t :-> rho( t[1], t[2] ) > );
     end if;

     // if there is a centre we have to do some work...

     if IsNilpotent( L ) then
        levi:= false;
        s:= series_nilp( L );
     elif IsSolvable( L ) then
        levi:= false;
        s:= series_solv( L );
     else
        levi:= HasLeviSubalgebra( L );
        s:= series_gen( L );
     end if;

     b:= s[1];
     for j in [2..#s] do
         b cat:= s[j];
     end for;
     V:= VectorSpace( F, dim );
     W:= VectorSpaceWithBasis( [ V!x : x in b ] ); 
     T:= [ ];
     for i in [1..#b] do
         for j in [i+1..#b] do
             cf:= Coordinates( W, V!( b[i]*b[j] ) );
             for k in [1..#cf] do
                 if not IsZero( cf[k] ) then
                    Append( ~T, <i,j,k, cf[k]> );
                    Append( ~T, <j,i,k,-cf[k]> );
                 end if;
             end for;
         end for; 
     end for;
 
     K:= LieAlgebra< F, dim | T >;
     U:= UniversalEnvelopingAlgebra( K );

     ind:= #s[1];
     mats:= [ ZeroMatrix( F, ind+1, ind+1 ) : x in [1..ind] ];
     for i in [1..ind] do
         mats[i][1][i+1]:= 1;
     end for;
     if not levi then
        while ind lt dim do
              ind:= ind+1;
              mats:= extend_rep( U, K, mats, ind, ind );
        end while;

     else
        dim_levi:= #s[#s];
        while ind lt dim-dim_levi do
              ind:= ind+1;
              mats:= extend_rep( U, K, mats, ind, ind );
        end while;
        mats,faith:= extend_rep( U, K, mats, ind+1, dim );

        if not faith then
	   // we take the direct sum with the adjoint rep...
           n:= NumberOfColumns( mats[1] );
           deg:= n + Dimension( K );
           // put the adjoint matrix of each basis element in the 
           // right bottom corner...
           new_mats:= [ ];
           for i in [1..Dimension(K)] do
               adm:= Matrix( AdjointMatrix( K, K.i ) );
               mat:= ZeroMatrix( F, deg, deg );
               for j in [1..n] do
                   for k in [1..n] do
                       mat[j][k]:= mats[i][j][k];
                   end for;
               end for;

               for j in [1..Dimension(K)] do
                   for k in [1..Dimension(K)] do
                       mat[n+j][n+k]:= adm[j][k];
                   end for;
               end for;

               Append( ~new_mats, mat );
           end for;
           mats:= new_mats;
        end if;

     end if;

     
     return [ Transpose( m ) : m in mats ], W, V;
    

end function;


intrinsic FaithfulModule( L::AlgLie ) -> ModAlg
{A faithful module of the input Lie algebra}


     F:= CoefficientRing( L );
     dim:= Dimension( L );

     // first we check whether there is no centre...
     if Dimension( Centre(L) ) eq 0 then
            
        M:= RModule( F, dim );
        rho:= function( x, v )
              return M!Eltseq( ( x*L!Eltseq(v) ) );
	end function;
        return Module( L, 
            map< CartesianProduct( L, M ) -> M | t :-> rho( t[1], t[2] ) > );
     end if;

     if not IsSolvable( L ) then
        levi:= HasLeviSubalgebra( L );
     else
        levi:= true;
     end if;
        
     require levi : "The input Lie algebra is not solvable and does not have a Levi subalgebra; therefore FaithfulModule does not work for it.";

     // if there is a centre then conrep will do the work...
     mats, W, V:= con_rep( L );
     M:= RModule( F, NumberOfRows( mats[1] ) );

     rho:= function( x, v )  

           cf:= Coordinates( W, V!x );
           vv:= cf[1]*(v*mats[1]);
           for k in [2..#cf] do
               if not IsZero( cf[k] ) then
                  vv:= vv + cf[k]*(v*mats[k]);
               end if;
           end for;
           return M!( Eltseq(vv) );
     end function; 

     return Module( L, 
            map< CartesianProduct( L, M ) -> M | t :-> rho( t[1], t[2] ) > );


end intrinsic;


intrinsic IsomorphicMatrixLieAlgebra( L::AlgLie ) -> AlgMatLie
{A matrix Lie algebra that is isomorphic to the input Lie algebra}

     if Type( L ) eq AlgMatLie then
        return L, map< L -> L | x :-> x >;
     end if;

     F:= CoefficientRing( L );
     dim:= Dimension( L );

     // first we check whether there is no centre...
     if Dimension( Centre(L) ) eq 0 then
        adm:= [ AdjointMatrix( L, L.i ) : i in [1..dim] ];    
        M:= MatrixLieAlgebra( F, dim );
        Q:= [ M!u : u in adm ];
        K:= sub< M | Q >;

        f:= function( x )

            cf:= Coordinates( L, x );
            r:= 0*Q[1];
            for i in [1..#cf] do
                if not IsZero( cf[i] ) then
                   r:= r + cf[i]*Q[i];
                end if;      
            end for;
            return r;
        end function;
        return K, map< L -> K | x :-> f(x) >;
     end if;

     if not IsSolvable( L ) then
        levi:= HasLeviSubalgebra( L );
     else
        levi:= true;
     end if;
        
     require levi : "The input Lie algebra is not solvable and does not have a Levi subalgebra; therefore IsomorphicMatrixLieAlgebra does not work for it.";

     // If there is a centre, then we let conrep do the work...

     mats, W, V:= con_rep( L );
     mats:= [ Transpose( m ) : m in mats ];
     adm:= [ ];
     for i in [1..dim] do
         cf:= Coordinates( W, V!L.i );
         m:= 0*mats[1];
         for k in [1..#cf] do
             if not IsZero( cf[k] ) then
                m:= m + cf[k]*mats[k];
             end if;
         end for;
         Append( ~adm, m );
     end for; 

     M:= MatrixLieAlgebra( F, NumberOfColumns( mats[1] ) );
     Q:= [ M!u : u in adm ];
     K:= sub< M | Q >;

     f:= function( x )

         cf:= Coordinates( L, x );
         r:= 0*Q[1];
         for i in [1..#cf] do
             if not IsZero( cf[i] ) then
                r:= r + cf[i]*Q[i];
             end if;      
         end for;
         return r;
     end function;
     return K, map< L -> K | x :-> f(x) >;

end intrinsic;
