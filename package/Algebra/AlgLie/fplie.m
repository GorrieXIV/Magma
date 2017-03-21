freeze;

///////////////////////////////////////////////////////////////////////////

make_basis:= procedure( ~BB )

    // produce a basis of the subspace of the free Lie ring spanned by BB

   if #BB gt 0 then

      mns:= {};
      for b in BB do
         mns join:= Seqset( Monomials(b) );
      end for;

      mns:=SetToSequence( mns );
      Sort( ~mns ); 

      n:= #mns;

      mat:= SparseMatrix( #BB, #mns );
      for j in [1..#BB] do
          mb:= Monomials(BB[j]); cb:= Coefficients(BB[j]);
          for i in [1..#mb] do
              mat[j][ n-Index( mns, mb[i] )+1 ]:= cb[i];
          end for;
         
      end for;

      Echelonize( ~mat );

      Reverse( ~mns );
      bas:= [ ];
      for i in [1..NumberOfRows( mat )] do
          b:= 0*BB[1];
          s:= Support( mat, i );
          for j in s do
              b +:= mat[i][j]*mns[j];
          end for;
          Append( ~bas, b );
      end for;
       
      //return bas;
 
      BB:= bas;

   end if;

end procedure;


FpLieRingHOM:= function( A, R, bound )

    // compute A/I, where I is the ideal gen by R along with Jacobi's

    // We take the reverse list of generators, to have the 
    // smallest one first.
    g:= Reverse( [ A.i : i in [1..Rank(A)] ] );
 
    B:= [ ];
    Bd:= [ ];

    NB:= [ ];   // basis in "normal form" i.e., displaying torsion etc.
    Tors:= [ ]; // the torsion corresponding to the elements of NB

    G:= [ ];
    BB:= [ ];    // G, BB will be the reduction pair...
    Gd:= [ ];   // same as G but then split up in equal degree parts.

    Qs:= [* *]; 
    //the Q-matrices for each degree (coming out of the Smith form).

    deg:= 1;

    is_nilquot:= bound lt Infinity();

    while deg le bound do

       rels:= [ ];
       for r in R do 
           if Degree(r) eq deg then
              f:= NormalForm( r, G );
              if f ne 0 then 
                 Append( ~rels, f ); 
              end if;
           end if;
       end for;

       //split into monic/nonmonic
       BBdeg:=  [ ];
       Gdeg:= [ ];
      
       if deg ge 3 then

           len:= #rels;

           for i in [1..#Bd[1]] do
               m1:= Bd[1][i];
               for u in [1..#Bd] do
                   v:= deg-1-u;
                   if v gt 0 and v le #Bd then
                      for j in [1..#Bd[u]] do
                          m2:= Bd[u][j];
                          for k in [1..#Bd[v] ] do
                              m3:= Bd[v][k];
                              if  m1 lt m2 and m2 lt m3 then
                                  
                                  f1:= NormalForm( m2*m3, Gd[u+v] );
                                  f2:= NormalForm( m1*m2, Gd[1+u] );
                                  f3:= NormalForm( m3*m1, Gd[1+v] );
                                  f:= m1*f1+m3*f2+m2*f3;
                                  Append( ~rels, f );

                              end if;
                                      
                          end for;
                      end for;
                   end if;
               end for;
           end for; 

       end if;

       // now add elements of the form (x,b) where x is a generator,
       // and b an element of BB of degree deg-1.

     
       for f in BB do
           if Degree(f) eq deg-1 then
              for x in Bd[1] do     
                  h:= NormalForm( x*f, Gdeg );      
                  if not IsZero(h) then
                     Append( ~rels, h );
                  end if;
              end for;
           end if;
       end for;

       make_basis( ~rels );

       for f in rels do 

           if not IsZero(f) then 
              c:= Coefficients(f)[1]; 
              if c eq -1 then
                 f0:= -f;
                 c:= 1;
              else
                 f0:= f;
              end if;
              if c eq 1 then
                 Append( ~Gdeg, f0 );
              else
                 Append( ~BBdeg, f0 ); 
              end if;
                                    
           end if;

      end for;

       Append( ~Gd, Gdeg );
       G cat:= Gdeg;

       // make the normal monomials of degree deg:

       if deg eq 1 then
          newB:= g;
          i:= 1;
          while i le #newB do
             f:= NormalForm( newB[i], G );
             if f ne newB[i] then 
                Remove( ~newB, i );
             else
                i:= i+1;
             end if;
          end while;
       else
          newB:= [ ];
          lms:= [ Monomials(u)[1] : u in Gdeg ];
          for x in Bd[1] do
              for m in Bd[deg-1] do
                  if x lt m then
                     m1:= x*m;
                     if not m1 in lms then 
                        Append( ~newB, m1 );
                     end if;
                  end if;
              end for;
          end for;
       end if;

       // Note that newB is sorted small to big 
       // (follows from the above piece of code). 

       if #BBdeg gt 0 then

          mat:= ZeroMatrix( Integers(), #BBdeg, #newB );
          for j in [1..#BBdeg] do
              mb:= Monomials(BBdeg[j]); cb:= Coefficients(BBdeg[j]);
              for i in [1..#mb] do
                  mat[j][ Index( newB, mb[i] ) ]:= cb[i];
              end for;
          end for;

          S,P,Q:= SmithForm( mat );
          Append( ~Qs, Q );
          Qi:= Q^-1;
      
          bas:= [ ];
          tor:= [ ];
          nocol:= NumberOfColumns( mat );
          for k in [1..nocol] do
              cc:= Qi[k];
              b:= Zero(A);
              for i in [1..nocol] do
                  if cc[i] ne 0 then
                     b +:= cc[i]*newB[i];
                  end if;
              end for;
              Append( ~bas, b );
              if k le NumberOfRows( S ) then
                 Append( ~tor, S[k][k] );
              else
                 Append( ~tor, 0 );
              end if;
          end for;      

          Append( ~NB, bas );
          Append( ~Tors, tor ); 
       else
          Append( ~NB, newB );
          Append( ~Tors, [ 0 : i in [1..#newB] ] );
          Append( ~Qs, ZeroMatrix( Integers(), 0, 0 ) );
       end if;

       BB cat:= BBdeg;

       Append( ~Bd, newB );

       if #newB eq 0 and bound gt 2*deg-1 then
          bound:= 2*deg-1;
          bound:= Maximum(bound,Maximum( [ Degree(u) : u in R ] ) );
       end if;
       deg:= deg+1;      

    end while;

    bas:= [ ];
    tors:= [ ];
    basinds:= [ ]; 
// a list of lists, e.g., if the k-th element is [0,0,6,7,8], then
// the "normal basis" has 5 elements of degree k, the first two 
// with torsion 1, the last three with positions 6, 7, 8 in the final basis.
// The first two willl then not be part of the final basis.

    grading:= [ ];


    k:= 1;
    for i in [1..#NB] do
        Append( ~basinds, [ ] );
        grad:= 0;
        for j in [1..#NB[i]] do
            if Tors[i][j] ne 1 then
                Append( ~bas, NB[i][j] );
                Append( ~tors, Tors[i][j] );
                Append( ~basinds[i], k ); k:= k+1;
                grad +:= 1;
             else
                Append( ~basinds[i], 0 );
             end if;
         end for;
         Append( ~grading, grad );
     end for;

     T:= [ ]; // mult table; contains the quadruples...
     for i in [1..#bas] do
         for j in [i+1..#bas] do
             deg:= Degree(bas[i]) + Degree( bas[j] );
             if not( is_nilquot and deg gt  bound ) then

                b:= NormalForm( bas[i]*bas[j], Gd[deg] );
                if not IsZero(b) then

                   entry:= [ ];
                   if NumberOfColumns(Qs[deg]) eq 0  then
                      mb:= Monomials( b ); cb:= Coefficients( b );
                      for k in [1..#mb] do
                          Append( ~T, <i,j, 
                            basinds[deg][Index( Bd[deg], mb[k] )],cb[k]>);
                          Append( ~T, <j,i, 
                            basinds[deg][Index( Bd[deg], mb[k] )],-cb[k]>);
                      end for;
                   else
                      mb:= Monomials(b); cb:= Coefficients(b);
                      cc:= [ 0 : i in [1..#Bd[deg]] ];
                      for k in [1..#mb] do
                          cc[ Index( Bd[deg], mb[k] ) ]:= cb[k];
                      end for;

                      cc:= Vector(cc)*Qs[deg];
  
// this is now the list of coefficients of b wrt normbas...
// in order to get normal form we "divide" by the torsion...

                      cc:= Eltseq( cc );
                      for k in [1..#cc] do 
                          if Tors[deg][k] ne 0 then
                             cc[k]:= cc[k] mod Tors[deg][k]; 
                          end if;
                      end for;
                      for k in [1..#cc] do
                          if cc[k] ne 0 then
                             Append( ~T, <i,j,basinds[deg][k],cc[k]> );
                             if Tors[deg][k] eq 0 then
                                Append( ~T, <j,i,basinds[deg][k],-cc[k]> );
                             else
                                Append( ~T, <j,i,basinds[deg][k],
                                                -cc[k] mod Tors[deg][k]> );
                             end if;
                          end if;
                      end for;
                   end if;
                   
                end if;
             end if;
         end for;
     end for;

     K:= LieAlgebra< tors | T : Check:= false >;

     phi := function( u )

         // Here u is an element of K, we map it to an element of 
         // the free algebra

         uu:= Eltseq( u );
         v:= Zero(A);
         for i in [1..#uu] do
             v +:= uu[i]*bas[i];
         end for;
         return v;

     end function;
         

     return K, grading, map< K -> A | x :-> phi(x) >;

end function;


normal_form:= function( f, G, dd )

    // special normal form: all monomials of degree > dd are zero as well.

    h:= NormalForm( f, G ); 
    if Degree(h) gt dd then
       mns:= Monomials(h);
       cfs:= Coefficients( h );
       h0:= 0*h;
       for i in [1..#mns] do
           if Degree( mns[i] ) le dd then
              h0 +:= cfs[i]*mns[i];
           end if;
       end for;
       h:= h0;
    end if;

    return h;

end function;

get_rid_of_hdeg:= function( f, dd )

    // all monomials of degree > dd are zero.

    if Degree(f) gt dd then
       mns:= Monomials(f);
       cfs:= Coefficients( f );
       h0:= 0*f;
       for i in [1..#mns] do
           if Degree( mns[i] ) le dd then
              h0 +:= cfs[i]*mns[i];
           end if;
       end for;
       return h0;
    end if;

    return f;

end function;


add_elm_to_G:= function( G, f, deg, nq )

   // Here G is a GB (i.e self reduced, monic). f is a monic element,
   // assumed reduced wrt G.
   // We add f to G. Maybe some elements of G reduce modulo f, so
   // we have to take them from G, reduce them modulo f, and if they
   // remain monic, to add them to G. Otherwise they are added to a list
   // of nonmonic elements that will be returned as well.

   // nq is the nilpotent quotient bound; can be Infinity. 

   U:= [ f ];
   V:= [ ];
   ldeg:= false;
   while #U gt 0 do
      newelms:= [ ];
      i:= 1;
      while i le #G do
          g:= G[i];
          m:= LeadingMonomial(g);
          g:= NormalForm( g, U );
          if not IsZero(g) then
             if LeadingMonomial(g) eq m and LeadingCoefficient(g) eq 1 then
                // leave it in G
                G[i]:= g;
                i +:= 1;
             else
                Append( ~newelms, g );
                Remove( ~G, i );
             end if;
          else
             Remove( ~G, i );
          end if;
      end while;
      G cat:= U;
      if &or[ Degree(v) lt deg : v in U ] then
         ldeg:= true;
      end if;
           
      U:= [ ];
      for g in newelms do
          c:= LeadingCoefficient(g);
          h:= g;
          if c eq -1 then h:= -h; c:= 1; end if;
          if c eq 1 then
             Append( ~U, h );
          else
             Append( ~V, h );
          end if;
      end for;
      if #U gt 0 then
         U:= Reduce( U );
      end if;
      for i in [1..#U] do
          U[i]:= normal_form( U[i], G, nq );
      end for;
      // this may have resulted in non monic elements again...
      i:= 1;
      while i le #U do
         c:= LeadingCoefficient(U[i]);
         if c ne 1 then
            Append( ~V, U[i] );
            Remove( ~U, i );
         else
            i:= i+1;
         end if;
      end while;

   end while;

   return G, V, ldeg;

end function;

Bdatum:= recformat< B, mons, mtrx : SeqEnum, V,W : ModED >;

extended_make_basis:= function( BB )

      // Here BB is a set of elements of the free algebra;
      // we make the Bdatum for the subspace spanned by it.

      if #BB eq 0 then 
         V:= RModule( Integers(), 0 );
         return rec< Bdatum | B:= [], mons:= [], mtrx:= [ ], V:=V, W:= V >;
      end if;

      mns:= [ ];
      for b in BB do
          mb:= Monomials(b);
          for m in mb do
              if not m in mns then Append( ~mns, m ); end if;
          end for;
      end for;

      Sort( ~mns );
      Reverse( ~mns );
      mat:= SparseMatrix( Integers(), #BB, #mns );
      for i in [1..#BB] do
          mb:= Monomials( BB[i] );
          cb:= Coefficients( BB[i] );
          for j in [1..#mb] do
              mat[i][ Index( mns, mb[j] ) ]:= cb[j];
          end for;
      end for;

      Echelonize( ~mat );

      V:= RModule( Integers(), #mns );
      W:= sub< V | [ V!mat[i] : i in [1..NumberOfRows(mat)]]>;

      bas:= [ ];
      zero:= 0*BB[1]; 
      mt:= [ ];
      for i in [1..NumberOfRows(mat)] do
          s:= Support( mat, i );
          b:= zero; 
          for j in s do
              b +:= mat[i][j]*mns[j];
              Append( ~mt, <i,j,mat[i][j]> );
          end for;
          Append( ~bas, b );
      end for;      
 
      return rec< Bdatum | B:= bas, mons:= mns, mtrx:= mt, 
                   V:= V, 
                   W:= W >;


end function;


is_contained:= function( Bdat, f )

    // Here Bdat is a Bdatum. We produce a new Bdatum,
    // of which the span is equal to the old one plus f.

    if IsZero(f) then return true,Bdat; end if;

    v:= Vector( Integers(), [ 0 : i in [1..#Bdat`mons] ] );
    mf:= Monomials( f );
    cf:= Coefficients( f );
    for k in [1..#mf] do
        pos:= Index( Bdat`mons, mf[k] );
        if pos eq 0 then
           BB:= Bdat`B; 
           Append( ~BB, f );
           return false, extended_make_basis( BB );
        else
           v[pos]:= cf[k];
        end if;
    end for;

    // see whether v is in Bdat`W:
    iscontained:= (Bdat`V)!v in Bdat`W;
     
    if not iscontained then


       V:= Bdat`V;
       n:= Dimension(Bdat`W);
       mns:= Bdat`mons;
       mat:= SparseMatrix( n+1, #mns, Bdat`mtrx );
       for j in [1..#mns] do
           mat[n+1][j]:= v[j];
       end for;
 
       Echelonize( ~mat );
 
       W:= sub< V | [ V!mat[i] : i in [1..NumberOfRows(mat)]]>;

       bas:= [ ];
       zero:= 0*(Bdat`B)[1]; 
       mt:= [ ];
       for i in [1..NumberOfRows(mat)] do
           s:= Support( mat, i );
           b:= zero; 
           for j in s do
               b +:= mat[i][j]*mns[j];
               Append( ~mt, <i,j,mat[i][j]> );
           end for;
           Append( ~bas, b );
       end for;      
 
       return false,rec< Bdatum | B:= bas, mons:= mns, mtrx:= mt, 
                   V:= V, 
                   W:= W >;


    else
       return true, Bdat;
    end if;

end function;


is_contained_0:= function( Bdat, f )

    // Same as is_contained, except that the answer is just yes/no
    // and the basis is not extended.

    if IsZero(f) then return true; end if;

    v:= Vector( Integers(), [ 0 : i in [1..#Bdat`mons] ] );
    mf:= Monomials( f );
    cf:= Coefficients( f );
    for k in [1..#mf] do
        pos:= Index( Bdat`mons, mf[k] );
        if pos eq 0 then
           return false;
        else
           v[pos]:= cf[k];
        end if;
    end for;

    return (Bdat`V)!v in Bdat`W;

end function;


add_elm_to_B:= procedure( ~B, G, f, gens, dg, nq )

   // Here B is a Bdatum.
   // f is a (presumably) non-monic element; we add it
   // to B, and make a new basis. If in the course of this operation
   // a new element of degree < dg appears then we add all products
   // of that element with generators, in order to reach id-closedness 
   // of degree dg in the end.   
   // We will not change G. 
   // The method runs as follows:
   //
   //    1. We add the element, obtaining a new basis B0.
   //    2. If there are elements h in B0 with the property that 
   //       they are not contained in the span of B, and deg(h) < dg,
   //       then we add all (x,h) for generators x (in gens). We
   //       obtain yet another new basis, B1.
   //    3. If B1 was made, then B:= B0; B0:= B1; and back to 2.
   //       Otherwise we are done.

   // nq is the nilpotent quotient parameter.

   is_c,B0:= is_contained( B, f );

   if not is_c then
      B1:= B0; 
      made_basis:= false;
      while not made_basis do
          made_basis:= true;
          for h in B0`B do
              is_c:= is_contained_0( B, h );
              if not is_c then

                 if Degree(h) lt dg then
                    for x in gens do
                        hh:= normal_form( x*h, G, nq );
                        is_c,B1:= is_contained( B1, hh );
                        if not is_c then
                           made_basis:= false;
                        end if;
                    end for;
                 end if;
              end if;
          end for;
          B:= B0; 
          B0:= B1; 
      end while;
   end if;

   //return B;

end procedure;

is_hom_elm:= function( f )

   mns:= Monomials(f);
   return Degree(mns[1]) eq Degree(mns[#mns]);
   
end function;


FpLieRingNH:= function( A, R, bound )

     // compute A/I, where I is the ideal gen by R along with Jacobi's
     // NONhomogeneous case

     // We take the reverse list of generators, to have the 
     // smallest one first.
     gens:= Reverse( [ A.i : i in [1..Rank(A)] ] );
 
     B:= [ ];
     Bd:= [ ];

     NB:= [ ];   // basis in "normal form" i.e., displaying torsion etc.
     Tors:= [ ]; // the torsion corresponding to the elements of NB

     G:= [ ];
     lms:= [ ];    // The leading monomials of G...
     BB:= extended_make_basis( [] );    // G, BB will be the reduction pair...

     deg:= 1;

     is_nilquot:= true;
     if bound eq Infinity() then 
        is_nilquot:= false; 
        nilquot:= bound;
     else
        nilquot:= bound;        
        bound:= 2*bound;
     end if;

     maxdeg:= nilquot;
     set_bound:= false;
     added_mons:= false;

     while deg le bound do

     //First we make a potentially large set of new relations.
     
       if is_nilquot then
          newrls:= [ ];
          for r in R do
              if Degree(r) eq deg-1 and not is_hom_elm(r) then
                 for x in gens do
                     f:= x*r;
                     mns:= Monomials(f);
                     if Degree( mns[#mns] ) le nilquot then
                        Append( ~newrls, x*r );
                     end if;
                 end for;
              end if;
          end for; 
          R cat:= newrls;
       end if;
       
       rels:= [];
       for r in R do
           if Degree(r) eq deg then
              f:= get_rid_of_hdeg( r, nilquot );
              f:= normal_form( f, G, nilquot );
              if not IsZero(f) then
                 Append( ~rels, f );
              end if;
           end if;
       end for;

       if deg ge 3 then

              lms:= [ LeadingMonomial(g) : g in G ];

              for i in [1..#Bd[1]] do
                  m1:= Bd[1][i];
                  for u in [1..#Bd] do
                      v:= deg-1-u;
                      if v gt 0 and v le #Bd then
                         for j in [1..#Bd[u]] do
                             m2:= Bd[u][j];
                             for k in [1..#Bd[v]] do
                                 m3:= Bd[v][k];
                                 if m1 lt m2 and m2 lt m3 then

                                    f:= m1*(m2*m3)+m3*(m1*m2)+
                                                    m2*(m3*m1);

                                    if not IsZero(f) then
                                       Append( ~rels, f );
                                    end if;
 
                                 end if;
                                      
                             end for;
                         end for;
                      end if;
                  end for;
              end for;
       end if;
       
       if is_nilquot and deg ge nilquot+1 then
          // add all monomials of degree deg.
          
          for i in [1..#Bd] do
              j:= deg-i;
              if j ge i and j le #Bd then
                 for u in Bd[i] do
                     for v in Bd[j] do
                         Append( ~rels, u*v );
                     end for;
                 end for;
              end if;
          end for;
          
       end if;
 

       // Now we have to do the following things:
       //
       //   * For all elements b\in B of degree deg-1, add (x,b) to the new 
       //    relations, where x is a generator.
       //
       //   * If the degree of an element is equal to deg, then the element
       //     can only reduce modulo the other elements of the same degree, 
       //     by a linalg type reduction. We perform this reduction, and put 
       //     the element in G if it is monic, in BB if it is not. 
       //
       //   * If the degree of the element is lower than deg (or the degree 
       //     of the element from the previous step is such), and it is monic, 
       //     then we put it in G, but have maybe to reduce existing elements 
       //     modulo the new element. We remove the elements of G that have 
       //     leading monomial divisible by the new one, from G, and append 
       //     them to the list of new relations (after reduction mod new 
       //     element).
       //
       //   * If the degree of the element is lower than deg, and it is not 
       //     monic, then we add it to BB, and add all relations that we get 
       //     by multiplying by generators, until degree deg. 

       for f in BB`B do
           if Degree(f) eq deg-1 then
              for x in gens do     
                  Append( ~rels, x*f );
              end for;
           end if;
       end for;

       V:= [ ]; // elements to be added to BB
       lowdeg:= false;
       for f in rels do

           h:= normal_form( f, G, nilquot );
           if not IsZero(h) then
              c:= LeadingCoefficient(h);
              if c eq -1 then
                 h:= -h;
                 c:= 1;
              end if;
              if c eq 1 then
                 G,V1,lwdeg:= add_elm_to_G( G, h, deg, nilquot );
                 V cat:= V1;
                 if lwdeg then lowdeg:= lwdeg; end if;
              else
                 Append( ~V, h );
              end if;
           end if;
       end for;

       // We have to reduce the elements of BB modulo G, but only in case
       // some lower deg element was added.

       if lowdeg then

          changed:= false;
          i:= 1;
          B0:= BB`B;
          while i le #B0 do
              f:= normal_form( B0[i], G, nilquot );
              if B0[i] ne f then
                 changed:= true;
                 Remove( ~B0, i );
                 if not IsZero(f) then
                    Append( ~V, f );
                 end if;
              else
                 i:= i+1;
              end if;
          end while;
          if changed then    
              BB:= extended_make_basis( B0 );
          end if;
       end if;

       for h in V do
           add_elm_to_B( ~BB, G, normal_form(h,G,nilquot), gens, deg, nilquot );
       end for;

       // move monic elements to G... (as long as there are monic elements
       // in BB).
       monics_in_B:= true;
       B0:= BB`B;
       
       while monics_in_B do
          monics_in_B:= false;
          V:= [ ];
          i:= 1;
          while i le #B0 do
              f:= B0[i];
              c:= LeadingCoefficient(f);
              if c eq -1 then  f:= -f; c:= 1; end if;
              if c eq 1 then
                 monics_in_B:= true;
                 G, V1:= add_elm_to_G( G, f, deg, nilquot );
                 V cat:= V1;
                 Remove( ~B0, i );
              else
                 i:= i+1;
              end if;
          end while;
          if monics_in_B then
             BB:= extended_make_basis( B0 ); 
          end if;
          // now we add the elements in V to BB, keeping it ideally closed...
          for f in V do
              add_elm_to_B( ~BB, G, normal_form(f,G,nilquot), gens, deg, nilquot );
          end for;

       end while;

       newB:= [ ];
       lms:= [ LeadingMonomial(f) : f in G ];

       // in NONHOM case might also have to throw away old basis elements.

       for i in [1..#Bd] do
           j:= 1;
           while j le #Bd[i] do
              if IsZero( NormalForm( Bd[i][j], lms ) ) then
                 Remove( ~Bd[i], j );
              else
                 j:= j+1;
              end if;
           end while;

       end for;

       if deg le maxdeg then
          if deg eq 1 then
             newB:= gens;
             i:= 1;
             while i le #newB do
                 if newB[i] in lms then
                    Remove( ~newB, i );
                 else
                    i:= i+1;
                 end if;
             end while;
             gens:= newB;
          elif deg gt nilquot then
               newB:= [ ];
          else
             newB:= [ ];
             for i in [1..#Bd[1]] do
                 for k in [1..#Bd[deg-1]] do
                     if Bd[1][i] lt Bd[deg-1][k] then
                        m:= Bd[1][i]*Bd[deg-1][k];
                        if not m in lms then 
                           Append( ~newB, m );
                        end if;
                     end if;
                 end for;
             end for;
          end if;
       end if;

       if #newB eq 0 and not set_bound then
          bound:= 2*deg-1;
          if #R gt 0 then
             bound:= Maximum(bound,Maximum( [Degree(u) : u in R ]));
          end if;
          if is_nilquot then
             bound:= Maximum( nilquot, bound );
          end if;
          maxdeg:= deg-1;
          set_bound:= true;
       elif #newB gt 0 then
          Append( ~Bd, newB );
       end if;
       deg:= deg+1;      

     end while;

     //End of main loop.

     newB:= [ ];
     for b in Bd do newB cat:= b; end for;
     
     Sort( ~newB );
   
     B0:= BB`B;
     mat:= ZeroMatrix( Integers(), #B0, #newB );
     for i in [1..#B0] do
        
         mb:= Monomials( B0[i] );
         cb:= Coefficients( B0[i] );
         for j in [1..#mb] do
             mat[i][ Index( newB, mb[j] ) ]:= cb[j]; 
         end for;
     end for;

     mat,P,Q:= SmithForm( mat );
     Qi:= Q^-1;
   
      
     bas:= [ ];
     tor:= [ ];
  
     for k in [1..#newB] do
         cc:= Qi[k];
         b:= Zero(A);
         for i in [1..#newB] do
             if cc[i] ne 0 then
                b +:= cc[i]*newB[i];
             end if;
         end for;
         Append( ~bas, b );
         if k le NumberOfRows(mat) then
            Append( ~tor, mat[k][k] );
         else
            Append( ~tor, 0 );
         end if;
     end for;      


     tors:= [ ];
     // torsion of basis elements with torsion not 1...

     k:= 1;
     r:= 0;
     for i in [1..#tor] do
         if tor[i] ne 1 then
            if r eq 0 then r:= i; end if;
            Append( ~tors, tor[i] );
            k:= k+1;
         end if;
     end for;

     //the first basis element which is not zero is on pos r, we
     //begin counting from there.

     bas:= [ bas[i] : i in [r..#bas] ];
     T:= [ ]; //SC table, contains quadruples.

     for i in [1..#bas] do
         for j in [i+1..#bas] do

             if is_nilquot then
                b:= get_rid_of_hdeg( bas[i]*bas[j], nilquot );
                b:= NormalForm( b, G );
             else
                b:= NormalForm( bas[i]*bas[j], G ); 
             end if;

                if not IsZero(b) then
                  
                   v:= Vector( Integers(), [ 0 : k in [1..#newB] ] );
                   mb:= Monomials(b);
                   cb:= Coefficients( b );
                   for k in [1..#cb] do
                       pos:= Index( newB, mb[k] );
                       v[pos]:= cb[k];
                   end for;
                
                   cc:= v*Q;     
        // so now cc is the list of coefficients wrt the "normal" basis.

                   for k in [r..#tor] do
                       if cc[k] ne 0 then
                          if tor[k] ne 0 then
                             Append( ~T, <i,j,k-r+1,cc[k] mod tor[k]> );
                             Append( ~T, <j,i,k-r+1,-cc[k] mod tor[k] > );
                          else
                             Append( ~T, <i,j,k-r+1,cc[k]> );
                             Append( ~T, <j,i,k-r+1,-cc[k]> );
                          end if;
                       end if;
                   end for;
             
                end if;
             
         end for;
     end for;

     K:= LieAlgebra< tors | T : Check:= false >;

     phi := function( u )

         // Here u is an element of K, we map it to an element of 
         // the free algebra

         uu:= Eltseq( u );
         v:= Zero(A);
         for i in [1..#uu] do
             v +:= uu[i]*bas[i];
         end for;
         return v;

     end function;

     return K,map<K -> A | x :-> phi(x)>;

end function;




intrinsic NilpotentQuotient(R::Setq[AlgFPLieElt], d::.)
    -> AlgLie, SeqEnum, SeqEnum, Map
{Return a structure constant Lie algebra which is isomorphic to the
nilpotent quotient of class d of the free Lie algebra modulo the
relations in R.}

    // R: relations
    // If NilQuot is an integer, then we only loop until that degree,
    // i.e., we do a nilpotent quotient. 

    require not IsNull(R): "Illegal null sequence";
    require d cmpeq Infinity() or Type(d) eq RngIntElt and d ge 0:
	"Argument 2 must be a positive integer or Infinity()";

    NilQuot := d;
    FpL := Universe(R);

    require IsField(BaseRing(FpL)) or BaseRing(FpL) eq Integers():
	"Currently FP Lie algebras are only defined over fields and over the ring of integers";

    R := [r: r in R];

    // We take the reverse list of generators, to have the 
    // smallest one first.
    gen:= Reverse( [ FpL.i : i in [1..Rank(FpL)] ] );

    // Check whether the relations are homogeneous.
    IS_HOM:= true;
    for g in R do
        d:= [ Degree(y) : y in Monomials( g ) ];
        if #Set( d ) gt 1 then
           IS_HOM:= false;
           break;
        end if;
    end for;

    // if the base ring is the integers, then we call one of the functions
    // above

    if BaseRing(FpL) cmpeq Integers() then
       if IS_HOM then
          K,gg,fc:= FpLieRingHOM( FpL, R, NilQuot );
          return K, gg, [], fc;
       else
          K,fc:= FpLieRingNH( FpL, R, NilQuot );
          return K, [], [], fc;
       end if;
    end if;


    // If we do a nilpotent quotient, then we only enumerate until 
    // degree NilQuot. Otherwise we determine the correct bound later.

    if NilQuot lt Infinity() and not IS_HOM then
       nilq_nothom:= true;
       bound:= 2*NilQuot;

       // we reduce the relations so that their degrees will be <= bound.
       newRels:= [ ];
       for r in R do
           mns:= Monomials( r );
           cfs:= Coefficients( r );
           rel:= Zero( FpL );
           for i in [1..#mns] do
               if Degree( mns[i] ) le NilQuot then
                  rel:= rel + cfs[i]*mns[i];
               end if;
           end for;
           Append( ~newRels, rel );
          
       end for;
       R:= newRels;

    else
       nilq_nothom:= false;
       bound:= NilQuot;
    end if;

    // Get relations of degree 1 (if any):
    G:= [ ];
    for r in R do
        if Degree(r) eq 1 then
           Append( ~G, r );
        end if;
    end for;

    if #G gt 0 then
       G:= Reduce( G );
       GD:= [ G ];
       LMS:= [ { Monomials(g)[1] : g in G } ];
       B:= [ FpL | ];
       for g in gen do
           if not g in LMS[1] then
              Append( ~B, g );
           end if;
       end for;
    else
       B:= gen;  // basis to be    
       G:= [ ]; // The Groebner basis to be.
       GD:= [ ]; // The Groebner basis to be, by degrees.
       LMS:= [ {@FpL| @} ]; //leading monomials
    end if;

    newBasElt:= true;

    degs:= [ Degree( x ) : x in B ];  // a list for stroring the degree of
                                      // each basis element.
    l:= 1;

    while l lt bound do

       l:= l+1;    
       newRels:= [ ];

       // find all relations of degree l...
       for i in [1..#R] do
           if Degree( R[i] ) eq l then
              g:= NormalForm( R[i], G );
              if g ne 0 then Append( ~newRels, g ); end if;
           end if;
       end for;

       // if we are in the nilpotent quotient, non-hom case, and l
       // is bigger than NilQuot, then we have to add the commutators
       // of basis elements of degree l as relations..
       if nilq_nothom and l gt NilQuot then
          for i in [1..#B] do
              for j in [i+1..#B] do
                  dm:= degs[i]+degs[j];
                  if dm eq l then
                     g:= NormalForm( B[i]*B[j], G );
                     if g ne 0 then Append( ~newRels, g ); end if;
                  end if;
              end for;
          end for;
       end if;

       if #newRels gt 0 then
          newRels:= Reduce( newRels );
       end if;

       // Jacobi identities (only Jac(x,a,b) where x is a generator).

       newRels := InternalJacRelations(l, B, GD, G, newRels, IS_HOM);

       for i in [1..#newRels] do
           c:= Coefficients( newRels[i] )[1];
           newRels[i]:= newRels[i]/c;
       end for;

       // Now we add the new relations. We only do a reduce if a
       // relation of lower degree was found.
       lowDeg:= false;
       newLMS:= {@FpL| @};
       for g in newRels do
           if Degree(g) lt l then
              lowDeg:= true;
           end if;
           Append( ~G, g );

	   dg := Degree(g);
	   for d := #GD to dg do
	      Append(~GD, [FpL|]);
	   end for;
	   Append(~GD[dg], g);

           Include( ~newLMS, Monomials(g)[1] );
       end for;
       if lowDeg then
          if #G gt 0 then

             G:= Reduce( G );
             Sort( ~G );

	     GD := [];
	     for g in G do
	       dg := Degree(g);
	       for d := #GD to dg do
		  Append(~GD, [FpL|]);
	       end for;
	       Append(~GD[dg], g);
	     end for;

             LMS:= [ ];
             for g in G do
                 dg:= Degree( g );
                 if not IsDefined( LMS, dg ) then
                    LMS[dg]:= {@FpL| @};
                 end if;
                 Include( ~LMS[dg], Monomials(g)[1] );
             end for;
             for i in [1..#LMS] do
                 if not IsDefined( LMS, i ) then
                     LMS[i]:= {@FpL| @};
                 end if;
             end for;
          end if;
       else
          Append( ~LMS, newLMS );
       end if;

       // see whether any of the basis elements reduce...
       // not necessary if no new rels of low deg found...

       if lowDeg then
          newB:= [ FpL | ];
          newdegs:= [ ];
          for i in [1..#B] do

              p:= NormalForm( B[i], G );
              // If the basis element does not reduce, then it remains
              // a basis element; otherwise we get rid of it.

              if B[i] eq p then
                 Append( ~newB, B[i] );
                 Append( ~newdegs, degs[i] );
              end if;
          end for;

          B:= newB;
          degs:= newdegs;
       end if;

       if nilq_nothom and l gt NilQuot then
          // no need to search for new basis elements, as these already 
          // have been added as relations...
          newBasElt:= false;
       end if;

       if newBasElt then
          // in the previous round new basis elements have been found,
          // so we must see whether the same holds in this round.

          // make new basis elements
          newBasElt:= false;
          len:= #B;

          for i in [1..len] do
              for j in [i+1..len] do
                  if degs[i] + degs[j] eq l then
                     mn:= ( B[i], B[j] );
                     // This monomial reduces if and only if it is equal
                     // to a leading monomial of a GB element (this follows
                     // from the fact that B[i], B[j] are reduced).

                     if not mn in LMS[ l ] then
                        Append( ~B, mn );
                        Append( ~degs, l );
                        newBasElt:= true;
                     end if;
                  end if;
              end for;
          end for;

          if not newBasElt then
             // No new basis elements are found. This means that we can
             // determine the bound up to which we have to enumerate 
             // relations. If the relations are homogeneous, then we 
             // stop immediately, because all monomials of higher degree
             // will reduce. Because of homogeneity they cannot reduce
             // to things of lower degree, so they will reduce to zero.
             // In the non-homgeneous case we have to enumerate until
             // 2*l-1, and we have to include all relations.
             if IS_HOM then
                bound:= l;
             elif not nilq_nothom then
                bound:= Maximum( 2*l-1, Maximum( [ Degree( r ) : r in R ] ) );
             end if;
             // if nilq_nothom then we leave the bound as it is.

          end if;

       end if;

    end while;

    // in the homogeneous case the thing is graded...
    if IS_HOM then
       gr:= [ ];
       k:= 1;
       while k le #B do 
          dm:= Degree( B[k] );
          n:= 0;
          while k le #B and Degree( B[k] ) eq dm do
              k:= k+1;
              n:= n+1;
          end while;
          Append( ~gr, [dm,n] );
       end while;
    else
       gr:= [ ];
    end if; 

    L:= InternalGBLieAlgebra(FpL, bound, B, GD, IS_HOM);
    // (This DID give the structure constants all multiplied by -1.)

/*
    // make the Lie algebra
    lens:= [ #u : u in LMS ];
    T:= [ ];
    for i in [1..#B] do
        for j in [i+1..#B] do

            if (IS_HOM and degs[i]+degs[j] lt bound) or not IS_HOM then

               // if the relations are homogeneous, than anything of degree
               // larger than bound will reduce to zero.
   
               m:= B[i]*B[j];            
               dm:= Degree( m );
               pos:= Position( LMS[dm], m );
               mns:= [ ];
               cfs:= [ ];
               if pos gt 0 then 
                  g:= G[ &+[ lens[j] : j in [1..dm-1] ]+pos];
                  mons:= Monomials( g );
                  cofs:= Coefficients( g );
                  for k in [2..#mons] do
                      Append( ~mns, mons[k] );
                      Append( ~cfs, -cofs[k]/cofs[1] );
                  end for;
               else
                  mns:= [ m ];
                  cfs:= [ 1 ];
               end if;

               for k in [1..#mns] do
                   pos:= Position( B, mns[k] );
                   Append( ~T, <i,j,pos,BaseRing( FpL )!cfs[k]> );
                   Append( ~T, <j,i,pos,BaseRing( FpL )!(-cfs[k])> );
               end for;
            end if;

        end for; 
    end for;

    if #T eq 0 then
       T:= [ <1,1,1,0> ];
    end if; 

    L:= LieAlgebra< BaseRing( FpL ), #B | T >;
*/


    // We add a function that takes two bracketed expressions, and 
    // returns their product as a lin co of bracketed expressions.

    bas:= {@@};
    for i in [1..#B] do Include( ~bas, B[i] ); end for;

    mult := function( a, b )
         k1:= Position( bas, a );
         k2:= Position( bas, b );
		 error if (k1 eq 0) or (k2 eq 0), "mult: (a,b) is not in BxB.";
         x:= Eltseq( L.k1*L.k2 );
         u:= Zero( FpL );
         for i in [1..#x] do
             if not IsZero( x[i] ) then
                u:= u + x[i]*bas[i];
             end if;
         end for;
         return u;
    end function;

    return L, gr, B, map< CartesianProduct(bas, bas) -> FpL | x :-> mult(x[1], x[2]) >;

end intrinsic;

intrinsic LieAlgebra(R::Setq[AlgFPLieElt])
    -> AlgLie, SeqEnum, SeqEnum, UserProgram
{Return a structure constant Lie algebra which is isomorphic to the
free Lie algebra modulo the relations in R.}
    return NilpotentQuotient(R, Infinity());
end intrinsic;

intrinsic InternalQuoAlgFPLie(L::AlgFPLie, R::Setq[AlgFPLieElt]) -> AlgLie, Map
{Construct the lie algebra L/I, where I is the ideal generated by the elements of R.}
	require #R gt 0 and Universe(R) eq L : "quo<L|R>: R should be a nonempty sequence of elements of L";
	require IsField(BaseRing(L)) : "quo<L|R>: The coefficient ring of L should be a field.";

	/* Do the hard work */
	K, _, B, _ := LieAlgebra(R);

	//Set up the map from K -> L
	KtoL := func<x | &+[ x[i]*B[i] : i in [1..Dimension(K)] ]>;
	
	//Set up the map from L -> K
	Bis := {@ b : b in B @};
	imgs := [ K | p ne 0 select K.p else 0 where p := Position(B, L.i) : i in [1..Rank(L)] ];
	homLK := hom<L -> K | imgs>;

	return K, map<L -> K | x :-> homLK(x), x :-> KtoL(x)>;
end intrinsic;


intrinsic InternalHomAlgFPLie(L::AlgFPLie, M::Any, Q::SeqEnum) -> Map
{Construct a hom from L to M, where L.i is mapped to Q[i]. 
 Q must be a sequence of elements of M of length Rank(L)}

	assert #Q eq Rank(L);
	ChangeUniverse(~Q, M);
	
	mptrm := function(t)
		c := LeadingCoefficient(t);
		m,a,b := IsLeaf(t);
		if m then
			return c*Q[a];
		else 
			return c*$$(a)*$$(b);
		end if;
	end function;
	mp := function(x)
		return &+[ M | mptrm(t) : t in Terms(x) ];		
	end function;
	
	return map<L -> M | x :-> mp(x)>;
end intrinsic;

