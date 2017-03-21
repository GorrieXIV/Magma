freeze;

///////////////////////////////////////////////////////////////////////////

declare attributes AlgQUE: Counit, Antipode, Comultiplications, 
                           HopfStructureTwist;


import "autom.m" : FindDef_F, FindDef_E, anti_automorphism; 
import "qea.m" : in_p;

intrinsic Counit( U::AlgQUE ) -> Map
{The counit of the quantized enveloping algebra U}

     if assigned U`Counit then
        return U`Counit;
     end if; 

     eps:= function( x )


           R:= RootDatum( U );
           s:= #PositiveRoots( R );
           r:= Rank( R );
           mx:= Monomials( x );
           cx:= Coefficients( x );
           a:= Zero( CoefficientRing( U ) );
           for i in [1..#mx] do
               b:= One( CoefficientRing(U) );
               l:= 1;
               while l le s and not IsZero(b) do
                   dl:= Degree( mx[i], l );
                   if dl gt 0 then
                      b:= Zero( CoefficientRing(U) );
                   end if;
                   l:= l+1;
               end while;
               l:= 1;
               while l le s and not IsZero(b) do
                   dl:= Degree( mx[i], s+r+l );
                   if dl gt 0 then
                      b:= Zero(CoefficientRing(U));
                   end if;
                   l:= l+1;
               end while;

               l:= 1;
               while l le r and not IsZero(b) do
                   dl:= KDegree( mx[i], l );
                   if dl[2] gt 0 then
                      b:= Zero(CoefficientRing(U));
                   end if;
                   l:= l+1;
               end while;   

               a:= a + cx[i]*b;
           end for;

           return a;

     end function;

     b,_, f:= HasTwistedHopfStructure( U );
     if b then 
        e:= map< U -> CoefficientRing(U) | x :-> eps( f(x) ) >;
     else
        e:= map< U -> CoefficientRing(U) | x :-> eps(x) >;
     end if;
     U`Counit:= e;
     return e;

end intrinsic;

standard_antipode:= function( U )

    // Make the stamdard antipode....

    imgs:= [ ];

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;

    for j in [1..#posR] do
        // compute the imaga of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           imgs[pos]:= -U.pos*U.(s+j);

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[2] ]*imgs[ pair[1] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do

               a:= One( U );
               for l in [s..1 by -1] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[l]^dl;
                      a := a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;

    for j in [1..rank] do
        Append( ~imgs, U.(s+j)^-1 );
        Append( ~imgs, U.(s+j) );
    end for;

    for j in [1..#posR] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           imgs[s+2*rank+pos]:= -U.(s+j)^-1*U.(s+rank+pos);
   
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ rank+pair[2] ]*imgs[ rank+pair[1] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= One( U );
               for l in [s..1 by -1] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[ s+2*rank+l ]^dl;
                      a:= a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[s+2*rank+pos]:= im;
          
        end if;
    end for;


    S:= anti_automorphism( U, imgs );

    // Now we do the same for the inverse...
    imgs:= [ ];
    for j in [1..#posR] do
        // compute the imaga of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           imgs[pos]:= -q^( -Integers()!CF[j][j] )*U.pos*U.(s+j);

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[2] ]*imgs[ pair[1] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do

               a:= One( U );
               for l in [s..1 by -1] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[l]^dl;
                      a := a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;

    for j in [1..rank] do
        Append( ~imgs, U.(s+j)^-1 );
        Append( ~imgs, U.(s+j) );
    end for;

    for j in [1..#posR] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           imgs[s+2*rank+pos]:= -q^( Integers()!CF[j][j] )*
                                       U.(s+j)^-1*U.(s+rank+pos);
   
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ rank+pair[2] ]*imgs[ rank+pair[1] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= One( U );
               for l in [s..1 by -1] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[ s+2*rank+l ]^dl;
                      a:= a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[s+2*rank+pos]:= im;
          
        end if;
    end for;


    Sinv:= anti_automorphism( U, imgs );

    return map< U -> U | x :-> S(x), y :-> Sinv(y) >; 

end function;

intrinsic Antipode( U::AlgQUE ) -> Map
{Antipode of the quantized enveloping algebra U}

    if assigned U`Antipode then 
       return U`Antipode;
    end if;

    sa:= standard_antipode( U );
    b,f, fi:= HasTwistedHopfStructure( U );
    if b then
       // we have to compute S all over again...
     
       // first we see whether f is an automorphism, or antiautomorphism

       R:= U`RootDatum;
       s:= #PositiveRoots(R);
       rank:= Rank(R);
       
       // we find two elements x, y such that f(x)f(y) ne f(y)f(x)
       found:= false; 
       for i in [1..2*s+rank] do
           if found then break i; end if;
           a:= f(U.i);
           for j in [i+1..2*s+rank] do
               b:= f(U.j);
               if a*b ne b*a then
                  if f(U.i*U.j) eq a*b then
                     is_aut:= true;
                  else
                     is_aut:= false;
                  end if;
                  found:= true;
                  break j;
               end if;
           end for;
       end for;

       sai:= Inverse( sa );

       imgs:= [ ];
       for i in [1..s] do
           if is_aut then
              imgs[i]:= f( sa( fi( U.i ) ) );
              imgs[i+2*rank+s]:= f( sa( fi( U.(i+rank+s) ) ) );
           else
              imgs[i]:= f( sai( fi( U.i ) ) );
              imgs[i+2*rank+s]:= f( sai( fi( U.(i+rank+s) ) ) );
           end if;
       end for;

       for i in [1..rank] do
           if is_aut then
              imgs[s+2*i-1]:= f( sa( fi( U.(s+i) ) ) );
              imgs[s+2*i]:= f( sa( fi( U.(i+s)^-1 ) ) );
           else
              imgs[s+2*i-1]:= f( sai( fi( U.(s+i) ) ) );
              imgs[s+2*i]:= f( sai( fi( U.(s+i)^-1 ) ) );
           end if;
       end for;

       S:= anti_automorphism( U, imgs );
 
       // inverse...
       imgs:= [ ];
       for i in [1..s] do
           if is_aut then
              imgs[i]:= f( sai( fi( U.i ) ) );
              imgs[i+rank+s]:= f( sai( fi( U.(i+rank+s) ) ) );
           else
              imgs[i]:= f( sa( fi( U.i ) ) );
              imgs[i+rank+s]:= f( sa( fi( U.(i+rank+s) ) ) );
           end if;
       end for;

       for i in [1..rank] do
           if is_aut then
              imgs[s+2*i-1]:= f( sai( fi( U.(s+i) ) ) );
              imgs[s+2*i]:= f( sai( fi( U.(i+s)^-1 ) ) );
           else
              imgs[s+2*i-1]:= f( sa( fi( U.(s+i) ) ) );
              imgs[s+2*i]:= f( sa( fi( U.(s+i)^-1 ) ) );
           end if;
       end for;

       Sinv:= anti_automorphism( U, imgs );

       sa:= map< U -> U | x :-> S(x), y :-> Sinv(y) >;
    end if;

    U`Antipode:= sa;
    return sa;


end intrinsic;
    
// An element of the d-th tensor power of U is a list of
// the form [* tuple, cft, tuple, cft...*]. Where tuple 
// is a d-tuple of elements of U. All these elements are
// monomials. First we have a few functions for 
// addition, multiplication, etc.

    
add:= function( a, b )

       if #a eq 0 then return b; end if;
       if #b eq 0 then return a; end if;

       tups:= [ ];
       cfs:= [ ];
       for i in [1..#a-1 by 2] do
           Append( ~tups, a[i] );
           Append( ~cfs, a[i+1] );
       end for;
       for i in [1..#b-1 by 2] do

           // look for the place of b[i]...
           k:= 1;
           pos:= 0;
           while k le #tups and pos eq 0 do
               if b[i] le tups[k] then
                  pos:= k;
               end if;
               k:= k+1;
           end while;
           if pos eq 0 then
              pos:= #tups+1;
           end if;

           if pos gt #tups then
              Append( ~tups, b[i] );
              Append( ~cfs, b[i+1] );
           elif b[i] eq tups[pos] then
              c:= cfs[pos]+b[i+1];
              if IsZero( c ) then
                 Remove( ~tups, pos );
                 Remove( ~cfs, pos );
              else
                 cfs[pos]:= c;
              end if;
           else
              Insert( ~tups, pos, b[i] );
              Insert( ~cfs, pos, b[i+1] );
           end if;

       end for;

       res:= [**];
       for i in [1..#tups] do
           Append( ~res, tups[i] );
           Append( ~res, cfs[i] );
       end for;

       return res;
end function;

    
mult:= function( a, b )

       if #a eq 0 then
          return a;
       end if;

       d:= #a[1];

       tups:= [ ];
       cfs:= [ ];

       for i in [1..#a-1 by 2] do
           for j in [1..#b-1 by 2] do
               
               elm:= [* a[i][k]*b[j][k] : k in [1..d] *];
               mns:= [ Monomials( u ) : u in elm ];
               ccc:= [ Coefficients( u ) : u in elm ];

               tt:= [ <> ];
               cc:= [ a[i+1]*b[j+1] ];
               for k in [1..d] do
                   tt1:= [ ];
                   cc1:= [ ];
                   for l in [1..#mns[k]] do
                       for r in [1..#tt] do
                           t:= tt[r];
                           Append( ~t, mns[k][l] );
                           Append( ~tt1, t );
                           c:= cc[r]*ccc[k][l];
                           Append( ~cc1, c );
                       end for;
                   end for;
                   tt:= tt1;
                   cc:= cc1;
               end for;

               tups cat:= tt;
               cfs cat:= cc;
           end for;
       end for;     

       Sort( ~tups, ~p );
       cc:= [ ];
       for i in [1..#cfs] do
           j:= i^p;
           cc[i]:= cfs[j];
       end for;
       
       res:= [**];
       i:= 1;
       while i le #tups do
           c:= cc[i];
           found:= false;
           while i lt #tups and not found do
               if tups[i+1] eq tups[i] then
                  c +:= cc[i+1];
                  i:= i+1;
               else
                  found:= true;
               end if;
           end while;
           if not IsZero( c ) then
              Append( ~res, tups[i] );
              Append( ~res, c );
           end if;
           i:= i+1;
       end while;

       return res;
end function;

scl_mult:= function( scal, a )

       res:= [**];
       for i in [1..#a-1 by 2] do
           Append( ~res, a[i] );
           Append( ~res, scal*a[i+1] );
       end for;
       return res;

end function; 

apply_fct:= function( U, deg, f, a )

       // here a is a tensor element of degree deg, f : U -> U a fucntion,
       // we compute (f\tensor ... \tensor f)(a)


       tups:= [ ];
       ccc:= [ ];

       for i in [1..#a by 2 ] do
           f_list:= [ f(a[i][k]) : k in [1..deg] ];
           mns:= [ Monomials(u) : u in f_list ];
           cfs:= [ Coefficients(u) : u in f_list ]; 

           tt:= [ <> ];
           cc:= [ a[i+1] ];
           for k in [1..deg] do
               tt1:= [ ];
               cc1:= [ ];
               for l in [1..#mns[k]] do
                   for r in [1..#tt] do
                       t:= tt[r];
                       Append( ~t, mns[k][l] );
                       Append( ~tt1, t );
                       c:= cc[r]*cfs[k][l];
                       Append( ~cc1, c );
                   end for;
               end for;
               tt:= tt1;
               cc:= cc1;
           end for;

           tups cat:= tt;
           ccc cat:= cc;
       end for; 

       Sort( ~tups, ~p );
       cc:= [ ];
       for i in [1..#ccc] do
           j:= i^p;
           cc[i]:= ccc[j];
       end for;
       
       res:= [**];
       i:= 1;
       while i le #tups do
          c:= cc[i];
          found:= false;
          while i lt #tups and not found do
              if tups[i+1] eq tups[i] then
                 c +:= cc[i+1];
                 i:= i+1;
              else
                 found:= true;
              end if;
          end while;
          if not IsZero( c ) then
             Append( ~res, tups[i] );
             Append( ~res, c );
          end if;
          i:= i+1;
       end while;
       return res;

end function;

intrinsic Comultiplication( U::AlgQUE, deg::RngIntElt ) -> Map
{The computiplication of degree deg of the quantized enveloping algebra U}

    require deg ge 2 : 
           "The degree of a comultiplication map must be at least 2.";

    if not assigned U`Comultiplications then
       U`Comultiplications:= [];
    end if;

    comults:= U`Comultiplications;

    if IsDefined( comults, deg-1 ) then return comults[deg-1]; end if;

    imgs:= [ ];

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;
    F:= CoefficientRing( U );

    t:= <>;
    for i in [1..deg] do Append( ~t, One(U) ); end for;
    one:= [* t, One(F) *];

    for j in [1..s] do
        // compute the imaga of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           elm:= [**];
           for i in [1..deg] do
               t:= <>;
               for k in [1..i-1] do
                   Append( ~t, One(U) );
               end for;
               Append( ~t, U.pos );
               for k in [i+1..deg] do
                   Append( ~t, U.(s+j)^-1 );
               end for;
               Append( ~elm, t );
               Append( ~elm, One( F ) );
           end for;

           imgs[pos]:= mult( one, elm );

           // (we multiply by one in order to get it into normal form).

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= scl_mult( (1/cf), mult( imgs[ pair[1] ], imgs[ pair[2] ] ) );
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do

               a:= one;
               for l in [1..s] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      for i in [1..dl] do
                          a:= mult( a, imgs[l] );
                      end for;
                      a := scl_mult( 1/cf, a );
                   end if;
               end for;
               a:= scl_mult( cfs[k], a );
               im:= add( im, a );
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;


    for j in [1..s] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           elm:= [**];
           for i in [1..deg] do
               t:= <>;
               for k in [1..i-1] do
                   Append( ~t, U.(s+j) );
               end for;
               Append( ~t, U.(s+rank+pos) );
               for k in [i+1..deg] do
                   Append( ~t, One(U) );
               end for;
               Append( ~elm, t );
               Append( ~elm, One( F ) );
           end for;

           imgs[s+rank+pos]:= mult( one, elm );
   
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= scl_mult( 1/cf, mult( imgs[ pair[1] ], imgs[ pair[2] ] ) );
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= one;
               for l in [1..s] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      for i in [1..dl] do
                          a:= mult( a, imgs[ s+rank+l ] );
                      end for;
                      a:= scl_mult( 1/cf, a );
                   end if;
               end for;
               a:= scl_mult( cfs[k], a );
               im:= add( im, a );
           end for;
           
           imgs[s+rank+pos]:= im;
          
        end if;
    end for;


    D:= function( x )


          a:= [**];
          mx:= Monomials( x );
          cx:= Coefficients( x );
          for k in [1..#mx] do
        
              b:= one;
              // first we see whether the monomial contains F's...
              for l in [1..s] do
                  dl:= Degree( mx[k], l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     for i in [1..dl] do
                         b:= mult( b, imgs[ l ] );
                     end for;
                     b:= scl_mult( 1/cf, b );
                  end if;
              end for;

              // look for K's...
              for l in [1..rank] do
                  dl:= KDegree( mx[k], l );
                  if dl ne <0,0> then

                     t:= <>;
                     for i in [1..deg] do
                         Append( ~t, U.(s+l) );
                     end for;
                     K:= [* t, One(F) *];
                     t:= <>;
                     for i in [1..deg] do
                         Append( ~t, U.(s+l)^-1 );
                     end for;
                     Ki:= mult( one, [* t, One(F) *] );
 
                     if dl[1] gt 0 then
                        b:= mult( b, K );
                     end if;

                     if dl[2] gt 0 then
                        qa:= q^( Integers()!(CF[l][l]/2) );
                        c:= one;
                        for i in [1..dl[2]] do
                            c:= scl_mult( 1/(qa^i-qa^-i), 
                                   mult( c, add( scl_mult( qa^(-i+1), K ),
                                                 scl_mult( -qa^(i-1), Ki ) )
                                       )
                                        );
                        end for;
                        b:= mult( b, c );
                     end if;

                  end if;
              end for;

              // look for E's...
              for l in [1..s] do
                  dl:= Degree( mx[k], s+rank+l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     for i in [1..dl] do
                         b:= mult( b, imgs[ s+rank+l ] );
                     end for;
                     b:= scl_mult( 1/cf, b );
                  end if;
              end for;
              a:= add( a, scl_mult( cx[k], b ) );

          end for;

          return a;
    end function;

    b,f, fi:= HasTwistedHopfStructure( U );
    if b then 

       imgs:= [ ];
       for j in [1..s] do
           imgs[j]:= apply_fct( U, deg, f, D( fi( U.j ) ) );
       end for;
       for j in [1..rank] do
           Append( ~imgs, apply_fct( U, deg, f, D( fi( U.(s+j) ) ) ) );
           Append( ~imgs, apply_fct( U, deg, f, D( fi( U.(s+j)^-1 ) ) ) );
       end for;
       for j in [1..s] do
           imgs[s+2*rank+j]:= apply_fct( U, deg, f, D( fi( U.(j+rank+s) ) ) );
       end for;

       D:= function( x )

          a:= [**];
          mx:= Monomials( x );
          cx:= Coefficients( x );
          for k in [1..#mx] do
        
              b:= one;
              // first we see whether the monomial contains F's...
              for l in [1..s] do
                  dl:= Degree( mx[k], l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     for i in [1..dl] do
                         b:= mult( b, imgs[ l ] );
                     end for;
                     b:= scl_mult( 1/cf, b );
                  end if;
              end for;

              // look for K's...
              for l in [1..rank] do
                  dl:= KDegree( mx[k], l );
                  if dl ne <0,0> then

                     if dl[1] gt 0 then
                        b:= mult( b, imgs[s+2*l-1] );
                     end if;

                     if dl[2] gt 0 then
                        qa:= q^( Integers()!(CF[l][l]/2) );
                        c:= one;
                        K:= imgs[s+2*l-1];
                        Ki:= imgs[s+2*l];
                        for i in [1..dl[2]] do
                            c:= scl_mult( 1/(qa^i-qa^-i), 
                                   mult( c, add( scl_mult( qa^(-i+1), K ),
                                                 scl_mult( -qa^(i-1), Ki ) )
                                       )
                                        );
                        end for;
                        b:= mult( b, c );
                     end if;

                  end if;
              end for;

              // look for E's...
              for l in [1..s] do
                  dl:= Degree( mx[k], s+rank+l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     for i in [1..dl] do
                         b:= mult( b, imgs[ s+2*rank+l ] );
                     end for;
                     b:= scl_mult( 1/cf, b );
                  end if;
              end for;
              a:= add( a, scl_mult( cx[k], b ) );

          end for;

          return a;
       end function;

    end if;

    comults[deg-1]:= D;
    U`Comultiplications:= comults;
    
    return D;


end intrinsic;


intrinsic UseTwistedHopfStructure( U::AlgQUE, f::Map, finv::Map )
{Force U to use a Hopf structure that is twisted by f}

    require Domain(f) eq U and Codomain(f) eq U : "f is not a mapping U->U.";
 
    require Domain(finv) eq U and Codomain(finv) eq U : 
       "The inverse of f is not a mapping U->U.";
    
    U`HopfStructureTwist:= [ f, finv ];

end intrinsic;

intrinsic HasTwistedHopfStructure( U::AlgQUE ) -> BoolElt, Map, Map
{Check whether U uses a twisted Hopf structure}

    if assigned U`HopfStructureTwist then
       return true, U`HopfStructureTwist[1], U`HopfStructureTwist[2];
    else
       return false, _, _;
    end if;

end intrinsic;

