freeze;

///////////////////////////////////////////////////////////////////////////

comp_tab:= procedure( ~T )

   
     len:= #T;
     for i in [1..len] do
         t:= <T[i][2],T[i][1],T[i][3],-T[i][4]>;
         if not t in T then 
            Append( ~T, t );
         end if;
     end for;

end procedure;


// dim 2


L2_1:= function( F ) 

     S:= [ <1,2,1,0> ];
     comp_tab( ~S );
     return LieAlgebra< F, 2 | S >;

end function;

L2_2:= function( F ) 

     
     S:= [ <2,1,1,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 2 | S >;

end function;


//dim3

// Abelian Lie algebra L^1:
L3_1:= function( F ) 

     S:= [ <1,2,1,0> ];
     comp_tab( ~S );
     return LieAlgebra< F, 3 | S >;

end function;

// L^2:
L3_2:= function( F ) 

     S:= [ <3,1,1,1>, <3,2,2,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 3 | S >;

end function;

// L^3_a:
L3_3:= function( F, a ) 

     S:= [ <3,1,2,1>, <3,2,1,a>, <3,2,2,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 3 | S >;

end function;

// L^4_a:
L3_4:= function( F, a ) 

     S:= [ <3,1,2,1>, <3,2,1,a> ];
     comp_tab( ~S );
     return LieAlgebra< F, 3 | S >;

end function;


//dim 4 

L4_1:= function( F ) 

     S:= [ <1,2,1,0> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_2:= function( F ) 

     S:= [ <4,1,1,1>, <4,2,2,1>, <4,3,3,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_3:= function( F, a ) 

     S:= [ <4,1,1,1>, <4,2,3,1>, <4,3,2,-a>, <4,3,3,1+a> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_4:= function( F ) 

     S:= [ <4,2,3,1>, <4,3,3,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_5:= function( F ) 

     S:= [ <4,2,3,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_6:= function( F, a, b ) 

     S:= [ <4,1,2,1>, <4,2,3,1>, <4,3,1,a>, <4,3,2,b>, <4,3,3,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_7:= function( F, a, b ) 

     S:= [ <4,1,2,1>, <4,2,3,1>, <4,3,1,a>, <4,3,2,b> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_8:= function( F ) 

     S:= [ <1,2,2,1>, <3,4,4,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;


L4_9:= function( F, a  ) 

     S:= [ <4,1,1,1>, <4,1,2,a>, <4,2,1,1>, <3,1,1,1>, <3,2,2,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_10:= function( F, a  ) 

     S:= [ <4,1,2,1>, <4,2,1,a>, <3,1,1,1>, <3,2,2,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;

L4_11:= function( F, a, b  ) 

     S:= [ <4,1,1,1>, <4,2,2,b>, <4,3,3,1+b>, <3,1,2,1>, <3,2,1,a> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;


L4_12:= function( F ) 

     S:= [ <4,1,1,1>, <4,2,2,2>, <4,3,3,1>, <3,1,2,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;


L4_13:= function( F, a ) 

     S:= [ <4,1,1,1>, <4,1,3,a>, <4,2,2,1>, <4,3,1,1>, <3,1,2,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;


L4_14:= function( F, a ) 

     S:= [ <4,1,3,a>, <4,3,1,1>, <3,1,2,1> ];
     comp_tab( ~S );
     return LieAlgebra< F, 4 | S >;

end function;


liealg_hom:= function( K, L, p, i )

     return hom< K -> L | [ <p[k],i[k]> : k in [1..#p] ] >;

end function;

forward id_data;

isomN:= function( L, x1, x2, x3, x4 )

      // Here the xi satisfy the commutation relations of N;
      // we produce the isomorphism with M_0^13...

      F:= BaseRing( L );

      if Characteristic(F) ne 3 then
         y1:= x1+x2;
         y2:= 3*x1-(3/2*One(F))*x2;
         y3:= x1+x2-x3+2*x4;
         y4:= x3;
      else
         y1:= x2;
         y2:= x1+x2;
         y3:= x1-x2+x3+x4;
         y4:= x1-x2+x3;
      end if;
      name:= "L4_13( ";
      name cat:= Sprint( F );
      name cat:= ", ";
      name cat:= Sprint( Zero(F) );
      name cat:= " )";
      K:= L4_13( F, Zero(F) );
      f:= liealg_hom(K,L,Basis(K),[y1,y2,y3,y4]);
      return  name, [ Zero(F) ], f;

end function;

isomM9:= function( L, x1, x2, x3, x4, a )

      // The xi satisfy the commutation rules of M9a; we return 
      // the isomorphism with either N, M8 or M9a

      F:= BaseRing( L );

      if Characteristic(F) ne 2 then
         if a eq (-1/4)*One(F) then
            return isomN( L, x1, x2, x3, x4 );
         end if;
      end if;

      P := PolynomialRing( F ); T := P.1;
      pol:= T^2-T-a;
      facs:= Factorization( pol );

      if #facs eq 2 or (#facs eq 1 and facs[1][2] eq 2) then
         //direct sum...
         dd:= DirectSumDecomposition( L );
         _,_,f:= id_data( dd[1] );
         K1:= Domain( f );
         x1:= f( K1.2 );
         x2:= f( K1.1 );
         _,_,f:= id_data( dd[2] );
         K1:= Domain( f );
         x3:= f( K1.2 );
         x4:= f( K1.1 );
         name:= "L4_8( ";
         name cat:= Sprint( F );
         name cat:= " )";
         K:= L4_8( F );
         f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
         return  name, [], f;     
      else

         if IsFinite(F) then
            // for M9 we let b be the smallest power of the primitive root
            // such that T^2-T-b has no roots in F
            q:= #F;
            prim:= PrimitiveElement( F );
            for i in [1..q-1] do
                facs:= Factorization( T^2-T-prim^i );
                if #facs eq 1 and facs[1][2] eq 1 then
                   b:= prim^i;
                   break;
                end if;
            end for;
            
            if Characteristic(F) gt 2 then
               c:= Sqrt( (b+One(F)/4)/(a+One(F)/4) );               
               x1:= c*x1+((One(F)-c)/2)*x2;
               x4:= ((One(F)-c)/2)*x3+c*x4;
            else
               facs:= Factorization( T^2+T+a+b );
               ef:= Coefficients( facs[1][1] );
               c:= -ef[1];
               x1:= x1+c*x2;
               x4:= c*x3+x4;
            end if;
         else
            b:= a;
         end if;
         name:= "L4_9( ";
         name cat:= Sprint( F );
         name cat:= ", ";
         name cat:= Sprint( b );
         name cat:= " )";
         K:= L4_9( F, b );
         f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
         return  name, [ b ], f;
      end if;

end function;

isomM10:= function( L, x1, x2, x3, x4, a )

      // the xi satisfy the commutation rels of M10(a)
      // char is 2
      F:= BaseRing( L );
      if IsFinite(F) then
         b:= Sqrt( a );
         y1:= x1;
         y2:= b*x1+x2;
         y3:= x3;
         y4:= b*x3+x4;
         name:= "L4_13( ";
         name cat:= Sprint( F );
         name cat:= ", ";
         name cat:= Sprint( Zero(F) );
         name cat:= " )";
         K:= L4_13( F, Zero(F) );
         f:= liealg_hom(K,L,Basis(K),
                                       [y1,y2,y1+y2+y4,y1+y2+y3]);
         return  name, [Zero(F)], f;
      else
         name:= "L4_10( ";
         name cat:= Sprint( F );
         name cat:= ", ";
         name cat:= Sprint( a );
         name cat:= " )";
         K:= L4_10( F, a );
         f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
         return  name, [a], f;
      end if;
end function;

isomM11:= function( L, x1, x2, x3, x4, a, b )

      F:= BaseRing(L);
                  
      if b eq Zero(F) then
         name:= "L4_11( ";
         name cat:= Sprint( F );
         name cat:= ", ";
         name cat:= Sprint( a );
         name cat:= ", ";
         name cat:= Sprint( b );
         name cat:= " )";
         K:= L4_11( F, a, b );
         f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
         return  name, [a,b], f;
      elif IsFinite(F) then
         gam:= Sqrt( b/(a*(b^2+One(F))) );
         eps:= Sqrt( 1/a );
         del:= 1/(1+b);
         y1:= a*gam*x1+b*del*x2;
         y2:= a*eps*b*del*x1+a*gam*eps*x2;
         y3:= eps*x3;
         y4:= gam*x3+del*x4;
         name:= "L4_11( ";
         name cat:= Sprint( F );
         name cat:= ", ";
         name cat:= Sprint( One(F) );
         name cat:= ", ";
         name cat:= Sprint( Zero(F) );
         name cat:= " )";
         K:= L4_11( F, One(F), Zero(F) );
         f:= liealg_hom(K,L,Basis(K),[y1,y2,y3,y4]);
         return  name, [One(F),Zero(F)], f;
      else 
         name:= "L4_11( ";
         name cat:= Sprint( F );
         name cat:= ", ";
         name cat:= Sprint( a );
         name cat:= ", ";
         name cat:= Sprint( b );
         name cat:= " )";
         K:= L4_11( F, a, b );
         f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
         return  name, [a,b], f;
      end if;     
end function;


id_data:= function( L )

     n:= Dimension( L );
     F:= BaseRing( L );


     V:= KSpace( F, n );
     DL:= L*L;
     b:= [ V!( Eltseq( L!DL.i ) ) : i in [1..Dimension(DL)] ];
     sp:= sub< V | b >;

     k:= 1;
     while Dimension( sp ) lt n-1 do
         if not V!Eltseq( L.k ) in sp then
            Append( ~b, V!Eltseq( L.k ) );
            sp:= sub< V | b >;
         end if;
         k:= k+1;
     end while;

     if n eq 2 then

        x1:= L!Eltseq( b[1] );
        for k in [1,2] do
            if not V!Eltseq( L.k ) in sp then
               x2:= L.k;
               break;
            end if;
        end for;
        
        if x1*x2 eq Zero(L) then
           name:= "L2_1( ";
           name cat:= Sprint( F );
           name cat:= " )";
           K:= L2_1( F );
           f:= liealg_hom( K, L, Basis(K), Basis(L) );
           return name, [], f;
        end if;

        c1:= Coordinates( sp, V!Eltseq(x2*x1) );
        x2:= x2/c1[1];
        name:= "L2_2( ";
        name cat:= Sprint( F );
        name cat:=  " )";
        K:= L2_2( F );
        f:= liealg_hom( K, L, Basis(K), [x1,x2] );
        return name, [], f;

     elif n eq 3 then

        x1:= L!Eltseq(b[1]); x2:= L!Eltseq(b[2]);

        if x1*x2 ne Zero(L) then
           // Here [L,L] has dimension 1, and its centralizer
           // has dimension 2, and it contains [L,L].
           sp:= Centralizer( L, DL );
           x1:= L!sp.1;
           x2:= L!sp.2;
           sp:= sub< V | [ V!Eltseq(x1), V!Eltseq(x2) ] >;
        end if;

        for k in [1..3] do
            if not V!Eltseq( L.k ) in sp then
               x3:= L.k;
               break;
            end if;
        end for;

        if x1*x3 eq Zero(L) and x2*x3 eq Zero(L) then
           // Abelian!
           name:= "L3_1( ";
           name cat:= Sprint( F );
           name cat:=  " )";
           K:= L3_1( F );
           f:= liealg_hom( K, L, Basis(K), Basis(L) );
           return name, [], f;
        end if;

        sp:= KSpaceWithBasis( [ V!Eltseq(x1), V!Eltseq(x2) ] );
        c1:= Coordinates( sp, V!Eltseq( x3*x1 ) );
        c2:= Coordinates( sp, V!Eltseq( x3*x2 ) );
        if c1[1] eq c2[2] and c1[2] eq Zero(F) and c2[1] eq Zero(F) then
           x3:= x3/c1[1];
           name:= "L3_2( ";
           name cat:= Sprint( F );
           name cat:= " )";
           K:= L3_2( F );
           f:= liealg_hom( K, L, Basis(K), [x1,x2,x3] );
           return name, [], f;
        end if;

        r,p:= RationalForm( Matrix( F, [ c1, c2 ] ) );
        y1:= p[1][1]*x1+p[1][2]*x2;
        y2:= p[2][1]*x1+p[2][2]*x2;
        x1:= y1; x2:= y2;

        if r[2][2] ne Zero(F) then
           x2:= x2/r[2][2];
           x3:= x3/r[2][2];
           par:= r[2][1]/(r[2][2]^2);
           name:= "L3_3( ";
           name cat:= Sprint( F );
           name cat:= ", ";
           name cat:= Sprint( par );
           name cat:= " )";
           K:= L3_3( F, par );
           f:= liealg_hom( K, L, Basis(K), [x1,x2,x3] );
           return name, [par], f;
        end if;

        par:= r[2][1];
        if IsFinite(F) and not par in [Zero(F),One(F)] then
           if Characteristic(F) eq 2 then
              a:= Sqrt( 1/par );
           else
              exp:= Log( 1/par );
              if IsEven( exp ) then 
                 a:= PrimitiveElement(F)^(Integers()!(exp/2));
              else
                 exp:= Log( PrimitiveElement(F)/par );
                 a:= PrimitiveElement(F)^(Integers()!(exp/2));
              end if;
           end if;
           x2:= a*x2;
           x3:= a*x3;
           par:= a^2*par;
        end if;
        name:= "L3_4( ";
        name cat:= Sprint( F );
        name cat:= ", ";
        name cat:= Sprint( par );
        name cat:= " )";
        K:= L3_4( F, par );
        f:= liealg_hom( K, L, Basis(K), [x1,x2,x3] );
        return name, [par], f;

     elif n eq 4 then

        x1:= L!Eltseq( b[1] ); 
        x2:= L!Eltseq( b[2] ); 
        x3:= L!Eltseq( b[3] );



        for k in [1..4] do
            if not V!Eltseq( L.k ) in sp then
               x4:= L.k;
               break;
            end if;
        end for;

        // See whether ad x4 is an outer derivation of K:

        K:= sub< L |  [x1,x2,x3] >;
        Matsp:= KMatrixSpace( F, 3, 3 );
        adK:= sub< Matsp | [ Zero( Matsp ) ] >;
        bK:= [ ];
        b_adK:= [ ];
        for i in [1..3] do
            adx:= AdjointMatrix( K, K.i );
            if not Matsp!adx in adK then
               Append( ~bK, K.i );
               Append( ~b_adK, adx );
               adK:= sub< Matsp | [ Matsp!u : u in b_adK ] >;
            end if;
        end for;
        
        mat:= [ Coordinates( K, K!((L!K.i)*x4) ) : i in [1,2,3] ];
        mat:= Matsp!Matrix( mat );
        if mat in adK then
           if #b_adK eq 0 and IsZero(mat) then // L is abelian
              name:= "L4_1( ";
              name cat:= Sprint( F );
              name cat:= " )";
              K:= L4_1( F );
              f:= liealg_hom( K, L, Basis(K), Basis(L) );
              return name, [], f;
           else  
              adK:= KMatrixSpaceWithBasis( [ Matsp!u : u in b_adK ] );
              c1:= Coordinates( adK, mat );
              x3:= x4 - &+[ c1[i]*bK[i] : i in [1..#bK] ];
              _,_,f:= $$( K );
              M:= Domain(f);
              x4:= f( M.3 );
              x1:= f( M.1 );
              x2:= f( M.2 );
              K:= sub< L | [x1,x2,x3] >;
           end if;
        end if;

        name_0,p_0,f:= $$( K );
        M:= Domain( f );
        x1:= L!f( M.1 );
        x2:= L!f( M.2 );
        x3:= L!f( M.3 );

        V3:= KSpace( F, 4 );
        KK:= KSpaceWithBasis( [ V3!Eltseq(u) : u in [x1,x2,x3] ] );        
        c1:= Coordinates( KK, V3!Eltseq( x4*x1 ) );
        c2:= Coordinates( KK, V3!Eltseq( x4*x2 ) );
        c3:= Coordinates( KK, V3!Eltseq( x4*x3 ) );
        mat:= [ c1, c2, c3 ];
        num:= name_0[4];

        if num eq "1" then

           // K is abelian

           r,p,pols:= RationalForm( Matrix( F, mat ) );
           y1:= p[1][1]*x1+p[1][2]*x2+p[1][3]*x3;
           y2:= p[2][1]*x1+p[2][2]*x2+p[2][3]*x3;
           y3:= p[3][1]*x1+p[3][2]*x2+p[3][3]*x3;
           x1:= y1; x2:= y2; x3:= y3;
 
           if IsZero( r ) then
              // Abelian..
              name:= "L4_1( ";
              name cat:= Sprint( F );
              name cat:= " )";
              K:= L4_1( F );
              f:= liealg_hom( K, L, Basis(K), Basis(L) );
              return name, [], f;                 
           elif #pols eq 3 then
                x4:= x4/r[1][1];
                name:= "L4_2( ";
                name cat:= Sprint( F );
                name cat:= " )";
                K:= L4_2( F );
                f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                return name, [], f;
           elif #pols eq 2 then
                s:= r[1][1]; 
                if not IsZero( s ) then
                   x3:= x3/s;
                   x4:= x4/s;
                   par:= (r[3][3]-s)/s;
                   name:= "L4_3( ";
                   name cat:= Sprint( F );
                   name cat:= ", ";
                   name cat:= Sprint( par  );
                   name cat:= " )";
                   K:= L4_3( F, par );
                   f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                   return name, [par], f;
                elif not IsZero( r[3][3] ) then
                   t:= r[3][3];
                   x3:= x3/t;
                   x4:= x4/t;
                   name:= "L4_4( ";
                   name cat:= Sprint( F );
                   name cat:= " )";
                   K:= L4_4( F );
                   f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                   return name, [], f;
                else
                   name:= "L4_5( ";
                   name cat:= Sprint( F );
                   name cat:= " )";
                   K:= L4_5( F );
                   f:= liealg_hom(K,L,Basis(K), [x1,x2,x3,x4]);
                   return name, [], f;
                end if;
           else  // i.e., #pols eq 1
                u:= r[3][3];
                if not IsZero(u) then
                   x2:= x2/u;
                   x3:= x3/(u^2);
                   x4:= x4/u;
                   name:= "L4_6( ";
                   name cat:= Sprint( F );
                   name cat:= ", ";
                   name cat:= Sprint( r[3][1]/(u^3) );
                   name cat:= ", ";
                   name cat:= Sprint( r[3][2]/(u^2) );
                   name cat:= " )";
                   K:= L4_6( F, r[3][1]/(u^3), r[3][2]/(u^2) );
                   f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                   return name, [r[3][1]/(u^3), r[3][2]/(u^2)], f; 
                elif ( not IsZero(r[3][1]) ) and (not IsZero(r[3][2])) then
                   s:= r[3][2]/r[3][1];
                   x2:= x2*s;
                   x3:= x3*s^2;
                   x4:= x4*s;
                   t:= s^2*r[3][2];
                   name:= "L4_7( ";
                   name cat:= Sprint( F );
                   name cat:= ", ";
                   name cat:= Sprint( t );
                   name cat:= ", ";
                   name cat:= Sprint( t );
                   name cat:= " )";
                   K:= L4_7( F, t, t );
                   f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                   return name, [t,t], f;
                else

                   if IsFinite(F) then
                      q:= #F;
                      if not IsZero( r[3][1] ) then
                         par:= r[3][1];
                         a:= PrimitiveElement(F);
                         if q mod 6 eq 1 or q mod 6 eq 4 then
                            exp:= Log( par );
                            b:= One(F);
                            if exp mod 3 ne 0 then
                               exp:= Log( par/a  );
                               b:= a;
                               if exp mod 3 ne 0 then
                                  exp:= Log( par/(a^2) );
                                  b:= a^2;
                               end if; 
                            end if;
                            a:= a^( Integers()!(exp/3) );
                         else
                            exp:= Log( par );
                            if exp mod 3 eq 1 then
                               for b in F do
                                   if b^3 eq a then
                                      a:= a^(Integers()!((exp-1)/3))*b;
                                      break;
                                   end if;
                               end for;
                            elif exp mod 3 eq 2 then
                               for b in F do
                                   if b^3 eq a^2 then
                                      a:= a^(Integers()!((exp-2)/3))*b;
                                      break;
                                   end if;
                               end for;
                            else
                               a:= a^(Integers()!(exp/3));
                            end if; 
                            b:= One(F);
                         end if;
                         c1:= [ b, Zero(F) ]; 
                      elif not IsZero( r[3][2] ) then 
                         par:= r[3][2];
                         a:= PrimitiveElement(F);
                         if IsEven( q ) then
                            exp:= Log( par );
                            if exp mod 2 eq 1 then
                               a:= a^(Integers()!((exp-1)/2))*
                                              a^(Integers()!(q/2));
                            else
                               a:= a^(Integers()!(exp/2));
                            end if;
                            b:= One(F);
                         else
                            exp:= Log( par );
                            b:= One(F);
                            if not IsEven( exp ) then
                               exp:= Log( par/a );
                               b:= a;
                            end if;
                            a:= a^(Integers()!(exp/2));
                         end if;
                         c1:= [ Zero(F), b ]; 
                      else
                         a:= One(F);
                         c1:= [ Zero(F), Zero(F) ];
                      end if;
                      x2:= x2/a;
                      x3:= x3/(a^2);
                      x4:= x4/a;
                   else
                      c1:= [r[3][1],r[3][2]];
                   end if;
                   name:= "L4_7( ";
                   name cat:= Sprint( F );
                   name cat:= ", ";
                   name cat:= Sprint( c1[1] );
                   name cat:= ", ";
                   name cat:= Sprint( c1[2] );
                   name cat:= " )";
                   K:= L4_7( F, c1[1], c1[2] );
                   f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                   return name, [c1[1],c1[2]], f;
                end if;
           end if;

        elif num eq "2" then

           D:= Transpose( Matrix( F, mat ) );

           x4:= x4+D[1][3]*x1+D[2][3]*x2-D[2][2]*x3;

           V3:= KSpace( F, 4 );
           KK:= KSpaceWithBasis( [ V3!Eltseq(u) : u in [x1,x2,x3] ] );        
           c1:= Coordinates( KK, V3!Eltseq( x4*x1 ) );
           c2:= Coordinates( KK, V3!Eltseq( x4*x2 ) );
           c3:= Coordinates( KK, V3!Eltseq( x4*x3 ) );
           mat:= [ c1, c2, c3 ];
           D:= Transpose( Matrix( F, mat ) );
       
           if not IsZero( D[1][1] ) then
              x4:= x4/D[1][1];
              D:= D/D[1][1];
              w:= D[1][2];
              v:= D[2][1];

              if not IsZero( w ) then
                 x1:= w*x1;
                 v:= v*w;

                 return isomM9( L, x1, x2, x3, x4, v );

              else
                 //direct sum...
                 dd:= DirectSumDecomposition( L );
                 _,_,f:= $$( dd[1] );
                 M:= Domain( f );
                 x1:= f( M.2 );
                 x2:= f( M.2 );
                 _,_,f:= $$( dd[2] );
                 M:= Domain( f );
                 x3:= f( M.2 );
                 x4:= f( M.1 );
                 name:= "L4_8( ";
                 name cat:= Sprint( F );
                 name cat:= " )";
                 K:= L4_8( F );
                 f:= liealg_hom(K,L,Basis(K), [x1,x2,x3,x4]);
                 return name, [], f;
              end if;
           else

              if not IsZero( D[2][1] ) then 
                 x4:= x4/D[2][1];
                 a:= D[1][2]/D[2][1];
                 if Characteristic(F) ne 2 then
                    a:= a - (1/4)*One(F);
                    return isomM9( L, x1/(4*One(F))+x2/(2*One(F)), 
                                      x1/(2*One(F)), x3, x3/(2*One(F))+x4, a );
                 else
                    return isomM10( L, x1, x2, x3, x4, a );
                 end if;
              else
                 if not IsZero( D[1][2] ) then
                    x4:= x4/D[1][2];
                    if Characteristic(F) ne 2 then
                       y1:= (x1+x2)/(2*One(F));
                       y2:= x2;
                       y3:= x3;
                       y4:= (x3+x4)/(2*One(F));
                       return isomN( L, y1, y2, y3, y4 );
                    else
                      name:= "L4_10( ";
                      name cat:= Sprint( F );
                      name cat:= ", ";
                      name cat:= Sprint( Zero(F) );
                      name cat:= " )";
                      K:= L4_10( F, Zero(F) );
                      f:= liealg_hom(K,L,Basis(K),[x2,x1,x3,x4]);
                      return name, [Zero(F)], f;
                    end if;
                 end if;
              end if;
           end if;            
        elif num eq "3" then

           D:= Transpose( Matrix( F, mat ) );
           a:= p_0[1];

           if not IsZero( a ) then 
              x4:= x4-(D[1][3]/a-D[2][3])*x1+D[1][3]/a*x2-D[2][1]*x3;
              x4:= x4/D[1][1];
              return isomM9( L, x2, x1, x4, x3, a );
           else

              x4:= x4+D[2][3]*x1-D[2][1]*x3;
              V3:= KSpace( F, 4 );
              KK:= KSpaceWithBasis( [ V3!Eltseq(u) : u in [x1,x2,x3] ] );   
              c1:= Coordinates( KK, V3!Eltseq( x4*x1 ) );
              c2:= Coordinates( KK, V3!Eltseq( x4*x2 ) );
              c3:= Coordinates( KK, V3!Eltseq( x4*x3 ) );
              mat:= [ c1, c2, c3 ];
              D:= Transpose( Matrix( F, mat ) );

              if IsZero( D[1][3] ) then 
                 x4:= x4/D[1][1];
                 return isomM9( L, x2, x1, x4, x3, a );
              elif IsZero( D[1][1] ) then 
                 x4:= x4/D[1][3];
                 name:= "L4_6( ";
                 name cat:= Sprint( F );
                 name cat:= ", ";
                 name cat:= Sprint( Zero(F) );
                 name cat:= ", ";
                 name cat:= Sprint( Zero(F) );
                 name cat:= " )";
                 K:= L4_6( F, Zero(F), Zero(F) );
                 f:= liealg_hom(K,L,Basis(K),[-x4,x1,x2,x3]);
                 return name, [Zero(F),Zero(F)], f;
              else
                 x4:= x4/D[1][1];
                 x3:= -D[1][3]/D[1][1]*x1+x3;
                 return isomM9( L, x2, x1, x4, x3, a );
              end if;
           end if;
        else // i.e., num eq "4"...

           D:= Transpose( Matrix( F, mat ) );
           a:= p_0[1];

           if not IsZero( a ) and Characteristic(F) ne 2 then
              x4:= x4+D[2][3]*x1+D[1][3]/a*x2-D[2][1]*x3;
              x4:= x4/D[1][1];
              return isomM9( L, x1/(4*One(F))+x2/(2*One(F)), x1/(2*One(F)), 
                                x4, x3+x4/(2*One(F)), a-(1/4*One(F)) );
           elif not IsZero( a ) and Characteristic(F) eq 2 then

              x4:= x4+D[2][3]*x1+D[1][3]/a*x2-D[2][1]*x3;
              if IsZero( D[3][3] ) then
                 x4:= x4/D[1][1];
                 return isomM10( L, x1, x2, x4, x3, a );
              elif not IsZero( D[1][1] ) then
                 x4:= x4/D[1][1];
                 b:= One(F) + D[3][3]/D[1][1];
                 return isomM11( L, x1, x2, x3, x4, a, b );
              else
                 if a ne One(F) then
                    x4:= x4/D[3][3];
                    y1:= (a*x1+x2)/(a+One(F));
                    y2:= a*(x1+x2)/(a+One(F));
                    y3:= x3;
                    y4:= x3+(a+1)*x4;
                    return isomM11( L, y1, y2, y3, y4, a, a );
                 else
                    return isomM11( L, x2, x1, x3, x4, One(F), Zero(F) );
                 end if;
              end if;
           else       
              x4:= x4+D[2][3]*x1-D[2][1]*x3;
              if IsZero(D[1][3]) and IsZero(D[3][1]) 
                                     and D[1][1] eq D[3][3] then
                 x4:= x4/D[1][1];
                 name:= "L4_12( ";
                 name cat:= Sprint( F );
                 name cat:= " )";
                 K:= L4_12( F );
                 f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                 return name, [], f;
              else

                 if not IsZero(D[3][3]) then
                    u1:= D[1][1];
                    u3:= D[3][1];
                    v1:= D[1][3];
                    v3:= D[3][3];
                    if not IsZero(v1) then
                       x1:= x1+(v3/v1)*x3;
                    elif not IsZero(u3) then 
                       x3:= -(v3/u3)*x1+x3;
                    elif IsZero(u1) then 
                       y1:= x1;
                       x1:= x3;
                       x2:= -x2;
                       x3:= y1;
                    else
                       y1:= x1;
                       x1:= x1/(One(F) - v3/u1)-x3;
                       x3:= -(v3/u1)*y1/(One(F) - v3/u1)+x3;  
                    end if;

                    V3:= KSpace( F, 4 );
                    KK:= KSpaceWithBasis( [ V3!Eltseq(u) : 
                                                 u in [x1,x2,x3] ] );   
                    c1:= Coordinates( KK, V3!Eltseq( x4*x1 ) );
                    c2:= Coordinates( KK, V3!Eltseq( x4*x2 ) );
                    c3:= Coordinates( KK, V3!Eltseq( x4*x3 ) );
                    mat:= [ c1, c2, c3 ];
                    D:= Transpose( Matrix( F, mat ) );
                 end if; // now D[3][3] is zero...

                 u1:= D[1][1]; u3:= D[3][1]; v1:= D[1][3];
                 if not IsZero(u1) and not IsZero(v1) then
                    x4:= x4/u1;
                    x1:= (1/u1)*x1;
                    x2:= (1/(u1*v1))*x2;
                    x3:= (1/v1)*x3;
                    a:= (v1/u1)*(u3/u1);

                    name:= "L4_13( ";
                    name cat:= Sprint( F );
                    name cat:= ", ";
                    name cat:= Sprint( a );
                    name cat:= " )";
                    K:= L4_13( F, a );
                    f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                    return name, [a], f;
                 elif not IsZero(u1) and IsZero(v1) then
                    if not IsZero(u3) then
                       x4:= x4/u1;
                       x1:= (1/u3)*x1;
                       x2:= (1/(u1*u3))*x2;
                       x3:= (1/u1)*x3;
                       y1:= x1;
                       x1:= x1+x3;
                       x2:= -x2;
                       x3:= y1;
                    else
                       x4:= x4/u1;
                       x3:= x1+x3;
                    end if;
     
                    name:= "L4_13( ";
                    name cat:= Sprint( F );
                    name cat:= ", ";
                    name cat:= Sprint( Zero(F) );
                    name cat:= " )";
                    K:= L4_13( F, Zero(F) );
                    f:= liealg_hom(K,L,Basis(K),[x1,x2,x3,x4]);
                    return name, [Zero(F)], f;
                 elif IsZero(u1) and not IsZero(v1) then
                    x4:= x4/v1;
                    par:= u3/v1;
                    if IsFinite(F) and not par in [Zero(F),One(F)] then
                       if Characteristic(F) eq 2 then
                          a:= Sqrt( 1/par );
                       else
                          exp:= Log( 1/par );
                          if IsEven( exp ) then 
                             a:= PrimitiveElement(F)^(Integers()!(exp/2));
                          else
                             exp:= Log( PrimitiveElement(F)/par ); 
                             a:= PrimitiveElement(F)^(Integers()!(exp/2));
                          end if;
                       end if;
                    
                       x1:= a*x1;
                       x2:= a*x2;
                       x4:= a*x4; 
                       par:= a^2*par;
                    end if;
                    if IsZero(par) then

                       name:= "L4_7( ";
                       name cat:= Sprint( F );
                       name cat:= ", ";
                       name cat:= Sprint( Zero(F) );
                       name cat:= ", ";
                       name cat:= Sprint( Zero(F) );
                       name cat:= " )";
                       K:= L4_7( F, Zero(F), Zero(F) );
                       f:= liealg_hom( K, L, Basis(K), [-x4,x1,x2,x3]);
                       return name, [Zero(F),Zero(F)], f; 
                    else
                       
                       name:= "L4_14( ";
                       name cat:= Sprint( F );
                       name cat:= ", ";
                       name cat:= Sprint( par );
                       name cat:= " )";
                       K:= L4_14( F, par );
                       f:= liealg_hom( K, L, Basis(K), [x1,x2,x3,x4] );
                       return name, [par], f;
                    end if;
                 else

                    x4:= x4/u3;
                    y1:= x3;
                    y2:= -x2;
                    y3:= x1;
                    y4:= x4;
                    name:= "L4_7( ";
                    name cat:= Sprint( F );
                    name cat:= ", ";
                    name cat:= Sprint( Zero(F) );
                    name cat:= ", ";
                    name cat:= Sprint( Zero(F) );
                    name cat:= " )";
                    K:= L4_7( F, Zero(F), Zero(F) );
                    f:= liealg_hom( K, L, Basis(K), [-y4,y1,y2,y3] );
                    return name, [Zero(F),Zero(F)], f;
                 end if;
              end if;
           end if;
        end if;

     end if;

end function;


intrinsic SolvableLieAlgebra( F::Fld, dim::RngIntElt, no::RngIntElt : pars:= [] ) -> AlgLie
{The solvable Lie algebra of dimension dim over the field F, with number no in the classification.}


    require dim in [2,3,4] : "dim has to be between 2 and 4.";

    if dim eq 2 then
       require no le 2 : "There are only two classes of solvable Lie algebras of dimension 2.";
       
       if no eq 1 then
          return L2_1( F );
       else
          return L2_2(F);
       end if;

    elif dim eq 3 then
       require no le 4 : "There are only four classes of solvable Lie algebras of dimension 3.";

       if no in [3,4] then 
          require #pars eq 1 : "For this Lie algebra one parameter is required.";      end if;

       case no:
         when 1: return L3_1( F );
         when 2: return L3_2( F );
         when 3: return L3_3( F, pars[1] );
         when 4: return L3_4( F, pars[1] );
       end case;

    elif dim eq 4 then
       require no le 14 : "There are only fourteen classes of solvable Lie algebras of dimension 4.";

       if no in [3,9,10,13,14] then
          require #pars eq 1 : "For this Lie algebra one parameter is required.";      elif no in [6,7,11]  then
          require #pars eq 2 : "For this Lie algebra two parameters are required.";
          if no eq 11 then
             require Characteristic(F) eq 2: "This Lie algebra is only defined over a field of characteristic 2.";
          end if;
       end if;

      
   
       case no:
         when 1: return L4_1( F );
         when 2: return L4_2( F );
         when 3: return L4_3( F, pars[1] );
         when 4: return L4_4( F );
         when 5: return L4_5( F );
         when 6: return L4_6( F, pars[1], pars[2] );
         when 7: return L4_7( F, pars[1], pars[2] );
         when 8: return L4_8( F );
         when 9: return L4_9( F, pars[1] );
         when 10: return L4_10( F, pars[1] );
         when 11: return L4_11( F, pars[1], pars[2] );
         when 12: return L4_12( F );
         when 13: return L4_13( F, pars[1] );
         when 14: return L4_14( F, pars[1] );
       
       end case;

    end if;

end intrinsic;



intrinsic IdDataSLAC( L::AlgLie ) -> MonStgElt, SeqEnum, Map
{Here L has to be a solvable Lie algebra of dimension 2,3, or 4. This function
returns the name of L (as it appears in the classification), a sequence of
parameters, and an isomorphism from L to the isomorphic Lie algebra in the
classification} 

     n:= Dimension( L );

     require n in [2,3,4] : "L has to be of dimension 2, 3, or 4.";

     require IsSolvable( L ) : "L has to be a solvable Lie algebra.";

     return id_data( L );

end intrinsic;


intrinsic AllSolvableLieAlgebras( F::Fld, dim::RngIntElt ) -> SeqEnum
{All solvable Lie algebras of dimension dim over the finite field F}

        require IsFinite( F ) : "F has to be a finite field.";

        require dim in [2,3,4] : "dim has to be 2, 3, or 4.";

        if dim eq 2 then
           list:= [ ];
           Append( ~list, L2_1( F ) );
           Append( ~list, L2_2(F) );
           return list;
        elif dim eq 3 then

           list:= [ ];
           Append( ~list, L3_1(F) );
           Append( ~list, L3_2(F) );
           for a in F do
               Append( ~list, L3_3( F, a ) );
           end for;
           p:= Characteristic( F );
           aa:= [ Zero(F), One(F) ];
           if p gt 2 then
              Append( ~aa, PrimitiveElement(F) );
           end if;

           for a in aa do
               Append( ~list, L3_4( F, a ) );
           end for;

        elif dim eq 4 then
           list := [ ];
           Append( ~list, L4_1(F) );
           Append( ~list, L4_2(F) );
           for a in F do
               Append( ~list, L4_3( F, a ) );
           end for;           
           Append( ~list, L4_4(F) );
           Append( ~list, L4_5(F) );
           for a in F do
               for b in F do
                   Append( ~list, L4_6(F,a,b) );
               end for;
           end for;  
           for a in F do
               Append( ~list, L4_7( F, a, a ) );
           end for;         

           q:= #F;
           m:= q mod 6;
           if IsOdd( q ) then
              a:= PrimitiveElement( F );
              if m eq 1 then
                 Append( ~list, L4_7( F, a^0, Zero(F) ) );
                 Append( ~list, L4_7( F, a, Zero(F) ) );
                 Append( ~list, L4_7( F, a^2, Zero(F) ) );
              else
                 Append( ~list, L4_7( F, One(F), Zero(F) ) );
              end if;
              Append( ~list, L4_7( F, Zero(F), One(F) ) );
              Append( ~list, L4_7( F, Zero(F), a ) );
           else
              if m eq 4 then
                 a:= PrimitiveElement( F );
                 Append( ~list, L4_7( F, a^0, Zero(F) ) );
                 Append( ~list, L4_7( F, a, Zero(F) ) );
                 Append( ~list, L4_7( F, a^2, Zero(F) ) );
              else
                 Append( ~list, L4_7( F, One(F), Zero(F) ) );
              end if;
              Append( ~list, L4_7( F, Zero(F), One(F) ) );
           end if;

           Append( ~list, L4_8( F ) );
    
           // for M9 we let b be the smallest power of the primitive root
           // such that T^2-T-b has no roots in F
           a:= PrimitiveElement( F );
           FF := PolynomialRing( F ); T := FF.1;
           for i in [1..q-1] do
               ff:= Factorization( T^2-T-a^i );
               if #ff eq 1 and ff[1][2] eq 1 then
                  Append( ~list, L4_9( F, a^i ) );
                  break;
               end if;
           end for;

           if IsEven( q ) then
              Append( ~list, L4_11( F, One(F), Zero(F) ) );
           end if;
           Append( ~list, L4_12( F ) );

           for a in F do
               Append( ~list, L4_13( F, a ) );
           end for; 

           if IsEven( q ) then
              Append( ~list, L4_14( F, One(F) ) );
           else
              Append( ~list, L4_14( F, One(F) ) );
              Append( ~list, L4_14( F, PrimitiveElement(F) ) );              
           end if;
             

        end if;
        return list;

end intrinsic;



intrinsic MatrixOfIsomorphism( f::Map ) -> AlgMatElt
{The matrix of the isomorphism f, as obtained by IdDataSLAC.}

     m:= [ ];
     M:= Domain(f);
     for i in [1..Dimension(M)] do
         Append( ~m, Eltseq( f(M.i) ) );
     end for;
     return Matrix( BaseRing( M ), m );

end intrinsic; 

//============================================================================
//
//       Nilpotent Lie algebras (dim leq 6):
//
//====================================dim 3====================================

L31:= function( F )

   S:= [ <1,2,1,0> ];
   comp_tab( ~S );
   return LieAlgebra< F, 3 | S >;

end function;

L32:= function( F )

   S:= [ <1,2,3,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 3 | S >;

end function;

//===================================dim 4====================================

L41:= function( F )

   S:= [ <1,2,1,0> ];
   comp_tab( ~S );
   return LieAlgebra< F, 4 | S >;

end function;

L42:= function( F )

   S:= [ <1,2,3,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 4 | S >;

end function;

L43:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 4 | S >;

end function;

//====================================dim5===================================

L51:= function( F )

   S:= [ <1,2,1,0> ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

L52:= function( F )

   S:= [ <1,2,3,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

L53:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

L54:= function( F )

   S:= [ <1,2,5,1>, <3,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

L55:= function( F )

   S:= [ <1,2,3,1>, <1,3,5,1>, <2,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

L56:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,3,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

L57:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

L58:= function( F )

   S:= [ <1,2,4,1>, <1,3,5,1>  ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

L59:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <2,3,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 5 | S >;

end function;

//=================================== dim6===============================

L61:= function( F )

   S:= [ <1,2,1,0> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L62:= function( F )

   S:= [ <1,2,3,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L63:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L64:= function( F )

   S:= [ <1,2,5,1>, <3,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L65:= function( F )

   S:= [ <1,2,3,1>, <1,3,5,1>, <2,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L66:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,3,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L67:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L68:= function( F )

   S:= [ <1,2,4,1>, <1,3,5,1>  ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L69:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <2,3,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L610:= function( F )

   S:= [ <1,2,3,1>, <1,3,6,1>, <4,5,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L611:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,6,1>, <2,3,6,1>, <2,5,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L612:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,6,1>, <2,5,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L613:= function( F )

   S:= [ <1,2,3,1>, <1,3,5,1>, <2,4,5,1>, <1,5,6,1>, <3,4,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L614:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,3,5,1>, <2,5,6,1>, <3,4,6,-1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L615:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,3,5,1>, <1,5,6,1>, <2,4,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L616:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,5,6,1>, <3,4,6,-1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L617:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <1,5,6,1>, <2,3,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L618:= function( F )

   S:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <1,5,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L619:= function( F, a )

   S:= [ <1,2,4,1>, <1,3,5,1>, <2,4,6,1>, <3,5,6,a> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L620:= function( F )

   S:= [ <1,2,4,1>, <1,3,5,1>, <1,5,6,1>, <2,4,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L621:= function( F, a )

   S:= [ <1,2,3,1>, <1,3,4,1>, <2,3,5,1>, <1,4,6,1>, <2,5,6,a> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L622:= function( F, a )

   S:= [ <1,2,5,1>, <1,3,6,1>, <2,4,6,a>, <3,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L623:= function( F )

   S:= [ <1,2,3,1>, <1,3,5,1>, <1,4,6,1>, <2,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L624:= function( F, a )

   S:= [ <1,2,3,1>, <1,3,5,1>, <1,4,6,a>, <2,3,6,1>, <2,4,5,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L625:= function( F )

   S:= [ <1,2,3,1>, <1,3,5,1>, <1,4,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

L626:= function( F )

   S:= [ <1,2,4,1>, <1,3,5,1>, <2,3,6,1> ];
   comp_tab( ~S );
   return LieAlgebra< F, 6 | S >;

end function;

//========================================================================

// Some utilities for checking, to be removed later:

chck:= function( f )

   K:= Domain(f);
   L:= Codomain(f);
   for i in [1..Dimension(K)] do
       for j in [1..Dimension(K)] do
           if not f(K.i*K.j) eq f(K.i)*f(K.j) then
              print i,j;
              return false;
           end if;
       end for;
   end for;
   return true;

end function;

mess_up:= function( L )

   d:= Dimension(L);
   F:= BaseField(L);
   set:= [ ];
   if not IsFinite( F ) then
      set:= [ F!x : x in [-10..10] ];
      //set:= [1,0];
   else
      set:= F;
   end if;

   m:= ScalarMatrix( d, Zero(F) );
   while Rank(m) lt d do
         for i in [1..d] do
             for j in [1..d] do
                 m[i][j]:= Random( set );
             end for;
         end for;
   end while;

   V:= RModule( F, d );
   W:= RModuleWithBasis( [ V!m[i] : i in [1..d] ] );
   T:= [ ];
   for i in [1..d] do
       for j in [1..d] do
           x:= V!Eltseq( (L!m[i]*L!m[j]) );
           cf:= Coordinates( W, V!Eltseq(x) );
           for k in [1..d] do
               if not IsZero( cf[k] ) then
                  Append( ~T, <i,j,k,cf[k]> );
               end if;
           end for;
        end for;
   end for;

   return LieAlgebra< F, d | T >;

end function;

liealg_hom:= function( K, L, p, i )

     return hom< K -> L | [ <p[k],i[k]> : k in [1..#p] ] >;

end function;

class_dim_le4:= function( L )

    // finds an isomorphism of the nilpotent Lie algebra L of dim <= 4,
    // to a "normal form".

    if Dimension(L) eq 3 then
       if IsCommutative( L ) then
          return [3,1], liealg_hom( L, L, Basis(L), Basis(L) );
       else
          C:= Centre(L);
          for i in [1..3] do
              if not L.i in C then 
                 x:= L.i; break;
              end if;
          end for;

          C:= sub< L | [ x, L!C.1 ] >;
          for i in [1..3] do
              if not L.i in C then 
                 y:= L.i; break;
              end if;
          end for;

          T:= [ <1,2,3,1> ]; comp_tab( ~T );
          K:= LieAlgebra< BaseField(L), 3 |  T >;
          return [3,2], liealg_hom( L, K, [x,y,x*y], Basis(K) );
       end if; 
    elif Dimension(L) eq 4 then
       if IsCommutative(L) then
          return [4,1], liealg_hom( L, L, Basis(L), Basis(L) );
       else
          C:= Centre(L);
          if Dimension(C) eq 2 then
             for i in [1..4] do
                 if not L.i in C then 
                    x:= L.i; break;
                 end if;
             end for;

             C1:= sub< L | [ C.1, C.2, x ] >;
             for i in [1..4] do
                 if not L.i in C1 then 
                    y:= L.i; break;
                 end if;
             end for;

             z:= x*y;
             A:= sub< C | [C!z] >;
             if C.1 in A then
                u:= L!C.2; 
             else
                u:= L!C.1;
             end if;

             T:= [ <1,2,3,1> ]; comp_tab( ~T );
             K:= LieAlgebra< BaseField(L), 4 |  T >;
             return [4,2], liealg_hom( L, K, [x,y,z,u], Basis(K) );
          elif Dimension(C) eq 1 then

             D:= L*L;
             b:= [L!D.1,L!D.2];
             D:= sub< L | b >;
             cc:= [ ];
             for i in [1..4] do
                 if not L.i in D then 
                    Append( ~cc, L.i );
                    Append( ~b, L.i );
                    D:= sub< L | b>; 
                 end if;
             end for;

             z:= cc[1]*cc[2];
             if cc[1]*z ne Zero(L) then
                x:= cc[1]; y:= cc[2];
             else 
                x:= cc[2]; y:= cc[1];
             end if;

             z:= x*y; u:= x*z;

             // we have to change y to make sure that [x,y]=z, and
             // [y,u]=0.
             V:= RModule( BaseField(L), Dimension(L) );
             W:= RModuleWithBasis( [ V!Eltseq( u ) ] );
             a:= Coordinates( W, V!Eltseq( y*z ) )[1];
             y:= -a*x+y;

             T:= [ <1,2,3,1>, <1,3,4,1> ]; comp_tab( ~T );
             K:= LieAlgebra< BaseField(L), 4 |  T >;
             return [4,3], liealg_hom( L, K, [x,y,z,u], Basis(K) );

          end if;
       end if;
    end if;

end function;

skew_symm_NF:= function( V, f )

    // here V is a vector space, and f : VxV -> F a skew-symmetric
    // bilinear form; we compute a basis of V such that f has standard form.

    b:= Basis(V);
    dim:= Dimension(V);
    found:= false;
    for i in [1..dim] do
        if found then break; end if;
        for j in [i+1..dim] do
            c:= f(<b[i],b[j]>);
            if c ne 0 then
               u:= [b[i]]; v:= [b[j]/c];
               found:= true; break;
            end if;
        end for;
    end for;

    done:= false;
    while not done do
          // consider the linear map T: V --> V defined by
          // T(w) = \sum_i f(w,v[i])u[i] - f(w,u[i])v[i],
          // then T is projection onto the space spanned by the elts in u,v.
          // set U = (1-T)V; then T is zero on U, and V is the direct 
          // sum of U and the space spanned by u,v. We compute U.
          W:= RModule( BaseField(V), dim );
          bU:= [ ];
          for x in b do
              w:= &+[ f(<x,v[i]>)*u[i]-f(<x,u[i]>)*v[i] : i in [1..#u] ];
              w:= x-w;
              if not w eq Zero(V) then
                 if #bU eq 0 then
                    Append( ~bU, w );
                    sp:= RModuleWithBasis( [ W!Eltseq( w ) ] );
                 else
                    if not W!Eltseq(w) in sp then
                       Append( ~bU, w );
                       sp:= RModuleWithBasis( [W!Eltseq(a) : a in bU ] );
                    end if;
                 end if;
              end if;
          end for;
 
          found:= false;
          for i in [1..#bU] do
              if found then break; end if;
              for j in [i+1..#bU] do
                  c:= f(<bU[i],bU[j]>);
                  if c ne 0 then
                     Append( ~u, bU[i] ); Append( ~v, bU[j]/c );
                     found:= true; break;
                  end if;
              end for;
          end for;
          if not found then
             done:= true;
             bb:= [ ];
             for i in [1..#u] do
                 Append( ~bb, u[i] );          
                 Append( ~bb, v[i] );          
             end for;
             bb cat:= bU;
          elif 2*#u eq dim then
             done:= true;
             bb:= [ ];
             for i in [1..#u] do
                 Append( ~bb, u[i] );          
                 Append( ~bb, v[i] );          
             end for;
          end if;
    end while;

    return bb;

end function;



class_dim_5:= function( K )

    if IsCommutative(K) then 
       return [5,1], liealg_hom( K, K, Basis(K), Basis(K) );
    end if;

    F:= BaseField( K );

    // see if there is an abelian component (necessarily of dim 1)
    C:= Centre( K );
    D:= K*K;
    ind:= 0;
    for i in [1..Dimension(C)] do
        if not C.i in D then
           ind:= i;
           break;
        end if;
    end for;

    if ind gt 0 then

       bL:= [ K!u : u in Basis(D) ];
       bsp:= bL cat [ K!C.ind ];
       sp:= sub< K | bsp >;  // note that this is a subalgebra!
       for i in [1..Dimension(K)] do
           if not K.i in sp then
              Append( ~bL, K.i );
              Append( ~bsp, K.i );
              sp:=  sub< K | bsp >;
           end if;
       end for;

       L,f:= sub< K | bL >;
       bL:= [ f(L.i) : i in [1..Dimension(L) ] ];
       bL cat:= [ K!C.ind ];
       V:= RModule( F, Dimension(K) );
       W:= RModuleWithBasis( [ V!Eltseq( bL[i] ) : i in [1..#bL] ] );

       // so now bL is a basis of K, the first n-1 elements form 
       // a basis of an ideal, the last element of an abelian ideal.
       // We have an isomorphism of K to the direct sum of L with a
       // 1-dim ideal; write x\in K on the basis bL. 

       type, tau:= class_dim_le4( L );
       M:= Codomain( tau );

       T:= [ ];
       for i in [1..Dimension(M)] do
           for j in [1..Dimension(M)] do
               c:= Eltseq( M.i*M.j );
               for k in [1..#c] do
                   if not IsZero(c[k]) then
                      Append( ~T, <i,j,k,c[k]> );
                   end if;
               end for;
           end for;
       end for;

       N:= LieAlgebra< F, 5 | T >;

       imgs:= [ ];
       for x in Basis(K) do
           cx:= Coordinates( W, V!Eltseq( x ) );
           y:= Eltseq( tau( L![ cx[i] : i in [1..#cx-1] ] ) );
           Append( ~y, cx[ #cx ]  );
           Append( ~imgs, N!y );
       end for;

       return [5,type[2]], liealg_hom( K, N, Basis(K), imgs );

    end if;

    // if there are no central components, then we look at the 
    // cocycle we get by dividing by the centre, and so on.

    C:= Centre(K);
    L,p:= quo< K | C >;
    s:= Inverse(p);

    coc1:= map< CartesianProduct( L, L ) -> C | 
                                v :-> s(v[1])*s(v[2])-s(v[1]*v[2]) >;   

    type, tau:= class_dim_le4( L );
    taui:= Inverse( tau );
    M:= Codomain( tau );
    coc2:= map< CartesianProduct( M, M ) -> C |
                                v :->  coc1( <taui(v[1]),taui(v[2])> ) >;

    // now we need to map coc2 to normal form, according to the type of M 

    if type eq [4,1] then
    
       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
        
       bM:= skew_symm_NF( M, coc21 );

       V:= RModule( F, 4 );
       W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
       
       T:= [ <1,2,5,1>, <3,4,5,1> ]; comp_tab( ~T );
       N:= LieAlgebra< F, 5 | T >;

       imgs:= [ ];
       for x in Basis(K) do
           // the coordinate of the central part of x:
           // this will be the coordinate of the central part of the 
           // image of x. 
           cz:= Coordinates( C, x-s(p(x)) )[1];           
           cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
           Append( ~cx, cz );
           Append( ~imgs, N!cx );
       end for;

       return [5,4], liealg_hom( K, N, Basis(K), imgs );

    elif type eq [4,2] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;

       a:= coc21( <M.1,M.3> );
       b:= coc21( <M.1,M.4> );
       c:= coc21( <M.2,M.3> );
       d:= coc21( <M.2,M.4> );

       mat:= IdentityMatrix( F, 4 ); 

       if IsZero( a ) then
          // c is non zero
          m:= IdentityMatrix( F, 4 );
          m[2][1]:= 1;
          mat:= m;
          a:= c; b:= b+d; 
       end if;

       m:= IdentityMatrix( F, 4 );
       m[1,1]:= 1/a;
       m[1,2]:= -c;
       m[2,2]:= a;
       m[4,4]:= 1/(a*d-b*c);
       m[3,4]:= -m[4,4]*b/a;
       mat:= mat*m;

       V:= RModule( F, 4 );
       mat:= Transpose( mat );
       W:= RModuleWithBasis( [ V!Eltseq(mat[i]) : i in [1,2,3,4] ] );

       T:= [ <1,2,3,1>, <1,3,5,1>, <2,4,5,1> ]; comp_tab( ~T );
       N:= LieAlgebra< F, 5 | T >;

       imgs:= [ ];
       for x in Basis(K) do
           cz:= Coordinates( C, x-s(p(x)) )[1];           
           cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
           Append( ~cx, cz );

           // effectively subtract a coboundary (i.e., apply one further
           // isomorphism): 
           // Here we have (in the normal form Lie algebra)
           // [x1,x2]=x3. Hence c(x1,x2)=1, rest 0 is a coboundary.
           // The isomorphism corresponding to the subtraction of c
           // from the cocycle, subtracts coc21( x1, x2 )*x5 from
           // the element. (Rather vague comment...).
           cf:= coc21( <M!mat[1],M!mat[2]> );
           cx[5]:= cx[5] - cf*cx[3];

           Append( ~imgs, N!cx );
       end for;

       return [5,5], liealg_hom( K, N, Basis(K), imgs );           

    elif type eq [4,3] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;

       a:= coc21( <M.1,M.4> );
       b:= coc21( <M.2,M.3> );

       if not IsZero(b) then

          T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,3,5,1> ]; comp_tab( ~T );
          N:= LieAlgebra< F, 5 | T >;
          
          imgs:= [ ];
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) )[1];           
              cx:= Eltseq( tau( p(x) ) );
              cf:= a/b;
              cx[1] *:= cf; cx[2]*:= cf; cx[3]*:= cf^2; cx[4] *:= cf^3;
              Append( ~cx, cf^4*cz/a );
              
              // take care of the coboundary...
              c1:= coc21( <cf^-1*M.1,cf^-1*M.2> );
              cx[5]:= cx[5] - c1*(cf^4/a)*cx[3];

              c1:= coc21( <cf^-1*M.1,cf^-2*M.3> );
              cx[5]:= cx[5] - c1*(cf^4/a)*cx[4];

              Append( ~imgs, N!cx );
          end for;
          return [5,6], liealg_hom( K, N, Basis(K), imgs );

       else

          T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1> ]; comp_tab( ~T );
          N:= LieAlgebra< F, 5 | T >;
          
          imgs:= [ ];
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) )[1];           
              cx:= Eltseq( tau( p(x) ) );
              Append( ~cx, cz/a );
              
              // take care of the coboundary...
              cf:= coc21( <M.1,M.2> );
              cx[5]:= cx[5] - cf/a*cx[3];

              cf:= coc21( <M.1,M.3> );
              cx[5]:= cx[5] - cf/a*cx[4];

              Append( ~imgs, N!cx );
          end for;
          return [5,7], liealg_hom( K, N, Basis(K), imgs );

       end if;

    elif type eq [ 3, 1 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       coc22:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[2] >;
       bM:= skew_symm_NF( M, coc21 );

       b:= coc22(<bM[1],bM[3]>); c:= coc22(<bM[2],bM[3]>);
       if IsZero(b) then
          // change the basis bM so that it becomes nonzero.
          bM[1]:= bM[1]+bM[2];
          b:= coc22(<bM[1],bM[3]>); c:= coc22(<bM[2],bM[3]>);
       end if;

       // change the basis so that c becomes zero... 
       bM[2]:= bM[2]-c/b*bM[1];

       V:= RModule( F, 3 );
       W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
       
       a:= coc22(<bM[1],bM[2]>);
       b:= coc22(<bM[1],bM[3]>);

       T:= [ <1,2,4,1>, <1,3,5,1> ]; comp_tab( ~T );
       N:= LieAlgebra< F, 5 | T >;

       imgs:= [ ];
       for x in Basis(K) do
           // the coordinate of the central part of x:
           cz:= Coordinates( C, x-s(p(x)) );           
           cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );

           // account for the base change in the centre:
           cz[2]:= -cz[1]*a/b+cz[2]/b;
           cx cat:= cz;
           Append( ~imgs, N!cx );
       end for;

       return [5,8], liealg_hom( K, N, Basis(K), imgs );

    elif type eq [ 3, 2 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       coc22:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[2] >;

       m:= Matrix( [[coc21(<M.1,M.3>),coc21(<M.2,M.3>)],
                    [coc22(<M.1,M.3>),coc22(<M.2,M.3>)] ] );

       m:= m^-1;
       mt:= Transpose(m);

       T:= [ <1,2,3,1>, <1,3,4,1>, <2,3,5,1> ]; comp_tab( ~T );
       N:= LieAlgebra< F, 5 | T >;

       c1:= mt[1,1]*coc21(<M.1,M.2>)+mt[2,1]*coc22(<M.1,M.2>);
       c2:= mt[1,2]*coc21(<M.1,M.2>)+mt[2,2]*coc22(<M.1,M.2>);
          
       imgs:= [ ];
       for x in Basis(K) do
           cz:= Coordinates( C, x-s(p(x)) );           
           cx:= Eltseq( tau( p(x) ) );
           cx cat:= Eltseq( Vector(cz)*mt );
              
           // take care of the coboundary...

           cx[4]:= cx[4] - c1*cx[3];
           cx[5]:= cx[5] - c2*cx[3];
           Append( ~imgs, N!cx );
       end for;
       return [5,9], liealg_hom( K, N, Basis(K), imgs );


    end if;


end function;

comp_mat:= function( x, y, det )

    if IsZero(y) then
       c:= 0; a:= 1/x; d:= x*det;b:= 0;
    else
       a:= -y*det; c:= -y*det; d:= x*det; b:= (1+x*y*det)/y;
    end if;
    return a,b,c,d;

end function;


class_dim_6:= function( K )

    if IsCommutative(K) then 
       return [6,1], liealg_hom( K, K, Basis(K), Basis(K) );
    end if;

    F:= BaseField( K );

    // see if there is an abelian component (necessarily of dim 1)
    C:= Centre( K );
    D:= K*K;
    ind:= 0;
    for i in [1..Dimension(C)] do
        if not C.i in D then
           ind:= i;
           break;
        end if;
    end for;

    if ind gt 0 then

       bL:= [ K!u : u in Basis(D) ];
       bsp:= bL cat [ K!C.ind ];
       sp:= sub< K | bsp >;  // note that this is a subalgebra!
       for i in [1..Dimension(K)] do
           if not K.i in sp then
              Append( ~bL, K.i );
              Append( ~bsp, K.i );
              sp:=  sub< K | bsp >;
           end if;
       end for;

       L,f:= sub< K | bL >;
       bL:= [ f(L.i) : i in [1..Dimension(L) ] ];
       bL cat:= [ K!C.ind ];
       V:= RModule( F, Dimension(K) );
       W:= RModuleWithBasis( [ V!Eltseq( bL[i] ) : i in [1..#bL] ] );

       // so now bL is a basis of K, the first n-1 elements form 
       // a basis of an ideal, the last element of an abelian ideal.
       // We have an isomorphism of K to the direct sum of L with a
       // 1-dim ideal; write x\in K on the basis bL. 

       type, tau:= class_dim_5( L );
       M:= Codomain( tau );

       T:= [ ];
       for i in [1..Dimension(M)] do
           for j in [1..Dimension(M)] do
               c:= Eltseq( M.i*M.j );
               for k in [1..#c] do
                   if not IsZero(c[k]) then
                      Append( ~T, <i,j,k,c[k]> );
                   end if;
               end for;
           end for;
       end for;

       N:= LieAlgebra< F, 6 | T >;

       imgs:= [ ];
       for x in Basis(K) do
           cx:= Coordinates( W, V!Eltseq( x ) );
           y:= Eltseq( tau( L![ cx[i] : i in [1..#cx-1] ] ) );
           Append( ~y, cx[ #cx ]  );
           Append( ~imgs, N!y );
       end for;

       return [6,type[2]], liealg_hom( K, N, Basis(K), imgs );

    end if;

    // if there are no central components, then we look at the 
    // cocycle we get by dividing by the centre, and so on.

    C:= Centre(K);
    L,p:= quo< K | C >;
    s:= Inverse(p);

    coc1:= map< CartesianProduct( L, L ) -> C | 
                                v :-> s(v[1])*s(v[2])-s(v[1]*v[2]) >;   

    if Dimension(L) le 4 then
       type, tau:= class_dim_le4( L );
    else
       type, tau:= class_dim_5( L );
    end if;
    taui:= Inverse( tau );
    M:= Codomain( tau );
    coc2:= map< CartesianProduct( M, M ) -> C |
                                v :->  coc1( <taui(v[1]),taui(v[2])> ) >;

    // now we need to map coc2 to normal form, according to the type of M 

    if type eq [ 5, 2 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;

       bM:= Basis(M);

       // we change the basis bM so that the cocycle is in "normal form":

       a:= coc21(<M.1,M.3>); d:= coc21(<M.2,M.3>);
 
       a11, a21, a12, a22:= comp_mat( a, d, One(F) );

       v1:= a11*bM[1]+a21*bM[2];
       v2:= a12*bM[1]+a22*bM[2];
       bM[1]:= v1; bM[2]:= v2;

       b:= coc21(<bM[1],bM[4]>); c:= coc21(<bM[1],bM[5]>);
       bM[4]:= bM[4]-b*bM[3];
       bM[5]:= bM[5]-c*bM[3];

       e:= coc21(<bM[2],bM[4]>); f:= coc21(<bM[2],bM[5]>); 
       g:= coc21(<bM[4],bM[5]>);

       if not (IsZero(e) and IsZero(f)) then
          a44, a54, a45, a55:= comp_mat( e, f, 1/g );
          v1:= a44*bM[4]+a54*bM[5];
          v2:= a45*bM[4]+a55*bM[5];
          bM[4]:= v1; bM[5]:= v2;

          T:= [ <1,2,3,1>, <1,3,6,1>, <4,5,6,1> ]; comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;
          
          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );
              
              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[3];

              // isomorphism to M_2 (see paper):
              cx[5]:= cx[5]-cx[2];
              Append( ~imgs, N!cx );
          end for;
          return [6,10], liealg_hom( K, N, Basis(K), imgs );

       else

          bM[4]:= bM[4]/g;
          T:= [ <1,2,3,1>, <1,3,6,1>, <4,5,6,1> ]; comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;
          
          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );
              
              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[3];
              Append( ~imgs, N!cx );
          end for;
          return [6,10], liealg_hom( K, N, Basis(K), imgs );

       end if;
    elif type eq [5,3] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       bM:= Basis(M);

       // we change the basis bM so that the cocycle is in "normal form":

       a:= coc21(<M.1,M.4>);

       bM[2]:= bM[2]/a; bM[3]:= bM[3]/a; bM[4]:= bM[4]/a;
       b:= coc21(<bM[1],bM[5]>); d:= coc21(<bM[2],bM[5]>);
       bM[1]:= bM[1]-b/d*bM[2];
       bM[5]:= bM[5]/d;

       c:= coc21( <bM[2],bM[3]> );
       if not IsZero(c) then
          T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,6,1>, <2,3,6,1>, <2,5,6,1> ]; 
          comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;
          
          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          c2:= coc21(<bM[1],bM[3]>);
          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );
              
              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[3]-c2*cx[4];

              // make c equal to 1...
              cx[1]:= cx[1]/c; cx[2]:= cx[2]/c; cx[3]:= cx[3]/c^2;
              cx[4]:= cx[4]/c^3; cx[5]:= cx[5]/c^3; cx[6]:= cx[6]/c^4;
              Append( ~imgs, N!cx );
          end for;
          return [6,11], liealg_hom( K, N, Basis(K), imgs );

       else

          T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,6,1>, <2,5,6,1> ]; 
          comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;
          
          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          c2:= coc21(<bM[1],bM[3]>);
          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );
              
              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[3]-c2*cx[4];
              Append( ~imgs, N!cx );
          end for;
          return [6,12], liealg_hom( K, N, Basis(K), imgs );

       end if;

    elif type eq [5,5] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       bM:= Basis(M);

       // we change the basis bM so that the cocycle is in "normal form":

       b:= coc21(<M.1,M.5>);
       bM[2]:= bM[2]/b; bM[3]:= bM[3]/b; bM[5]:= bM[5]/b;
       a:= coc21(<bM[1],bM[4]>); c:= coc21(<bM[2],bM[3]>);
       bM[1]:= bM[1]-a*bM[3]; bM[2]:= bM[2]+c*bM[4];

       imgs:= [ ];
       c1:= coc21(<bM[1],bM[2]>);
       c2:= coc21(<bM[1],bM[3]>);
       d:= coc21(<bM[2],bM[4]>)-c2;
       T:= [ <1,2,3,1>, <1,3,5,1>, <2,4,5,1>, <1,5,6,1>, <3,4,6,1> ]; 
       comp_tab( ~T );
       N:= LieAlgebra< F, 6 | T >;

       V:= RModule( F, 5 );
       W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
       for x in Basis(K) do
           cz:= Coordinates( C, x-s(p(x)) );           
           cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
           cx cat:= Eltseq( cz );
              
           // take care of the coboundary...
           cx[6]:= cx[6] - c1*cx[3]-c2*cx[5];
           
           if not IsZero(d) then
              // map it to 1:
              cx[1]:= cx[1]/d; cx[3]:= cx[3]/d; cx[4]:= cx[4]/d^2;
              cx[5]:= cx[5]/d^2; cx[6]:= cx[6]/d^3; 
              // make isom with the Lie alg where d=0:
              cx[5]:= cx[5]+(cx[2]+cx[3])/2;
              cx[4]:= cx[4]+cx[1]/2;
              cx[3]:= cx[3]+cx[2];
           end if;
           Append( ~imgs, N!cx );
       end for;
       return [6,13], liealg_hom( K, N, Basis(K), imgs );
       
    elif type eq [ 5, 6 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       bM:= Basis(M);

       // we change the basis bM so that the cocycle is in "normal form":

       a:= coc21(<M.1,M.5>); 
       b:= coc21(<M.2,M.3>)-coc21(<M.1,M.4>); 
       c:= coc21(<M.2,M.5>);

       if not IsZero(c) then
          a21:= -a/c; a42:= -(a^2/c^2+b/c)/2;
          bM[1]:= bM[1]+a21*bM[2];
          bM[2]:= bM[2]+a42*bM[4];
          bM[3]:= bM[3]+a42*bM[5];
          bM[4]:= bM[4]+a21*bM[5];
          c:= coc21(<bM[2],bM[5]>);

          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          c2:= coc21(<bM[1],bM[3]>);
          c3:= coc21(<bM[1],bM[4]>);

          T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,3,5,1>, <2,5,6,1>, 
                <3,4,6,-1> ]; 
          comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;

          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );
              
              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[3]-c2*cx[4]-c3*cx[5];
           
              // make c=1;
              cx[6]:= cx[6]/c;
              Append( ~imgs, N!cx );
          end for;
          return [6,14], liealg_hom( K, N, Basis(K), imgs );
       else

          a21:= b/(2*a); 
          bM[1]:= bM[1]+a21*bM[2];
          bM[4]:= bM[4]+a21*bM[5];

          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          c2:= coc21(<bM[1],bM[3]>);
          c3:= coc21(<bM[1],bM[4]>);

          T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,3,5,1>, <1,5,6,1>, 
                <2,4,6,1> ]; 
          comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;

          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );
              
              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[3]-c2*cx[4]-c3*cx[5];

              // make a=1:
              cx[6]:= cx[6]/a;
           
              Append( ~imgs, N!cx );
          end for;
          return [6,15], liealg_hom( K, N, Basis(K), imgs );
       end if;

    elif type eq [ 5, 7 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       bM:= Basis(M);

       // we change the basis bM so that the cocycle is in "normal form":

       a:= coc21(<M.1,M.5>); 
       b:= coc21(<M.2,M.3>);
       c:= coc21(<M.2,M.5>);

       if not IsZero(c) then
          a21:= -a/c; a42:= -(b/c)/2;
          bM[1]:= bM[1]+a21*bM[2];
          bM[2]:= bM[2]+a42*bM[4];
          bM[3]:= bM[3]+a42*bM[5];

          c:= coc21(<bM[2],bM[5]>);

          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          c2:= coc21(<bM[1],bM[3]>);
          c3:= coc21(<bM[1],bM[4]>);

          T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <2,5,6,1>, <3,4,6,-1> ]; 
          comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;

          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          for x in Basis(K) do
              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );
              
              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[3]-c2*cx[4]-c3*cx[5];
           
              // make c=1;
              cx[6]:= cx[6]/c;
              Append( ~imgs, N!cx );
          end for;
          return [6,16], liealg_hom( K, N, Basis(K), imgs );
       else

          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          c2:= coc21(<bM[1],bM[3]>);
          c3:= coc21(<bM[1],bM[4]>);

          if not IsZero(b) then   
             T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <1,5,6,1>, <2,3,6,1> ]; 
             comp_tab( ~T );
             N:= LieAlgebra< F, 6 | T >;
             tt:= [ 6, 17 ];
          else
             T:= [ <1,2,3,1>, <1,3,4,1>, <1,4,5,1>, <1,5,6,1> ]; 
             comp_tab( ~T );
             N:= LieAlgebra< F, 6 | T >;
             tt:= [ 6, 18 ];
          end if;

          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );

          b:= b/a; //(we will divide by a, also changing b)

          for x in Basis(K) do

              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );

              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[3]-c2*cx[4]-c3*cx[5];

              // make a=1:
              cx[6]:= cx[6]/a;
 
              if not IsZero(b) then
                 // make it 1:
                 cx[1]:= cx[1]/b; cx[2]:= cx[2]/b^2; cx[3]:= cx[3]/b^3;
                 cx[4]:= cx[4]/b^4; cx[5]:= cx[5]/b^5; cx[6]:= cx[6]/b^6;
              end if;
            
              Append( ~imgs, N!cx );
          end for;
          return tt, liealg_hom( K, N, Basis(K), imgs );
       end if;       

    elif type eq [ 5, 8 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       bM:= Basis(M);

       // we change the basis bM so that the cocycle is in "normal form":

       d:= coc21(<M.2,M.4>); 
       e:= coc21(<M.2,M.5>);
       f:= coc21(<M.3,M.5>);
       if not IsZero(f) then
          bM[2]:= bM[2]-e/f*bM[3];
          bM[4]:= bM[4]-e/f*bM[5];
       elif not IsZero(d) then
          bM[3]:= bM[3]-e/d*bM[2];
          bM[5]:= bM[5]-e/d*bM[4];
       else
          v:= bM[2];
          bM[2]:= bM[2]-bM[3];
          bM[3]:= bM[3]+v;
          v:= bM[4];
          bM[4]:= bM[4]-bM[5];
          bM[5]:= v+bM[5];
       end if;

       d:= coc21(<bM[2],bM[4]>);
       if not IsZero(d) then

          // make d=1:
          bM[1]:= bM[1]/d; bM[4]:= bM[4]/d; bM[5]:= bM[5]/d;
          // and a=c=0
          a:= coc21(<bM[1],bM[4]>);
          c:= coc21(<bM[2],bM[3]>);
          bM[1]:= bM[1]-a*bM[2];
          bM[3]:= bM[3]-c*bM[4];

          b:= coc21(<bM[1],bM[5]>);

          if IsZero(b) then
             f:= coc21(<bM[3],bM[5]>);
             T:= [ <1,2,4,1>, <1,3,5,1>, <2,4,6,1>, <3,5,6,f> ]; 
             comp_tab( ~T );
             N:= LieAlgebra< F, 6 | T >;

             V:= RModule( F, 5 );
             W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
             imgs:= [ ];
             c1:= coc21(<bM[1],bM[2]>);
             c2:= coc21(<bM[1],bM[3]>);
             for x in Basis(K) do

                 cz:= Coordinates( C, x-s(p(x)) );           
                 cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
                 cx cat:= Eltseq( cz );

                 // take care of the coboundary...
                 cx[6]:= cx[6] - c1*cx[4]-c2*cx[5];

                 Append( ~imgs, N!cx );
             end for;
             return [* 6, 19, f *], liealg_hom( K, N, Basis(K), imgs );

          else // i.e., b <> 0

             bM[3]:= bM[3]/b;
             bM[5]:= bM[5]/b;
             f:= coc21(<bM[3],bM[5]>);

             if not IsZero(f) then
                
                T:= [ <1,2,4,1>, <1,3,5,1>, <2,4,6,1>, <3,5,6,f> ]; 
                comp_tab( ~T );
                N:= LieAlgebra< F, 6 | T >;

                V:= RModule( F, 5 );
                W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                imgs:= [ ];
                c1:= coc21(<bM[1],bM[2]>);
                c2:= coc21(<bM[1],bM[3]>);

                for x in Basis(K) do

                    cz:= Coordinates( C, x-s(p(x)) );           
                    cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
                    cx cat:= Eltseq( cz );

                    cx[3]:= cx[3] + cx[1]/f;

                    // take care of the coboundary...
                    cx[6]:= cx[6] - c1*cx[4]-c2*cx[5];

                    Append( ~imgs, N!cx );
                end for;
                return [* 6, 19, f *], liealg_hom( K, N, Basis(K), imgs );
             else // i.e., f=0
                             
                T:= [ <1,2,4,1>, <1,3,5,1>, <1,5,6,1>, <2,4,6,1> ]; 
                comp_tab( ~T );
                N:= LieAlgebra< F, 6 | T >;

                V:= RModule( F, 5 );
                W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                imgs:= [ ];
                c1:= coc21(<bM[1],bM[2]>);
                c2:= coc21(<bM[1],bM[3]>);
                for x in Basis(K) do

                    cz:= Coordinates( C, x-s(p(x)) );           
                    cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
                    cx cat:= Eltseq( cz );

                    // take care of the coboundary...
                    cx[6]:= cx[6] - c1*cx[4]-c2*cx[5];

                    Append( ~imgs, N!cx );
                end for;
                return [ 6, 20 ], liealg_hom( K, N, Basis(K), imgs );
             end if;
          end if;
       else // i.e., d=0

          // make f=1:
          bM[1]:= bM[1]/f; bM[4]:= bM[4]/f; bM[5]:= bM[5]/f;
          // and c=0, a=1
          a:= coc21(<bM[1],bM[4]>);
          c:= coc21(<bM[2],bM[3]>);
          bM[2]:= bM[2]+c*bM[5];
          bM[2]:= bM[2]/a; bM[4]:= bM[4]/a;

          b:= coc21(<bM[1],bM[5]>);        

          T:= [ <1,2,4,1>, <1,3,5,1>, <1,5,6,1>, <2,4,6,1> ]; 
          comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;

          V:= RModule( F, 5 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          imgs:= [ ];
          c1:= coc21(<bM[1],bM[2]>);
          c2:= coc21(<bM[1],bM[3]>);
          for x in Basis(K) do

              cz:= Coordinates( C, x-s(p(x)) );           
              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= Eltseq( cz );

              // take care of the coboundary...
              cx[6]:= cx[6] - c1*cx[4]-c2*cx[5];

              if not IsZero(b) then
                 cx[2]:= cx[2]/b^2; cx[3]:= cx[3]/b; cx[4]:= cx[4]/b^2;
                 cx[5]:= cx[5]/b; cx[6]:= cx[6]/b^2;
                 cx[3]:= cx[3]+cx[1];
              end if;
              cx1:= cx;
              cx1[2]:= cx[3]; cx1[3]:= cx[2];
              cx1[4]:= cx[5]; cx1[5]:= cx[4];

              Append( ~imgs, N!cx1 );
          end for;
          return [ 6, 20 ], liealg_hom( K, N, Basis(K), imgs );

       end if;

    elif type eq [ 5, 9 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       bM:= Basis(M);

       // we change the basis bM so that the cocycle is in "normal form":

       a:= coc21(<M.1,M.4>); 
       b:= coc21(<M.1,M.5>);
       c:= coc21(<M.2,M.5>);
       if not IsZero(c) then
          bM[1]:= bM[1]-b/c*bM[2];
          bM[4]:= bM[4]-b/c*bM[5];
       elif not IsZero(a) then
          bM[2]:= bM[2]-b/a*bM[1];
          bM[5]:= bM[5]-b/a*bM[4];
       else
          v:= bM[1];
          bM[1]:= bM[1]-bM[2];
          bM[2]:= v+bM[2];
          bM[3]:= 2*bM[3];
          v:= bM[4];
          bM[4]:= 2*(bM[4]-bM[5]);
          bM[5]:= 2*(v+bM[5]);
       end if;

       a:= coc21(<bM[1],bM[4]>);
       c:= coc21(<bM[2],bM[5]>);

       T:= [ <1,2,3,1>, <1,3,4,1>, <2,3,5,1>, <1,4,6,1>, <2,5,6,c/a> ]; 
       comp_tab( ~T );
       N:= LieAlgebra< F, 6 | T >;

       V:= RModule( F, 5 );
       W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
       imgs:= [ ];
       c1:= coc21(<bM[1],bM[2]>);
       c2:= coc21(<bM[1],bM[3]>);
       c3:= coc21(<bM[2],bM[3]>);
       for x in Basis(K) do

           cz:= Coordinates( C, x-s(p(x)) );           
           cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
           cx cat:= Eltseq( cz );

           // take care of the coboundary...
           cx[6]:= cx[6] - c1*cx[3]-c2*cx[4]-c3*cx[5];

           cx[6]:= cx[6]/a;
           Append( ~imgs, N!cx );
       end for;
       return [* 6, 21, c/a *], liealg_hom( K, N, Basis(K), imgs );

    elif type eq [ 4, 1 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       coc22:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[2] >;


       bM:= skew_symm_NF( M, coc21 );

       if IsZero( coc21(<bM[3],bM[4]>) ) then
          // find a linear combination of coc21, coc22 that is nondegenerate:
          y:= coc22(<bM[1],bM[2]>); a:= coc22(<bM[1],bM[3]>);
          b:= coc22(<bM[1],bM[4]>); c:= coc22(<bM[2],bM[3]>);
          d:= coc22(<bM[2],bM[4]>); e:= coc22(<bM[3],bM[4]>);
          if IsZero( a*d-b*c ) then
             x:= 1-y;
          else
             x:= -y;
          end if;

          if IsZero(x) then
             store:= coc21;
             coc21:= map< CartesianProduct( M, M ) -> F |
                           v :-> x*coc21(v)+coc22(v) >;
             // so now coc21 has become coc22, need to make coc22 equal to
             // the old coc21 (otherwise no linger independent).
             coc22:= store;
             r:= 1; t:= 0;
          else
             coc21:= map< CartesianProduct( M, M ) -> F |
                           v :-> x*coc21(v)+coc22(v) >;
             r:= 0; t:= 1;
          end if;
          bM:= skew_symm_NF( M, coc21 );

          u:= x; v:= 1;
          // i.e., we have made a base change in the centre, corresponding 
          // to theta_1 --> u*theta_1 + v*\theta_2
          //    theta_2 --> r*theta_1 + t*\theta_2
       else
          u:= 1; v:= 0;
          r:= 0; t:= 1;
       end if;

       y:= coc22(<bM[1],bM[2]>);
       if not IsZero(y) then
          coc22:= map< CartesianProduct( M, M ) -> F |
                       v :-> -y*coc21(v)+coc22(v) >;
          r:= -u*y+r; t:= -v*y+t;
          // a new base change...
       end if;

       a:= coc22(<bM[1],bM[3]>);
       if IsZero(a) then
          // try to make it 0:
          b:= coc22(<bM[1],bM[4]>);
          c:= coc22(<bM[2],bM[3]>);
          d:= coc22(<bM[2],bM[4]>);
          if not IsZero(b) then
             bM[3]:= bM[3]+bM[4];
             a:= coc22(<bM[1],bM[3]>);
          elif not IsZero(c) then
             bM[1]:= bM[1]+bM[2];
             a:= coc22(<bM[1],bM[3]>);
          elif not IsZero(d) then
             bM[1]:= bM[1]+bM[2];
             bM[3]:= bM[3]+bM[4];
             a:= coc22(<bM[1],bM[3]>);
          end if;
       end if;

       if not IsZero(a) then
          // make it 1:
          bM[1]:= bM[1]/a; bM[4]:= bM[4]/a;

          // make b,c -> 0
          b:= coc22(<bM[1],bM[4]>); c:= coc22(<bM[2],bM[3]>);
          bM[2]:= bM[2]-c*bM[1]; bM[4]:= bM[4]-b*bM[3];

          e:= coc22(<bM[3],bM[4]>);
          if not IsZero(e) then
             // make it 1:
             bM[2]:= bM[2]/e; bM[4]:= bM[4]/e;

             a:= coc22(<bM[2],bM[4]>);

             if not IsZero(a) and not IsZero( a+1/4 ) then
                b:= a+1/4;
             elif IsZero(a) then
                b:= 1;
             elif IsZero( a+1/4 ) then
                b:= 0;
             end if;
          else
             b:= coc22(<bM[2],bM[4]>);
          end if;

          T:= [ <1,2,5,1>, <1,3,6,1>, <2,4,6,b>, <3,4,5,1> ]; 
          comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;

          V:= RModule( F, 4 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          imgs:= [ ];

          q:= coc21(<bM[1],bM[2]>); // we have to change that back to 1...
          for x in Basis(K) do

              cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );

              cz1:= cz;
              cz1[1]:= u/q*cz[1]+v/q*cz[2];
              cz1[2]:= r*cz[1]+t*cz[2];

              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= cz1;

              if not IsZero(e) then
                 // make another isomorphism...
                 cx1:= cx;
                 if not IsZero(a) and not IsZero(a+1/4) then
                    cx1[1]:= (1/(4*a)+1)*cx[1]; 
                    cx1[2]:= cx[3];
                    cx1[3]:= a*cx[2]+cx[3]/2;
                    cx1[4]:= cx[4]+1/(2*a)*cx[1];
                    cx1[5]:= -cx[5]/2+cx[6];
                    cx1[6]:= (a+1/4)*cx[5];
                 elif IsZero(a) then
                    cx1[1]:= cx[4];
                    cx1[2]:= -cx[2]/4;
                    cx1[3]:= cx[2]/4-cx[3]/2;
                    cx1[4]:= 2*cx[1]-cx[4];
                    cx1[5]:= -cx[5]/2+cx[6];
                    cx1[6]:= cx[5]/2;   
                 elif IsZero(a+1/4) then
                    cx1[1]:= -2*cx[1]+cx[4];
                    cx1[2]:= cx[2]/2-2*cx[3];
                    cx1[3]:= cx[2]/2-cx[3];
                    cx1[4]:= -4*cx[1]+cx[4];
                    cx1[6]:= -cx[5]+2*cx[6];
                 end if;
                 cx:= cx1;
              end if;
              Append( ~imgs, N!cx );
          end for;
          return [* 6, 22, b *], liealg_hom( K, N, Basis(K), imgs );

       else // i.e, a=0, which means that b=c=d=0.

          // make e=1:
          e:= coc22(<bM[3],bM[4]>);
          coc22:= map< CartesianProduct( M, M ) -> F |
                                               v :-> coc22(v)/e >;
          r:= r/e; t:= t/e;

          // subtract coc22 from coc21:
          coc21:= map< CartesianProduct( M, M ) -> F | 
                                          v :-> coc21(v)-coc22(v) >;
          u:= u-r; v:= v-t;

          T:= [ <1,2,5,1>, <1,3,6,1>, <2,4,6,1>, <3,4,5,1> ]; 
          comp_tab( ~T );
          N:= LieAlgebra< F, 6 | T >;

          V:= RModule( F, 4 );
          W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
          imgs:= [ ];

          for x in Basis(K) do

              cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );

              cz1:= cz;
              cz1[1]:= u*cz[1]+v*cz[2];
              cz1[2]:= r*cz[1]+t*cz[2];

              cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x) ) ) ) );
              cx cat:= cz1;

              // isom 
              cx1:= cx;
              cx1[1]:= cx[1]-cx[4];
              cx1[2]:= cx[2]/4-cx[3]/4;
              cx1[3]:= cx[2]/4+cx[3]/4;
              cx1[4]:= -cx[1]-cx[4];
              cx1[5]:= cx[5]/2-cx[6]/2;
              cx1[6]:= cx[5]/2+cx[6]/2;   
              cx:= cx1;
              Append( ~imgs, N!cx );
          end for;
          return [* 6, 22, One(F) *], liealg_hom( K, N, Basis(K), imgs );

       end if;   

    elif type eq [ 4, 2 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       coc22:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[2] >;
       bM:= Basis(M);

       // coc21 can be moved to one of three normal forms
       a:= coc21( <M.1,M.3> );
       b:= coc21( <M.1,M.4> );
       c:= coc21( <M.2,M.3> );
       d:= coc21( <M.2,M.4> );

       if IsZero(a) and not IsZero(c) then // make a not zero
          bM[1]:= bM[1]+bM[2];
          a:= coc21( <bM[1],bM[3]> );
          b:= coc21( <bM[1],bM[4]> );
       end if;

       if not IsZero(a) then

          bM[1]:= bM[1]/a;
          bM[2]:= bM[2]*a;
          c:= coc21(<bM[2],bM[3]>);
          bM[2]:= bM[2]-c*bM[1];

          b:= coc21( <bM[1],bM[4]> );
          d:= coc21( <bM[2],bM[4]> );

          if not IsZero(d) then
             bM[4]:= bM[4]/d-b/d*bM[3];
          else
             bM[4]:= bM[4]-b*bM[3];
          end if;
       else  // here also c=0.
          x,y,u,v:= comp_mat( b, d, One(F) );
          store:= bM[1];
          bM[1]:= x*bM[1]+y*bM[2];
          bM[2]:= u*store+v*bM[2];
       end if;

       s13:= coc21( <bM[1],bM[3]> );
       s24:= coc21( <bM[2],bM[4]> );
       s14:= coc21( <bM[1],bM[4]> );

       r:= 1; t:= 0; 
       u:= 0; v:= 1;

       if not IsZero( s13 ) then

          if not IsZero( s24 ) then

             a:= coc22(<bM[1],bM[3]>);
             u:= -a; v:= 1;             
             coc22:= map< CartesianProduct( M, M ) -> F |
                           v :-> -a*coc21(v)+coc22(v) >;


             b:= coc22( <bM[1],bM[4]> );  
             c:= coc22( <bM[2],bM[3]> );
             d:= coc22( <bM[2],bM[4]> );

             if IsZero(c) then

                if not IsZero(d) then

                   bM[3]:= bM[3]/d;
                   bM[2]:= bM[2]/d;
                   bM[1]:= bM[1]-b*bM[2];
                   bM[4]:= bM[4]+b*bM[3];

                   cf:= 1/coc21(<bM[1],bM[3]>);
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
                   r:= r*cf; t:= t*cf;
                   cf:= 1/coc22(<bM[2],bM[4]>);
                   coc22:= map< CartesianProduct( M, M ) -> F |
                                                v :-> cf*coc22(v) >;
                   u:= u*cf; v:= v*cf;
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> coc21(v)-coc22(v) >;
                   r:= r-u; t:= t-v;
                   c1:= coc21(<bM[1],bM[2]>);
                   c2:= coc22(<bM[1],bM[2]>);

                   T:= [ <1,2,4,1>, <1,3,5,1>, <2,4,6,1> ]; 
                   comp_tab( ~T );
                   N:= LieAlgebra< F, 6 | T >;

                   V:= RModule( F, 4 );
                   W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                   imgs:= [ ];

                   for x in Basis(K) do

                       cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                       cz1:= cz;
                       cz1[1]:= r*cz[1]+t*cz[2];
                       cz1[2]:= u*cz[1]+v*cz[2];
                       cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                       cx cat:= cz1;

                       // subtract the cocycle
                       cx[5]:= cx[5]-c1*cx[3];
                       cx[6]:= cx[6]-c2*cx[3];

                       // isom 
                       cx1:= cx;
                       cx1[1]:= cx[2];
                       cx1[2]:= cx[1];
                       cx1[3]:= cx[4];
                       cx1[4]:= -cx[3];
                       cx1[5]:= cx[6];
                       cx1[6]:= -cx[5];
                       cx:= cx1;
                       Append( ~imgs, N!cx );
                   end for;
                   return [* 6, 19, Zero(F) *], liealg_hom(K,N,Basis(K),imgs);
                else // d=0


                   cf:= 1/coc21(<bM[1],bM[3]>);
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
                   r:= r*cf; t:= t*cf;
                   cf:= 1/coc22(<bM[1],bM[4]>);
                   coc22:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc22(v) >;
                   u:= u*cf; v:= v*cf;

                   c1:= coc21(<bM[1],bM[2]>);
                   c2:= coc22(<bM[1],bM[2]>);

                   T:= [ <1,2,3,1>, <1,3,5,1>, <1,4,6,1>, <2,4,5,1> ]; 
                   comp_tab( ~T );
                   N:= LieAlgebra< F, 6 | T >;

                   V:= RModule( F, 4 );
                   W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                   imgs:= [ ];

                   for x in Basis(K) do

                       cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                       cz1:= cz;
                       cz1[1]:= r*cz[1]+t*cz[2];
                       cz1[2]:= u*cz[1]+v*cz[2];
                       cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                       cx cat:= cz1;

                       // subtract the cocycle
                       cx[5]:= cx[5]-c1*cx[3];
                       cx[6]:= cx[6]-c2*cx[3];

                       Append( ~imgs, N!cx );
                   end for;
                   return [ 6, 23 ], liealg_hom(K,N,Basis(K),imgs);
                end if; 
             else // i.e., c not 0

                if not IsZero(d) then
                   bM[1]:= (2*c/d)*bM[1]+bM[2];
                   bM[2]:= d/(2*c)*bM[2];
                   bM[4]:= (2*c/d)^2*bM[4]-(2*c/d)*bM[3];
 
                   cf:= 1/coc21(<bM[1],bM[3]>);
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
                   r:= r*cf; t:= t*cf;

                   cf:= coc22(<bM[2],bM[3]>);
                   coc22:= map< CartesianProduct( M, M ) -> F |
                                          v :-> (coc22(v)-c*coc21(v))/cf >;
                   u:= (u-c*r)/cf; v:= (v-c*t)/cf;

                   b:= coc22(<bM[1],bM[4]>);
                else
                   bM[1]:= bM[1]/c; bM[3]:= bM[3]/c; bM[4]:= bM[4]/(c^2);
                   cf:= 1/coc21(<bM[1],bM[3]>);
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
                   r:= r*cf; t:= t*cf;
                   b:= coc22(<bM[1],bM[4]>);
                end if;

                c1:= coc21(<bM[1],bM[2]>);
                c2:= coc22(<bM[1],bM[2]>);
                T:= [ <1,2,3,1>, <1,3,5,1>, <1,4,6,b>, <2,3,6,1>, <2,4,5,1> ]; 
                comp_tab( ~T );
                N:= LieAlgebra< F, 6 | T >;

                V:= RModule( F, 4 );
                W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                imgs:= [ ];

                for x in Basis(K) do

                    cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                    cz1:= cz;
                    cz1[1]:= r*cz[1]+t*cz[2];
                    cz1[2]:= u*cz[1]+v*cz[2];
                    cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                    cx cat:= cz1;

                    // subtract the cocycle
                    cx[5]:= cx[5]-c1*cx[3];
                    cx[6]:= cx[6]-c2*cx[3];

                    Append( ~imgs, N!cx );
                end for;
                return [* 6, 24, b *], liealg_hom(K,N,Basis(K),imgs);
             end if;
          else // theta_1 = Delta_13

             b:= coc22( <bM[1],bM[4]> );  
             d:= coc22( <bM[2],bM[4]> );

             if not IsZero(d) then
                bM[1]:= bM[1]-(b/d)*bM[2];
                bM[4]:= bM[4]/d;

                c:= coc22( <bM[2],bM[3]> );
                if not IsZero(c) then
                   bM[1]:= bM[1]/c;
                   bM[3]:= bM[3]/c;

                   // normalise coc21
                   cf:= 1/coc21(<bM[1],bM[3]>);
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
                   r:= r*cf; t:= t*cf;

                   //make a = 0 by subtracting...
                   a:= coc22(<bM[1],bM[3]>);
                   u:= u-a*r; v:= v-a*t;             
                   coc22:= map< CartesianProduct( M, M ) -> F |
                                v :-> -a*coc21(v)+coc22(v) >;

                   c1:= coc21(<bM[1],bM[2]>);
                   c2:= coc22(<bM[1],bM[2]>);
                   T:= [<1,2,3,1>,<1,3,5,1>,<1,4,6,1>,<2,3,6,1>,<2,4,5,1>]; 
                   comp_tab( ~T );
                   N:= LieAlgebra< F, 6 | T >;

                   V:= RModule( F, 4 );
                   W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                   imgs:= [ ];

                   for x in Basis(K) do

                       cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                       cz1:= cz;
                       cz1[1]:= r*cz[1]+t*cz[2];
                       cz1[2]:= u*cz[1]+v*cz[2];
                       cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                       cx cat:= cz1;

                       // subtract the cocycle
                       cx[5]:= cx[5]-c1*cx[3];
                       cx[6]:= cx[6]-c2*cx[3];

                       //isom...
                       cx1:= cx;
                       cx1[1]:= cx[1]+cx[2];
                       cx1[2]:= -cx[1] +cx[2];
                       cx1[3]:= 2*cx[3]+cx[4];
                       cx1[4]:= cx[4];
                       cx1[5]:= 2*cx[5]+2*cx[6];
                       cx1[6]:= -2*cx[5]+2*cx[6];

                       Append( ~imgs, N!cx1 );
                   end for;
                   return [* 6, 24, One(F) *], liealg_hom(K,N,Basis(K),imgs);
                else // c=0

                   // normalise coc21
                   cf:= 1/coc21(<bM[1],bM[3]>);
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
                   r:= r*cf; t:= t*cf;

                   //make a = 0 by subtracting...
                   a:= coc22(<bM[1],bM[3]>);
                   u:= u-a*r; v:= v-a*t;             
                   coc22:= map< CartesianProduct( M, M ) -> F |
                                v :-> -a*coc21(v)+coc22(v) >;

                   c1:= coc21(<bM[1],bM[2]>);
                   c2:= coc22(<bM[1],bM[2]>);
                   T:= [ <1,2,4,1>, <1,3,5,1>, <2,4,6,1> ]; 
                   comp_tab( ~T );
                   N:= LieAlgebra< F, 6 | T >;

                   V:= RModule( F, 4 );
                   W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                   imgs:= [ ];

                   for x in Basis(K) do

                       cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                       cz1:= cz;
                       cz1[1]:= r*cz[1]+t*cz[2];
                       cz1[2]:= u*cz[1]+v*cz[2];
                       cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                       cx cat:= cz1;

                       // subtract the cocycle
                       cx[5]:= cx[5]-c1*cx[3];
                       cx[6]:= cx[6]-c2*cx[3];

                       //isom...
                       cx1:= cx;
                       cx1[1]:= cx[2];
                       cx1[2]:= cx[1];
                       cx1[3]:= cx[4];
                       cx1[4]:= -cx[3];
                       cx1[5]:= cx[6];
                       cx1[6]:= -cx[5];
                       Append( ~imgs, N!cx1 );
                   end for;
                   return [* 6, 19, Zero(F) *], liealg_hom(K,N,Basis(K),imgs);

                end if;

             else // d=0
                bM[4]:= bM[4]/b; // now b=1
                c:= coc22(<bM[2],bM[3]>);
                if not IsZero(c) then
                   bM[1]:= bM[1]/c; bM[3]:= bM[3]/c; bM[4]:= c*bM[4];
                   // normalise coc21
                   cf:= 1/coc21(<bM[1],bM[3]>);
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
                   r:= r*cf; t:= t*cf;

                   //make a = 0 by subtracting...
                   a:= coc22(<bM[1],bM[3]>);
                   u:= u-a*r; v:= v-a*t;             
                   coc22:= map< CartesianProduct( M, M ) -> F |
                                v :-> -a*coc21(v)+coc22(v) >;

                   c1:= coc21(<bM[1],bM[2]>);
                   c2:= coc22(<bM[1],bM[2]>);
                   T:= [<1,2,3,1>,<1,3,5,1>,<2,3,6,1>,<2,4,5,1>]; 
                   comp_tab( ~T );
                   N:= LieAlgebra< F, 6 | T >;

                   V:= RModule( F, 4 );
                   W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                   imgs:= [ ];

                   for x in Basis(K) do

                       cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                       cz1:= cz;
                       cz1[1]:= r*cz[1]+t*cz[2];
                       cz1[2]:= u*cz[1]+v*cz[2];
                       cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                       cx cat:= cz1;

                       // subtract the cocycle
                       cx[5]:= cx[5]-c1*cx[3];
                       cx[6]:= cx[6]-c2*cx[3];

                       //isom...
                       cx1:= cx;
                       cx1[1]:= -cx[2];
                       cx1[2]:= -cx[1];
                       cx1[3]:= -cx[3];
                       cx1[4]:= -cx[4];
                       cx1[5]:= cx[6];
                       cx1[6]:= cx[5];

                       Append( ~imgs, N!cx1 );
                   end for;
                   return [* 6, 24, Zero(F) *], liealg_hom(K,N,Basis(K),imgs);

                else // c=0
                   // normalise coc21
                   cf:= 1/coc21(<bM[1],bM[3]>);
                   coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
                   r:= r*cf; t:= t*cf;

                   //make a = 0 by subtracting...
                   a:= coc22(<bM[1],bM[3]>);
                   u:= u-a*r; v:= v-a*t;             
                   coc22:= map< CartesianProduct( M, M ) -> F |
                                v :-> -a*coc21(v)+coc22(v) >;

                   c1:= coc21(<bM[1],bM[2]>);
                   c2:= coc22(<bM[1],bM[2]>);
                   T:= [<1,2,3,1>,<1,3,5,1>,<1,4,6,1>]; 
                   comp_tab( ~T );
                   N:= LieAlgebra< F, 6 | T >;

                   V:= RModule( F, 4 );
                   W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
                   imgs:= [ ];

                   for x in Basis(K) do

                       cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                       cz1:= cz;
                       cz1[1]:= r*cz[1]+t*cz[2];
                       cz1[2]:= u*cz[1]+v*cz[2];
                       cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                       cx cat:= cz1;

                       // subtract the cocycle
                       cx[5]:= cx[5]-c1*cx[3];
                       cx[6]:= cx[6]-c2*cx[3];

                       Append( ~imgs, N!cx );
                   end for;
                   return [ 6, 25 ], liealg_hom(K,N,Basis(K),imgs);

                end if;
             end if;
          end if;

       else // i.e., theta_1 = Delta_14

          c:= coc22(<bM[2],bM[3]>);
          if not IsZero(c) then

             bM[1]:= bM[1]/c; bM[3]:= bM[3]/c;

             a:= coc22(<bM[1],bM[3]>);
             d:= coc22(<bM[2],bM[4]>);
             bM[1]:= bM[1]-a*bM[2];
             bM[4]:= bM[4]-d*bM[3];

             // normalise coc21
             cf:= 1/coc21(<bM[1],bM[4]>);
             coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
             r:= r*cf; t:= t*cf;

             //make b = 0 by subtracting...
             b:= coc22(<bM[1],bM[4]>);
             u:= u-b*r; v:= v-b*t;             
             coc22:= map< CartesianProduct( M, M ) -> F |
                                v :-> -b*coc21(v)+coc22(v) >;

             c1:= coc21(<bM[1],bM[2]>);
             c2:= coc22(<bM[1],bM[2]>);
             T:= [ <1,2,4,1>, <1,3,5,1>, <2,4,6,1> ]; 
             comp_tab( ~T );
             N:= LieAlgebra< F, 6 | T >;

             V:= RModule( F, 4 );
             W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
             imgs:= [ ];

             for x in Basis(K) do

                 cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                 cz1:= cz;
                 cz1[1]:= r*cz[1]+t*cz[2];
                 cz1[2]:= u*cz[1]+v*cz[2];
                 cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                 cx cat:= cz1;

                 // subtract the cocycle
                 cx[5]:= cx[5]-c1*cx[3];
                 cx[6]:= cx[6]-c2*cx[3];

                 //isom...
                 cx1:= cx;
                 cx1[1]:= -cx[2];
                 cx1[2]:= cx[1];
                 cx1[3]:= cx[3];
                 cx1[4]:= -cx[4];
                 cx1[5]:= -cx[6];
                 cx1[6]:= -cx[5];
                 Append( ~imgs, N!cx1 );
             end for;
             return [* 6, 19, Zero(F) *], liealg_hom(K,N,Basis(K),imgs);
          else //c=0

             a:= coc22(<bM[1],bM[3]>);
             bM[2]:= bM[2]/a; bM[3]:= bM[3]/a;
             d:= coc22(<bM[2],bM[4]>);
             if not IsZero(d) then
                bM[4]:= bM[4]/d;
             end if;

             // normalise coc21
             cf:= 1/coc21(<bM[1],bM[4]>);
             coc21:= map< CartesianProduct( M, M ) -> F |
                                          v :-> cf*coc21(v) >;
             r:= r*cf; t:= t*cf;

             //make b = 0 by subtracting...
             b:= coc22(<bM[1],bM[4]>);
             u:= u-b*r; v:= v-b*t;             
             coc22:= map< CartesianProduct( M, M ) -> F |
                                v :-> -b*coc21(v)+coc22(v) >;

             c1:= coc21(<bM[1],bM[2]>);
             c2:= coc22(<bM[1],bM[2]>);
             if not IsZero(d) then
                T:= [ <1,2,3,1>, <1,3,5,1>, <1,4,6,1>, <2,4,5,1> ];
             else
                T:= [ <1,2,3,1>, <1,3,5,1>, <1,4,6,1> ];
             end if; 
             comp_tab( ~T );
             N:= LieAlgebra< F, 6 | T >;

             V:= RModule( F, 4 );
             W:= RModuleWithBasis( [ V!Eltseq(x) : x in bM ] );
             imgs:= [ ];

             for x in Basis(K) do

                 cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
                 cz1:= cz;
                 cz1[1]:= r*cz[1]+t*cz[2];
                 cz1[2]:= u*cz[1]+v*cz[2];
                 cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
                 cx cat:= cz1;

                 // subtract the cocycle
                 cx[5]:= cx[5]-c1*cx[3];
                 cx[6]:= cx[6]-c2*cx[3];

                 //isom...
                 cx1:= cx;
                 cx1[5]:= cx[6];
                 cx1[6]:= cx[5];
                 Append( ~imgs, N!cx1 );
             end for;
             if not IsZero(d) then
                return [ 6, 23 ], liealg_hom(K,N,Basis(K),imgs);
             else
                return [ 6, 25 ], liealg_hom(K,N,Basis(K),imgs);
             end if;
          end if;
       end if;
   
    elif type eq [ 4, 3 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       coc22:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[2] >;

       a:= coc21( <M.1,M.4> );
       b:= coc21( <M.2,M.3> );
       c:= coc22( <M.1,M.4> );
       d:= coc22( <M.2,M.3> );
       m:= Matrix( [[a,b],[c,d]] )^-1;

       r:= m[1,1]; t:= m[1,2];
       u:= m[2,1]; v:= m[2,2];

       cc:= coc21;
       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> r*coc21(v)+t*coc22(v) >;
       coc22:= map< CartesianProduct( M, M ) -> F |
                       w :-> u*cc(w)+v*coc22(w) >;

       bM:= Basis(M);
       c1:= coc21(<bM[1],bM[2]>);
       c2:= coc22(<bM[1],bM[2]>);
       c3:= coc21(<bM[1],bM[3]>);
       c4:= coc22(<bM[1],bM[3]>);

       T:= [ <1,2,3,1>, <1,3,4,1>, <2,3,5,1>, <1,4,6,1> ];
       comp_tab( ~T );
       N:= LieAlgebra< F, 6 | T >;

       V:= RModule( F, 4 );
       W:= RModuleWithBasis( [ V!Eltseq(x) : x in Basis(M) ] );
       imgs:= [ ];

       for x in Basis(K) do

           cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
           cz1:= cz;
           cz1[1]:= r*cz[1]+t*cz[2];
           cz1[2]:= u*cz[1]+v*cz[2];
           cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
           cx cat:= cz1;

           // subtract the cocycle
           cx[5]:= cx[5]-c1*cx[3]-c3*cx[4];
           cx[6]:= cx[6]-c2*cx[3]-c4*cx[4];

           //isom...
           cx1:= cx;
           cx1[5]:= cx[6];
           cx1[6]:= cx[5];
           Append( ~imgs, N!cx1 );
       end for;
       return [* 6, 21, Zero(F) *], liealg_hom(K,N,Basis(K),imgs);

    elif type eq [ 3, 1 ] then

       coc21:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[1] >;
       coc22:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[2] >;
       coc23:= map< CartesianProduct( M, M ) -> F |
                       v :-> Coordinates( C, coc2(v) )[3] >;

       m:= ScalarMatrix( 3, Zero(F) );
       m[1,1]:= coc21( <M.1,M.2> );
       m[1,2]:= coc21( <M.1,M.3> );
       m[1,3]:= coc21( <M.2,M.3> );
       m[2,1]:= coc22( <M.1,M.2> );
       m[2,2]:= coc22( <M.1,M.3> );
       m[2,3]:= coc22( <M.2,M.3> );
       m[3,1]:= coc23( <M.1,M.2> );
       m[3,2]:= coc23( <M.1,M.3> );
       m[3,3]:= coc23( <M.2,M.3> );

       m:= m^-1;

       T:= [ <1,2,4,1>, <1,3,5,1>, <2,3,6,1> ];
       comp_tab( ~T );
       N:= LieAlgebra< F, 6 | T >;

       V:= RModule( F, 3 );
       W:= RModuleWithBasis( [ V!Eltseq(x) : x in Basis(M) ] );
       imgs:= [ ];

       for x in Basis(K) do

           cz:= Eltseq( Coordinates( C, x-s(p(x)) ) );
           cz:= Vector(cz)*Transpose(m);
           cx:= Eltseq( Coordinates( W, V!Eltseq( tau( p(x)))));
           cx cat:= Eltseq( cz );
           Append( ~imgs, N!cx );
       end for;
       return [ 6, 26  ], liealg_hom(K,N,Basis(K),imgs);

    end if;


end function;


intrinsic IdDataNLAC( L::AlgLie ) -> MonStgElt, SeqEnum, Map
{Here L has to be a nilpotent Lie algebra of dimension 3,4,5,6. This function
returns the name of L (as it appears in the classification), a sequence of
parameters, and an isomorphism from L to the isomorphic Lie algebra in the
classification}

     n:= Dimension( L );

     require n in [3,4,5,6] : "L has to have dimension between 3 and 6.";

     require IsNilpotent( L ) : "L has to be a nilpotent Lie algebra.";

     if Dimension(L) eq 6 then
        require Characteristic( BaseRing(L) ) ne 2 : "The base ring of L cannot be of characteristic 2.";
     end if;

     if Dimension(L) le 4 then
        id,f:= class_dim_le4( L );
     elif Dimension(L) eq 5 then
        id,f:= class_dim_5( L );
     else
        id,f:= class_dim_6( L );
     end if;

     str:= "N" cat Sprint( id[1] ) cat "_" cat 
           Sprint( id[2] ) cat "( " cat Sprint( BaseRing(L) );
     for i in [3..#id] do
         str cat:= ", ";
         str cat:= Sprint( id[i] );
     end for;
     str cat:= " )";
     

     return str, [ id[i] : i in [3..#id] ],f;

end intrinsic;


intrinsic AllNilpotentLieAlgebras( F::Fld, dim::RngIntElt ) -> SeqEnum
{All nilpotent Lie algebras of dimension dim over the finite field F of 
characteristic not 2.}

        require IsFinite( F ) : "F has to be a finite field.";

        require dim in [3,4,5,6] : "dim has to be between 3 and 6.";

        require Characteristic(F) ne 2 : "The characteristic of F cannot be 2.";

    list:= [ ] ;
    if dim eq 3 then
       Append( ~list, L31( F ) );
       Append( ~list, L32( F ) );
    elif dim eq 4 then
       Append( ~list, L41( F ) );
       Append( ~list, L42( F ) );
       Append( ~list, L43( F ) );
    elif dim eq 5 then 
       Append( ~list, L51( F ) );
       Append( ~list, L52( F ) );
       Append( ~list, L53( F ) );
       Append( ~list, L54( F ) );
       Append( ~list, L55( F ) );
       Append( ~list, L56( F ) );
       Append( ~list, L57( F ) );
       Append( ~list, L58( F ) );
       Append( ~list, L59( F ) );
    else

       a:= PrimitiveElement(F);

       Append( ~list, L61( F ) );
       Append( ~list, L62( F ) );
       Append( ~list, L63( F ) );
       Append( ~list, L64( F ) );
       Append( ~list, L65( F ) );
       Append( ~list, L66( F ) );
       Append( ~list, L67( F ) );
       Append( ~list, L68( F ) );
       Append( ~list, L69( F ) );    
       Append( ~list, L610( F ) );
       Append( ~list, L611( F ) );
       Append( ~list, L612( F ) );
       Append( ~list, L613( F ) );
       Append( ~list, L614( F ) );
       Append( ~list, L615( F ) );
       Append( ~list, L616( F ) );
       Append( ~list, L617( F ) );
       Append( ~list, L618( F ) );

       Append( ~list, L619( F, Zero(F) ) );    
       Append( ~list, L619( F, One(F) ) );    
       Append( ~list, L619( F, a ) );    

       Append( ~list, L620( F ) );
 
       Append( ~list, L621( F, Zero(F) ) );    
       Append( ~list, L621( F, One(F) ) );    
       Append( ~list, L621( F, a ) );
  
       Append( ~list, L622( F, Zero(F) ) );    
       Append( ~list, L622( F, One(F) ) );    
       Append( ~list, L622( F, a ) );
  
       Append( ~list, L623( F ) );
     
       Append( ~list, L624( F, Zero(F) ) );    
       Append( ~list, L624( F, One(F) ) );    
       Append( ~list, L624( F, a ) );  

       Append( ~list, L625( F ) );
       Append( ~list, L626( F ) );
    end if;

    return list;
 
end intrinsic;


intrinsic NilpotentLieAlgebra( F::Fld, dim::RngIntElt, no::RngIntElt : pars:= [] ) -> AlgLie
{The nilpotent Lie algebra of dimension dim over the field F, with number no in the classification.}


    require dim in [3,4,5,6] : "dim has to be between 3 and 6.";

    if dim eq 3 then
       require no le 2 : "There are only two classes of nilpotent Lie algebras of dimension 3.";
       
       if no eq 1 then
          return L31( F );
       else
          return L32(F);
       end if;

    elif dim eq 4 then
       require no le 3 : "There are only three classes of nilpotent Lie algebras of dimension 4.";

       case no:
         when 1: return L41( F );
         when 2: return L42( F );
         when 3: return L43( F );
       end case;

    elif dim eq 5 then
       require no le 9 : "There are only nine classes of nilpotent Lie algebras of dimension 5.";

       case no:
         when 1: return L51( F );
         when 2: return L52( F );
         when 3: return L53( F );
         when 4: return L54( F );
         when 5: return L55( F );
         when 6: return L56( F );
         when 7: return L57( F );
         when 8: return L58( F );
         when 9: return L59( F );
       end case;

    else
       require no le 26 : "There are only twenty six classes of nilpotent Lie algebras of dimension 6.";

       if no in [19,21,22,24] then
          require #pars gt 0 : "For this Lie algebra a parameter list is required.";
          require pars[1] in F : "The parameter has to lie in the field of definition.";
       end if; 

       case no:
         when 1: return L61( F );
         when 2: return L62( F );
         when 3: return L63( F );
         when 4: return L64( F );
         when 5: return L65( F );
         when 6: return L66( F );
         when 7: return L67( F );
         when 8: return L68( F );
         when 9: return L69( F );
         when 10: return L610( F );
         when 11: return L611( F );
         when 12: return L612( F );
         when 13: return L613( F );
         when 14: return L614( F );
         when 15: return L615( F );
         when 16: return L616( F );
         when 17: return L617( F );
         when 18: return L618( F );
         when 19: return L619( F, pars[1] );
         when 20: return L620( F );
         when 21: return L621( F, pars[1] );
         when 22: return L622( F, pars[1] );
         when 23: return L623( F );
         when 24: return L624( F, pars[1] );
         when 25: return L625( F );
         when 26: return L626( F );
       end case;
    end if;

end intrinsic;








