freeze;

///////////////////////////////////////////////////////////////////////////

declare attributes AlgLie: IsRestrictable, PImages, PMap,
  GradingList;
declare attributes Grp : JenningsLieAlgebra;

//
//  Basic intrinsics for p-Lie algebras
//

SiFunctions:= function( p )

    // return a list of p-1 functions, the i-th function
    // being s_i(a,b) where a,b are from a Lie algebra.

    fcs:= [* *];
    for i in [1..p-1] do

        // s_i(a,b) is (1/i)* the coefficient of T^{i-1} in 
        // ad(Ta+b)^{p-1}(a). This last object is the sum of the
        // right-normed commutators [x_1[x_2[....[x_{p-2},[b,a]]...]]]
        // where x_k is a or b, and there are i-1 a's and p-1-i b's.

        set:= Subsets( {1..p-2}, i-1 );  // the positions of the a's.
        u:= SetToSequence( set );
        v:= [ SetToSequence( u[k] ) : k in [1..#u] ];

        si:= function( a, b )

             x:= 0*a;
             for k in [1..#v] do
                 s:= v[k];
                 e:= b*a;
                 for j in [1..p-2] do
                     if j in s then
                        e:= a*e;
                     else
                        e:= b*e;
                     end if;
                 end for;
                 x:= x+e;
             end for;
             return (1/i)*x;

        end function;

        Append( ~fcs, si );
    end for;
    return fcs;
    
end function;

pMapHom := function( L, imgs )
  F:= BaseRing( L );
  p:= Characteristic( F );
  if p eq 0 then
    return IdentityAutomorphism( L );
  end if;
  s:= SiFunctions( p );
  p_map:= function( L, imgs, s, p, x )

   // we have 
   //
   //  (c1*x1+...+cn*xn)^p = c1^p*x1^p + ... + cn^p*xn^p +
   //  \sum_{k=1}^{n-1} \sum_{i=1}^{p-1} s_i( ck*xk, c_{k+1}x_{k+1}+...+
   //  c_nx_n )

     c:= Coordinates( L, x );
     res:= 0*x;
     for k in [1..#c] do
         if not IsZero( c[k] ) then
            res:= res+c[k]^p*imgs[k];
            if k lt #c then
               y:= 0*x;
               for l in [k+1..#c] do
                 y:= y+c[l]*L.l;
               end for;
               if not IsZero(y) then
                  for i in [1..p-1] do
                    res:= res + s[i]( c[k]*L.k, y );
                  end for;
               end if;
            end if;
         end if;
     end for;
     return res;
  end function;

  return map< L -> L | x :-> p_map( L, imgs, s, p, x ) >;
end function;

// This computes a representative of x^p + Z(L).
// This is independent of the particular p-map, and
// this is much more efficient than pMap.
pMapCentral := function( L )
  F:= BaseRing( L );
  p:= Characteristic( F );
  rho := AdjointRepresentation( L );
  return map< L -> L | x :-> ( Codomain(rho)!( Matrix(rho(x))^p ) )@@rho >;
end function;


intrinsic IsRestrictable( L::AlgLie ) -> BoolElt, Map
{True iff L is a restrictable Lie algebra}

     F := BaseRing( L );
     require ISA( Category(F), Fld ) : "The base ring must be a field";
     p := Characteristic( F );
     if p eq 0 then  return true, IdentityAutomorphism(L);  end if;
     d := Dimension( L );
      
     if (not assigned L`IsRestrictable) or
     (L`IsRestrictable and not assigned L`PImages) then
        
       adL := AdjointRepresentation( L );
       M := Codomain( adL );
       
       // Compute the span of the image of ad
       V := RMatrixSpace( F, d, d );
       V := sub< V | [ V | adL(L.i) : i in [1..d] ] >;
       
       // Compute the p-images
       ok := true;  images := [];  i := 0;
       repeat
         i := i + 1;
         v := Matrix( adL( L.i ) )^p;
         if v in V then
			//If there is a centre, there is some freedom in choosing the "image"
			if Matrix(adL(L.i)) eq v then 
				Append(~images, L.i); 
			else 
				Append( ~images, (M!v)@@adL ); 
			end if;
         else
           ok := false;
         end if;
       until not ok or i eq d;
       
       L`IsRestrictable := ok;
       if ok then  L`PImages := images;  end if;
       
     end if;

     if L`IsRestrictable and not assigned L`PMap then
       L`PMap := ( Dimension(Centre(L)) eq 0 ) select
         pMapCentral( L ) else pMapHom( L, L`PImages );
     end if;

     if L`IsRestrictable then
         return true, L`PMap;
     else
       return false, _;
     end if;
     d:= Dimension( L );

end intrinsic;

intrinsic IsRestricted( L::AlgLie ) -> BoolElt, Map
{True iff L is a restrictable Lie algebra}
  return IsRestrictable( L );
end intrinsic;

intrinsic IspLieAlgebra( L::AlgLie ) -> BoolElt, Map
{True iff L is a restrictable Lie algebra}
  return IsRestrictable( L );
end intrinsic;

// for backwards compatibility
intrinsic IsRestrictedLieAlgebra( L::AlgLie ) -> BoolElt, Map
{True iff L is a restrictable Lie algebra}
  return IsRestrictable( L );
end intrinsic;

intrinsic RestrictionMap( L::AlgLie ) -> Map
{The restriction map of L}
  ok, pmap := IsRestrictable( L );
  require ok : "Not a restrictable Lie algebra";
  return pmap;
end intrinsic;

intrinsic pMap( L::AlgLie ) -> Map
{The restriction map of L}
  ok, pmap := IsRestrictable( L );
  require ok : "Not a restrictable Lie algebra";
  return pmap;
end intrinsic;


//
//  p-Lie subalgebras and quatients
//
intrinsic RestrictedSubalgebra( Q::SetEnum[AlgLieElt] ) -> AlgLie
{The restricted subalgebra generated by the input}
  L := Universe( Q );  Z := Centre( L );
  ok, pmap := IsRestrictable( L );
  require ok : "Not elements of a restrictable Lie algebra";
  M := sub< L | Q >;
  repeat
    if Z subset M then
      // we can now use a more efficient map
      pmap := pMapCentral( L );  
    end if;
    oldM := M;
    M := sub< L | M, [ (L!b)@pmap : b in Basis(M) ] >;
  until M eq oldM;
  M`IsRestrictable := true;
  M`PImages := [ M!( (L!b)@pmap ) : b in Basis( M ) ];
  return M;
end intrinsic;

intrinsic pSubalgebra( Q::SetEnum[AlgLieElt] ) -> AlgLie
{The restricted subalgebra generated by the input}
  return RestrictedSubalgebra( Q );
end intrinsic;

intrinsic pClosure( L::AlgLie, M::AlgLie ) -> BoolElt
{The restricted subalgebra of the first input, generated by the second}
  require M subset L : "The second argument must be a subalgebra of the first";
  require IsRestrictable( L ) : "The second argument must be restrictable";;
  return pSubalgebra( { L | L!b : b in Basis(M) } );
end intrinsic;

intrinsic IsRestrictedSubalgebra( L::AlgLie, M::AlgLie ) -> BoolElt
{True iff L is closed under the p-map of M and the p-map of L is a restriction}
  require ExistsCoveringStructure(L,M) and L subset M :
    "Not a subalgebra";
  ok, pmapM := IsRestrictable( M );
  require ok : "The second argument must be restrictable";
  ok, pmapL := IsRestrictable( L );
  return ok and forall{ b : b in Basis(L) | M!pmapL(b) eq pmapM(M!b) };
end intrinsic;

intrinsic IspSubalgebra( L::AlgLie, M::AlgLie ) -> BoolElt
{True iff L is closed under the p-map of M and the p-map of L is a restriction}
  return IspSubalgebra( L, M );
end intrinsic;

intrinsic pQuotient( L::AlgLie, M::AlgLie ) -> AlgLie
{The quotient of L by the p-closure of M, with the inherited p-map}
  ok, pmap := IsRestrictable( L );
  require ok : "The first argument must be restrictable";
  M := pClosure( M, L );
  Q, h := L/M;
  Q`IsRestrictable := true;
  Q`PImages := [ h(pmap(b@@h)) : b in Basis( Q ) ];
  return Q, h;
end intrinsic;

/* This is not used, since user-defined p-maps are not currently allowed
intrinsic CheckPImages( L::AlgLie, images::[] ) -> BoolElt
{Internal intrinsic}
  p := Characteristic( BaseRing( L ) );
  if p eq 0 then
    return images eq Basis(L);
  else
    s := SiFunctions( p );
    pmap := pMapHom( L, images );
    B := Basis( L );
    ad := AdjointRepresentation( L );
    for i in [1..#B] do
      for j in [1..#B] do
        if B[i]*images[j] ne B[i]*(ad(B[j])^p) or
        pmap(B[i]+B[j]) ne 
        images[i]+images[j]+ &+[s[idx](B[i],B[j]):idx in [1..p-1]] then
          return false;
        end if;
      end for;
    end for;
  end if;
  return true;
end intrinsic;*/


intrinsic JenningsLieAlgebra( G::Grp ) -> AlgLie
{ for a p-group G this returns the Lie algebra that is the direct sum of
subsequent quotients of the Jennings series of G }

    // for a p-group G this produces the corresponding Lie algebra
    // which is the direct sum of the quotients of successive terms
    // of the Jennings series.

    if assigned G`JenningsLieAlgebra then
       L:= G`JenningsLieAlgebra;
       return L,L`GradingList;
    end if;    
      
    fac:= FactoredOrder(G);
    require #fac eq 1: "The group G is not a p group";

    p:= fac[1][1];
    d:= fac[1][2];

    F:= GF(p);

    jen:= JenningsSeries( G );
    comps:=  [ ];      // successive quotients of of terms in the 
                       // Jennings series

    maps:= [* *];      //for each qotient this contains the projection map. 
    spaces:= [ ];      //for each quotient this contains a list of indices
                       // of basis elements that come from that quotient.
    // So if the quotients have orders p^2, 1, 1, p^3, p, then
    // spaces will be [ [1,2], [], [], [3,4,5], [6] ]
 
    n:= 0;
    for k in [1..#jen-1] do
        g,h:= quo< jen[k] | jen[k+1] >;
        Append( ~comps, g );
        Append( ~maps, h );
        s:= [ ];
        if #g gt 1 then
           for i in [1..FactoredOrder(g)[1][2]] do
               n:= n+1;
               Append( ~s, n );
           end for;
        end if;
        Append( ~spaces, s );
    end for;

    T:= [ ];

    for i in [1..n] do
        for k in [1..#spaces] do
            if i in spaces[k] then
               di:= k;
               hi:= comps[k].Position( spaces[k], i );
               break;
            end if;
        end for;
        gi:= G!(hi @@ maps[di] );
        for j in [i+1..n] do
            for k in [1..#spaces] do
                if j in spaces[k] then
                   dj:= k;
                   hj:= comps[k].Position( spaces[k], j );
                   break;
                end if;
            end for;
             
            if di+dj le #spaces and #spaces[di+dj] gt 0 then 
               //otherwise the product is zero anyway
   
               gj:= G!(hj @@ maps[dj] );
               h:= maps[di+dj]( ( gi, gj ) );

               // Get the exponents of h written as a product of generators.

               s:= Eltseq( h );
               inds:= spaces[di+dj];
               for k in [1..#inds] do
                   if not IsZero( s[k] ) then
                      Append( ~T, <i, j, inds[k], F!s[k] > );
                      Append( ~T, <j, i, inds[k], F!-s[k] > );
                   end if;
               end for;
            end if;
            
        end for;
    end for;    

    if #T eq 0 then
       T:= [ F!0 : i in [1..n^3] ];
    end if;
     
    L:= LieAlgebra< F, n | T >;

    pimgs:= [ ];
    for i in [1..n] do

        // get the pth-power image of the i-th basis element.

        for k in [1..#spaces] do
            if i in spaces[k] then
               di:= k;
               hi:= comps[k].Position( spaces[k], i );
               break;
            end if;
        end for;
        gi:= G!(hi @@ maps[di] );
        x:= Zero(L);
        if p*di le #spaces and #spaces[p*di] gt 0 then
           // otherwise the pth-power image is zero.
                            
           h:= maps[p*di]( gi^p );

           // Get the exponents of h written as a product of generators.

           s:= Eltseq( h );
           inds:= spaces[p*di];
           for k in [1..#inds] do
               x:= x+F!s[k]*L.(inds[k]);
           end for;
        end if;
        Append( ~pimgs, x );
    end for; 

    L`PImages:= pimgs;
    L`IsRestrictable:= true;
    G`JenningsLieAlgebra:= L;

    // L is graded, and the dimensions of the homogeneous components
    // follow from the data in spaces.
    gr:= [ ];
    for i in [1..#spaces] do
        if #spaces[i] gt 0 then     
           Append( ~gr, [ i, #spaces[i] ] ); 
        end if;
    end for;
    L`GradingList:= gr;
    return L,gr;

end intrinsic; 
