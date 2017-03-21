freeze;

// 
// morphisms.m
//
// Some basic functionality for SC algebra and Lie algebra morphisms
//

dependence := function( vects )
  A := Matrix( vects );
  N := Nullspace( A );
  return N.1;
end function;

reduceToBasis := function( vects )
  vects := [ Vector( v ) : v in vects ];
  B := [1..#vects];
  while not IsIndependent( vects[B] ) do
    d := dependence( vects[B] );
    _ := exists(i){ i : i in [1..#vects] | d[i] ne 0 };
    Remove( ~B, i );
  end while;
  return B;
end function;

intrinsic Image( f::Map[Alg,Alg] ) -> Alg
{The image of f}
  return sub< Codomain(f) | [ f(x) : x in Generators(Domain(f)) ] >;
end intrinsic;

compPreImageRule := procedure(h)
// Do we want this extra check:
    if assigned h`PreImageRule then
        return;
    end if;
    L := Domain( h );    d := Dimension( L );
    M := Codomain( h );  deg := Degree( M );
    V := RMatrixSpace( BaseRing(M), deg, deg ); // copy of M as vector space
    
    BL := Basis(L);
    B := [ V | h(BL[i]) : i in [1..d] ];
    idx := reduceToBasis( B );
    U := RMatrixSpaceWithBasis( B[idx] );
    h`PreImageRule := function( x )
        if x notin U then
            error "Runtime error in '@@': The element is not in the image of the map";
        else
            return &+[L| a[i]*BL[idx[i]] : i in [1..#idx] ] 
            where a is Coordinates(U, V!x);
        end if;
    end function;
end procedure;


intrinsic ComputePreImageRule( h::Map[AlgLie,AlgLie] )
{Internal intrinsic}
    compPreImageRule(h);    
end intrinsic;

intrinsic ComputePreImageRule( h::Map[AlgLie,AlgMatLie] )
{"} // "
    compPreImageRule(h);    
end intrinsic;

intrinsic ComputePreImageRule( h::Map[AlgMatLie,AlgLie] )
{"} // "
    compPreImageRule(h);    
end intrinsic;

intrinsic ComputePreImageRule( h::Map[AlgMatLie,AlgMatLie] )
{"} // "
    compPreImageRule(h);    
end intrinsic;


