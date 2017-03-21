freeze;

/////////////////////////////////////////////////////////////////////////////////////////

extract:= function( type, field, insubalgs, graph )

   if field eq 0 then
      F := Rationals();
   else
      F := CyclotomicField( field );
   end if;
   L := LieAlgebra( RootDatum( type : Isogeny:= "SC" ), F );

   subalgs:= [ ];
   for c in insubalgs do
       rank := Integers()!(#c/3);
       u := [ &+[ v[2]*L.v[1] : v in c[i] ] : i in [1..#c] ];

       x := u[[1..rank]];
       y := u[[rank+1..2*rank]];
       h := u[[2*rank+1..3*rank]];

       K := sub< L | x cat y cat h >; /* This line is taking almost all the CPU time */
       K`SplittingCartanSubalgebra:= sub< K | [ K!z : z in h ] >;
       Append( ~subalgs, K );
   end for;

   verts:= [ a : a in [1..#subalgs] ] cat [0];
   V:= {@ a : a in verts @};
   G:= Digraph< V | SequenceToSet( graph ) >;
   labs:= subalgs cat [L];
   AssignLabels(~G, Vertices(G), labs );

   return G;

end function;

intrinsic SubalgebrasInclusionGraph( typ::MonStgElt ) -> GrphDir
{Return the directed graph giving the inclusions among the semisimple subalgebras of the semisimple
Lie algebra of the given type.}

	if typ eq "B2" then typ:= "C2"; end if;

	require (#typ eq 2) and (StringToInteger(typ[2]) le 8) : "This function is only implemented for simple Lie algebras of rank up to 8";

	D := SemisimpleSubLieDatabase();

	dim, fld, subalgs, graph := SemisimpleSubLie(D, typ[1], StringToInteger(typ[2]));

	return extract( typ, fld, subalgs, graph );
end intrinsic;


intrinsic RestrictionMatrix( G::GrphDir, k::RngIntElt ) -> AlgMatElt
{Return the restriction matrix corresponding to the simple Lie algebra at the top of the inclusions graph
G, and its subalgebra at label k.}

    v:= Vertices(G);

    require k ge 1 and k lt #v : "k has to be positive, and less than the number of vertices of G";

    L:= Label( v[#v] );
    K:= Label( v[k] );

    _,_,hK:= CanonicalGenerators(K);
    _,_,hL:= CanonicalGenerators(L);
    b:= VectorSpaceWithBasis( [ Vector( BaseField(L), L!hL[i] ) : i in [1..#hL] ] );
    
    return Transpose( Matrix( Integers(), 
               [ Coordinates( b, Vector( BaseField(L), L!u ) ) : u in hK ] ));

end intrinsic;
