//cohomology.m 4/24/09
// fixed bugs 12/16/14

freeze;

import "setlevel.m":
    brm,
    SetLevel;
import "sharbly.m":
    unimodularize;

import "cuspidal.m":
    abmat;

function number_of_orbits(orb)
    return Maximum(orb`orbit_type);
end function;

function get_column(M,GLtype2,Gamma0type2);
    //returns the column in the boundary matrix associated to the GLtype
    //and Gamma0type.  Does not throw out non-orientable sharblies.
    //Just adds them to the relations.
    GLstd2:=M`ModFrmData`two_poly[GLtype2];
    orbits2:=M`LevelData`two_orbits[GLtype2];
    gamma0:=orbits2`gamma_list[Gamma0type2];
    boundary:=[ L : L in GLstd2`GL_facet_types | L[1] ne 0 ];
    sofar:=[0:i in [1..M`LevelData`total_number_of_one_orbits]];
    
    //We know the boundary of the standard 2 polytopes.  We get the
    //boundaries of the Gamma0 classes of 2-polytopes by translation.
    for L in boundary do
	//gamma0 moves standard 2-poly to here.
	mover:=L[3];//moves std edge to here
	sgn:=L[2];
	GLtype1:=L[1];
	i:=brm(M,gamma0*mover);
	Gamma0type1:=M`LevelData`one_orbits[GLtype1]`orbit_type[i];
		
	onumber:=M`LevelData`one_orbits[GLtype1]`orbit_number_list[i];
	totsgn:=sgn*onumber;
	j:=M`LevelData`one_orbits[GLtype1]`entry[Gamma0type1];
	sofar[j] +:= totsgn ;
    end for;
    vprintf Bianchi,4: "This relation involves edges %o.\n",
	Support(Vector(sofar));
    return sofar;
end function;


function relations(M)
    //Assumes F and M`LevelData have already been set up correctly
    vprint Bianchi, 1:"Computing relations and non-orientable cells.";
    orbits2:=M`LevelData`two_orbits;
    orbits1:=M`LevelData`one_orbits;
    L:=[];
    for GLtype2 in [1..#orbits2] do
	orbit:=orbits2[GLtype2];
	for Gamma0type2 in [1..orbit`total_number] do
	    if not Gamma0type2 in orbit`non_orientable_orbits then 
		col:=get_column(M,GLtype2,Gamma0type2);
		Append(~L,col);
	    end if;
	end for;
    end for;

    // the above computes the relations coming from the
    // orientable facets of the
    // polytopes.  Now we still must introduce the relations coming from
    // non-orientable orbits of edges.
    noedge_index:=&cat[[edge`entry[i]: i in edge`non_orientable_orbits] : edge in orbits1];
    non_orientables:=[[0: i in [1..M`LevelData`total_number_of_one_orbits]]:
	j in [1..#noedge_index]];
    for i in [1..#noedge_index] do
	non_orientables[i][noedge_index[i]]:=1;
	vprintf Bianchi, 4:
	    "edge number %o is non-orientable.\n", noedge_index[i];
    end for;

    L:=L cat non_orientables;
    vprintf Bianchi, 3:
	"     There are %o relations and %o non-orientable edges.\n",#L,#non_orientables;
    return L;

end function;


function cusptype(M,alpha,cusplist)
    // given a minimal vector defining a cusp alpha and a list of standard
    // cusps, return the type.  If v is new, return 1+maxtype.  Append
    // v to list of cusplist and return it as well.
    OF := Integers(BaseField(M));
    alpha := unimodularize(M,alpha);
    a1 := alpha[1];
    a2 := alpha[2];
    a := ideal<OF | a1,a2>;
    level := Level(M);
    H,f := ClassGroup(BaseField(M));
    assert a + level eq 1*OF;
    aplist := [ ideal<OF | w[1], w[2]> : w in cusplist ];
    for type in [ 1..#cusplist ] do
	if aplist[type] eq a then
	    ap1 := cusplist[type,1];
	    ap2 := cusplist[type,2];
	    ap := ideal<OF | ap1,ap2>;
	    
	    btype := Position([I@@f : I in M`ModFrmData`ideal_reps],-(a@@f));
	    assert btype ne 0;
	    b := M`ModFrmData`ideal_reps[btype];
	    b1, b2 := Explode(Basis(b));
	    	    
	    M1 := abmat(a1,a2,b);
	    M2 := abmat(ap1,ap2,b);
	   
	    b1 := M1[1,2];
	    b2 := M1[2,2];
	    bp1 := M2[1,2];
	    bp2 := M2[2,2];
	    
	    if (a2*OF + level) eq (ap2*OF + level) then
		//abd2 := a*b*(a2*OF + level);  // I don't think this is right.   
		abd2 := OF!!(a^(-1) * b * ((a2*ap2)*OF) + a*b * level);
		tf := exists(u){u : u in M`ModFrmData`torsion_units |
		    a2*bp2 mod abd2 eq u*ap2*b2 mod abd2};
		if tf then
		    return type, cusplist;
		end if;
	    end if;
	end if;
    end for;
    // if it reaches here, then it is not conjugate to any so far.
    return #cusplist + 1, Append(cusplist,Eltseq(alpha));
end function;

    
procedure homologydata(M)
    //Attaches a record of the homology
    SetLevel(M);
    OF := Integers(BaseField(M));
    Coeff:=M`homology_coefficients;
    if not assigned  M`LevelData`homology`relations then 
	M`LevelData`homology`relations := relations(M);
    end if;
    M`LevelData`homology`coefficient_ring:=Coeff;

    if not assigned M`LevelData`homology`zero_sharbly_space then 	
	// now try to compute cuspidal part.
	
	boundary := [];
	cuspclasses := [Basis(a) : a in M`ModFrmData`ideal_reps];
	for GLtype in [1..#M`LevelData`one_orbits] do
	    for gamma in M`LevelData`one_orbits[GLtype]`gamma_list do
		alpha :=
		    Eltseq(gamma*Matrix(OF,1,M`ModFrmData`one_poly[GLtype]`O2_vertices[1]));
		atype,cuspclasses := cusptype(M,alpha,cuspclasses);
		beta :=
		    Eltseq(gamma*Matrix(OF,1,M`ModFrmData`one_poly[GLtype]`O2_vertices[2]));
		btype,cuspclasses := cusptype(M,beta,cuspclasses);
		type := [atype, btype];
		if GLtype in M`ModFrmData`zero_reversers then 
		    Append(~boundary,Reverse([atype, btype]));
		else
		    Append(~boundary,type);
		end if;
	    end for;
	end for;
	M`ModFrmData`cuspclasses := cuspclasses;
	
	
	zss:=RSpace(Coeff,M`LevelData`total_number_of_one_orbits);
	// Now need to kill off non-orientable cells and 1-sharbly relations
	rel := M`LevelData`homology`relations;
	mss,mf := quo<zss | rel >;
	
	
	
	// define map from homology space to 
	boundarymap := [];

	for i in [1..M`LevelData`total_number_of_one_orbits] do
	    col := [0 : i in [1..#cuspclasses]];
	    col[boundary[i,1]] := 1;
	    col[boundary[i,2]] +:= -col[boundary[i,1]];
	    Append(~boundarymap,col);
	end for;

	Z := RSpace(M`homology_coefficients,#cuspclasses);
	bmap := Hom(zss,Z)!boundarymap;



	for i in [1..#rel] do
	    assert IsZero(bmap(Vector(rel[i])));
	end for;

	cmap := Hom(mss,Z)![Eltseq(bmap(v@@mf)) : v in Basis(mss)];
	M`bmap := cmap;	
	H,f := NullSpace(cmap);
	M`LevelData`homology`zero_sharbly_space:=zss;
	M`LevelData`homology`H:=H;
	M`LevelData`homology`ToH:= mf; // map from zss to H.
	M`Dimension := Dimension(H);
	
	
	bm:=BasisMatrix(H);
	M`basis_matrix := bm;
	I:=IdentityMatrix(CoefficientRing(bm),NumberOfRows(bm)); 
	M`basis_matrix_inv:=
	    Transpose(Solution(Transpose(M`basis_matrix),I));
    end if;

end procedure;
