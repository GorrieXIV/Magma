//defs.m

freeze;

declare verbose Bianchi, 4;

declare attributes TorPol:
    oriented_facets;

ZeroSharblyRec:=recformat<
    vertices,//vertices in cone space
    O2_vertices,//vertices in O2
    lift_matrix,//lift matrix data
    coefficient,
    bary,
    is_voronoi_reduced,//boolean true if endpoints in standard polytope.
    containing_cell,//only for voronoi reduced sharbly, gives the cell
    //record of the cell containing the 0-sharbly
    GL_type,//GL-type of the edge.
    is_strongly_reduced// GL-conj to an edge, or degenerate
    >;

    
LevelRec:=recformat<
    level,//level as an element of O
    rF,//residue class field
    projective_space,//sets projective space
    projective_space_map,//sets projective space
    bottom_row_map,//map of matrix to bottom row in projective space
    total_number_of_zero_orbits,//number of 1 orbits
    total_number_of_one_orbits,//number of 1 orbits
    total_number_of_two_orbits,//number of 2 orbits
    total_number_of_three_orbits,//number of 3 orbits
    three_orbits,
    two_orbits,//orbit records for 2 dimensional polytopes
    one_orbits,
    good_a,//associative array of ideals a such that a^2*p is principal	
    homology//Homology record
    >;

HomologyRec:=recformat<
    zero_sharbly_space,//
    H,//homology as a quotient
    ToH,//map to quotient H
    coefficient_ring,// coeff ring of homology
    relations,//boundary relations
    cycles
    >;


	
PerfectFormRec:=recformat<
    form, //in cone space
    O2minimal_vectors,//as list of O2
    minimal_vectors //as list of vectors in cone space
    >;

OrbitRec:=recformat<
    rStab,//stabilizer subgroup image in GL_2(rF)
    entry,//a list giving the total order number of
    //each Gamma0 class to know where to put the entry
    //in the matrix for the boundary
    orbit_type, //line orbits
    total_number, //number of this type of orbit
    gamma_list,//This is a list of gamma in Gamma_0, such that
    //[0:1]*gamma = a0, where a0 is the first point in each orbit.
    //It is used to pick a representative of the polytope when
    //we compute homology.
    orbit_mover_list,
    //this is a list of g in Stab(cell) such that a sends the point
    //a to a0 in its orbit.  It is given in the order from
    //projective_list.
    orbit_number_list,
    //This is a list of +/- 1 that tells if a in orbit agrees or
    //disagrees with orientation of a0
    non_orientable_orbits //a sequence of the non-orientable orbits indices
	>;
    
CellRec:=recformat<
    O2_vertices,//vertices as vectors in O2
    bary, //barycenter
    cone_vertices,//vertices in conespace
    stabilizer,//Stabilizer group in PGL
    fullstabilizer,
    stabilizer_plus,// subset of the stabilizer that maintains
    //orientation.  only set for edges.
    polytope,//Polytope
    form,//if cell is topcone, put form in cone space 
    oriented_facets, //Oriented facets of the polytope, only used
    //for 2 dimensional polytopes
    GL_facet_types, //gives the GL types of the edges that are on
    //the boundary of the 2 dimensional polytopes.  Given as a list
    //of pairs <a,sgn,g>, where a is the GLtype and sgn is +/-
    //depending on if the orientation matches, and g takes std to this edge
    neighbors,//a list of the cells defining the neighbors of the cell.
    neighbors_mover, // a list of <i,gamma> where i in [1..#GLtypes]
    //tells which GL standard cell this neighbor is conjugate to
    //and gamma takes the neighbor to the standard cell_i.
    gamma,//Only for cusps, gives gamma in GL which sends standard to here
    GLtype,//gives GLtype
    graph,//only for 3 dimensional polytopes.  Gives the graph of edges.
    mover//gives g in Gamma such that g takes standard to cell
	>;


ModFrmDataRec:=recformat<
    in_G,//boolean if matrix is in G, where G is GL or SL
    G,//string GL or SL, default is GL
    standard_sharblies,//standard 0-sharblies in same order as one_poly
    cone_lattice,// rank 4 lattice with inner product
    cone_space,//4 dimensional cone space with inner product
    initial_form, //PerfectFormRec for an intitial perfect form
    three_poly, //list of CellRec for 3 dimensional polytopes
    two_poly, //list of CellRec for 2 dimensional polytopes;
    one_poly,  //list of CellRec for 1 dimensional polytopes
    zero_poly,
    torsion_units,//Torsion units
    dets,//determinants of edges
    O2_in_cone_space,//just precompute to speed things up
    O2_in_cone_space_ij,//just precompute to speed things up
    ideal_reps,//representatives of ideal classes that are prime to level
    cuspclasses,
    standardorder,
    Qstandardorder,
    zero_reversers
>;
	
	


