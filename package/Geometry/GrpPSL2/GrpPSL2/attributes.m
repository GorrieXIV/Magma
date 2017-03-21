freeze;

////////////////////////////////////////////////////////////////////
//                                                                //  
//                Congruence Subgroups of PSL2                    // 
//                                                                // 
////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////
//                                                                //
//                    Attribute declarations                      //
//                                                                // 
////////////////////////////////////////////////////////////////////

declare type GrpPSL2 [GrpPSL2Elt];

declare attributes GrpPSL2:
   MatrixGroup,   // 
   BaseRing,      // 
   EichlerOrder,  // Used to define a Shimura subgroup, i.e.   
                  // intersection of 2 maximal orders
		  // in a quaternion order.
   MatrixRepresentation,     // for Shimura groups 
   Level,         // least integer N such that
                  // Gamma(N) is contained in the group.
   // a congruence subgroup will be given by a list of
   // groups of the form Gamma_0(N), Gamma_1(N), Gamma(N),
   // Gamma^0(N) and Gamma^1(N), and congugates of these;
   // the following lists define these groups
   gammaType_list, // sequence of sequences of 3 integers:
   // a sequence of 3 integers (n,m,p) represents
   // Gamma_0(N) intersect Gamma_1(M) intersect Gamma^0(P)
   // or
   // Gamma_0(N) intersect Gamma^1(M) intersect Gamma^0(P)
   // must have M divides NP
   conjugate_list, // sequence of matrices in MatrixGroup:
   // conjugating matrices for each element in
   // gamma type_list.
   //   character_list, // we allow a character to be used to
   //                // define the group on the diagonal.
   subgroup_list, // allow a list of subgroups; this will
                  // replace  the charlist argument.
                  // According to the documentation,
                  // the condition imposed by subgroup_list
                  // was intended to be that diagonal entries 
                  // of the matrix take value 1 for the character(s)
                  // in subgroup_list.
                  // I had to make a change in the MemberTest 
                  // function to get this correct.   --- Steve
   // Where computed, give the following:
   cusps,           // points in Cusps()
   cusp_widths,     // widths of cusps in cusp list, when
                    // G is in PSL_2(Z).
   elliptic_points, // points of type SpcHypElt
   Generators,    // where computed
   // data related to Atkin Lehner involutions:
   IsNormalizer,
   LevelFactorization,    // Factorization of N
   AtkinLehnerInvolutions,  // this is a subspace of F_2^r
   // Farey Symbol data:
   FS_labels,
   FS_cusps,
   FS_generators,
   FS_cosets,
   FS_gen_edges,
   FS_widths,
   FS_otherEdges,
   FS_glue_list;  // currently this is assigned in the function
                  // FindWord in words_for_matrices.m


declare type GrpPSL2Elt;

declare attributes GrpPSL2Elt:
   Parent,
   Element;


////////////////////////////////////////////////////////////////////
//                                                                //
//                         Printing                               //
//                                                                //
////////////////////////////////////////////////////////////////////

function find_factor(a,b)
   // given integers a,b with a|b,
   // this function finds c such that
   // there is a d such that d||a and d||b and d*c=b
   // (there may be a better way to achieve this!)
   divs:=PrimeDivisors(Gcd(a,b div a));
   d := Facint(SeqFact([f : f in Factorization(a) | f[1] notin divs]));
   return b div d;
end function;
   

function gammaIntersectiontionList(gammatype)
    // given a sequence list [N,M,P],
    // want to return a sequence [A,B1,B2,B3,C,D,E]
    // so that the group is
    // Gamma_0(A) intersect Gamma_1(B1)
    // inteserect Gamma(B2) intersect Gamma^1(B3)
    // intersect Gamma^0(C)
    // intersect Gamma_1(D) conjugated by [E,0;0,1]
    // where the integers are all as small as possible.
    // We assume that N divides M*P
    M,N,P := Explode(gammatype);    
    g1 := Gcd(gammatype);
    M1 := find_factor(g1,M);
    N1 := find_factor(g1,N);
    P1 := find_factor(g1,P);
    g2 := Gcd(M1,N1);
    M2 := find_factor(g2,M1);
    N2 := find_factor(g2,N1);
    g3 := Gcd(N2,P1);
    N3 := find_factor(g3,N2);
    P3 := find_factor(g3,P1);
    E  := N3 div Gcd(N3,M);
    return [M2,g2,g1,g3,P3,N3,E];
end function;

function gammastring(N,script)
    return "Gamma" cat script cat Sprintf("(%o)",N);
end function;


function gammaGroupString(gammatype)
    // this prints the group correponding to gammatype=[a,b,c]
    level := gammaIntersectiontionList(gammatype);    
    string := ["" : i in [1..5]];
    scripts :=["_0","_1","","^1","^0"];
    start := 1;
    for i:=5 to 1 by -1 do
       if level[i] ne 1 then
	  start := i;
	  string[i] := gammastring(level[i],scripts[i]);
       end if;
    end for;
    output := string[start];
    for i in [(start+1)..5] do
       if string[i] ne "" then
	  output := output cat " intersection " cat string[i];
       end if;
    end for;
    l6 := level[6];
    if l6 ne 1 then
       output := output cat " intersection (" cat gammastring(l6,"_1") cat
       Sprintf(" congugated by\n%o )",Matrix(2,2,[level[7],0,0,1]));
    end if;
    return output;
end function;
	
intrinsic Print(G::GrpPSL2, level::MonStgElt)
    {}    
    if assigned G`IsNormalizer and G`IsNormalizer then
       // Note: computation of normalizer not yet implemented.
       printf "Normalizer in PSL_2(R) of ";
    end if;
    if Type(BaseRing(G)) in {AlgQuat,AlgQuatOrd,AlgAssVOrd} then
       printf "Arithmetic Fuchsian group arising from order of %o", 
          Algebra(BaseRing(G));	
       return;
    end if;
    if assigned G`ShimData then
       printf "Arithmetic Fuchsian group arising from order of level of norm %o in a quaternion algebra of discriminant of norm %o over %o", 
          Norm(G`ShimData[3]), Norm(G`ShimData[2]), G`ShimData[1];
       return;
    end if;
    num := #(G`gammaType_list);
    // Note: currently num should always be 1.
    for i in [1..num] do
	if G`gammaType_list[i] eq [1,1,1] then
	    printf "PSL2(%o)", BaseRing(G);
	else
	    if num gt 1 or G`conjugate_list[i] ne G`MatrixGroup!1 then
		printf "(";
	    end if;
	    printf gammaGroupString(G`gammaType_list[i]);
	    if num gt 1 then
		printf ")";
	    end if;
	end if;
	if G`conjugate_list[i] ne G`MatrixGroup!1 then
	    printf " conjugated by %o ", G`conjugate_list[i]; 
	end if;
	if assigned  G`subgroup_list then
	   // Warning: this is not quite correct, but
	   // the use of characters is not properly
	   // implemented yet anyway.
	   printf " with character %o", G`subgroup_list[i];
	end if;
	if i lt #(G`gammaType_list) then
	    printf " intersection ";
	end if;
    end for; 
end intrinsic;

intrinsic Print(A::GrpPSL2Elt, level::MonStgElt)
   {}
   printf "%o", A`Element;
end intrinsic;

  


