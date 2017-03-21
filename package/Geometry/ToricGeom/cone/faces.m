freeze;

////////////////////////////////////////////////////////////////////////
// faces.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 27125 $
// $Date: 2010-06-04 12:14:46 +1000 (Fri, 04 Jun 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for manipulating faces of cones.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// Initially the face F of cone C is known iff F (as a TorCon) is in the
// sequence C`faces_cones. Later we may suppress this and allow faces
// known only by supporting hyperplane, dual face, etc.
// When user tests (positively) any cone for being a face of C, we throw
// that cone into C`faces_cones.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": seq_of_k_subsets, negate_sequence;
import "cone.m": duplicate_cone;
import "generators.m": cone_has_inequalities, are_R_generators_minimal;

declare attributes TorCon:
    number_of_faces,        // The number of faces (sequence) 
    euler_char,             // Euler Characteristic = sum (-1)^dim for every
                            // face of C, including 0 (if stricly convex) and C
                            // itself; it is either (-1)^(dim C) if C is a
                            // linear space or 0 for other cases (so most
                            // often). Can be used for predicting the number of
                            // faces.
    faces_cones,            // Seq of underlying cones for known faces
    faces_indices,          // Seq of indices of above 
    faces_indices_top,      // All faces_indices lt this number are calculated
    faces_numbers_of_known_subfaces, // Sequence of ints; i-th entry is n says
                            // that C already knows subfaces of numbers [1..n]
                            // of F, where F is i-th face of C
    faces_duals,            // Seq of indices of dual face in the dual cone
    faces_supports,         // Seq of supporting inequalities of known faces
    faces_all,              // Seq of BoolElt; i-th elt is true iff all
                            // cones of codim i are already known.
    faces_all_all,          // BoolElt, if true, then cone knows all its faces
                            // in every dim. 
    faces_all_last_check,
    faces_all_all_last_check,
    faces_codim_seq,
    faces_codim_seq_last_check;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Copies the data from "C" to "dC".
procedure faces_copy(C,dC)
    if assigned C`number_of_faces then
        dC`number_of_faces:=C`number_of_faces; end if;
    if assigned C`euler_char then
        dC`euler_char:=C`euler_char; end if;
    if assigned C`faces_cones then
        dC`faces_cones:=[duplicate_cone(F) : F in C`faces_cones]; end if;
    if assigned C`faces_indices then
        dC`faces_indices:=C`faces_indices; end if;
    if assigned C`faces_indices_top then
        dC`faces_indices_top:=C`faces_indices_top; end if;
    if assigned C`faces_numbers_of_known_subfaces then
        dC`faces_numbers_of_known_subfaces:=C`faces_numbers_of_known_subfaces;
    end if;
    if assigned C`faces_duals then
        dC`faces_duals:=C`faces_duals; end if;
    if assigned C`faces_supports then
        dC`faces_supports:=C`faces_supports; end if;
    if assigned C`faces_all then
        dC`faces_all:=C`faces_all; end if;
    if assigned C`faces_all_last_check then
        dC`faces_all_last_check:=C`faces_all_last_check; end if;
    if assigned C`faces_all_all_last_check then
        dC`faces_all_all_last_check:=C`faces_all_all_last_check; end if;
    if assigned C`faces_codim_seq then
        dC`faces_codim_seq:=C`faces_codim_seq; end if;
    if assigned C`faces_codim_seq_last_check then
        dC`faces_codim_seq_last_check:=C`faces_codim_seq_last_check; end if;
end procedure;

// Sets the data of "dC" equal to minus "C".
procedure faces_minus(C,dC)
    if assigned C`number_of_faces then
        dC`number_of_faces:=C`number_of_faces; end if;
    if assigned C`euler_char then
        dC`euler_char:=C`euler_char; end if;
    if assigned C`faces_cones then
        dC`faces_cones:=negate_sequence(C`faces_cones); end if;
    if assigned C`faces_indices then
        dC`faces_indices:=C`faces_indices; end if;
    if assigned C`faces_indices_top then
        dC`faces_indices_top:=C`faces_indices_top; end if;
    if assigned C`faces_numbers_of_known_subfaces then
        dC`faces_numbers_of_known_subfaces:=C`faces_numbers_of_known_subfaces;
    end if;
    if assigned C`faces_duals then
        dC`faces_duals:=C`faces_duals; end if;
    if assigned C`faces_supports then
        dC`faces_supports:=negate_sequence(C`faces_supports); end if;
    if assigned C`faces_all then
        dC`faces_all:=C`faces_all; end if;
    if assigned C`faces_all_last_check then
        dC`faces_all_last_check:=C`faces_all_last_check; end if;
    if assigned C`faces_all_all_last_check then
        dC`faces_all_all_last_check:=C`faces_all_all_last_check; end if;
    if assigned C`faces_codim_seq then
        dC`faces_codim_seq:=C`faces_codim_seq; end if;
    if assigned C`faces_codim_seq_last_check then
        dC`faces_codim_seq_last_check:=C`faces_codim_seq_last_check; end if;
end procedure;

// Sets the data of "dC" equal to "C", but with the ambient changed to "L".
procedure faces_change_ambient(C,dC,L)
    if assigned C`number_of_faces then
        dC`number_of_faces:=C`number_of_faces; end if;
    if assigned C`euler_char then
        dC`euler_char:=C`euler_char; end if;
    if assigned C`faces_cones then
        dC`faces_cones:=[ChangeAmbient(F,L) : F in C`faces_cones]; end if;
    if assigned C`faces_indices then
        dC`faces_indices:=C`faces_indices; end if;
    if assigned C`faces_indices_top then
        dC`faces_indices_top:=C`faces_indices_top; end if;
    if assigned C`faces_numbers_of_known_subfaces then
        dC`faces_numbers_of_known_subfaces:=C`faces_numbers_of_known_subfaces;
    end if;
    if assigned C`faces_duals then
        dC`faces_duals:=C`faces_duals; end if;
    if assigned C`faces_supports then
        dC`faces_supports:=[Dual(L) | Dual(L) ! H : H in C`faces_supports];
    end if;
    if assigned C`faces_all then
        dC`faces_all:=C`faces_all; end if;
    if assigned C`faces_all_last_check then
        dC`faces_all_last_check:=C`faces_all_last_check; end if;
    if assigned C`faces_all_all_last_check then
        dC`faces_all_all_last_check:=C`faces_all_all_last_check; end if;
    if assigned C`faces_codim_seq then
        dC`faces_codim_seq:=C`faces_codim_seq; end if;
    if assigned C`faces_codim_seq_last_check then
        dC`faces_codim_seq_last_check:=C`faces_codim_seq_last_check; end if;
end procedure;

// Returns the Euler Characteristic of C
function euler_characteristic(C)
    if not assigned C`euler_char then 
        C`euler_char:=IsLinearSpace(C) select (-1)^(Dimension(C)) else 0;
    end if;
    return C`euler_char;
end function;

// Checks if TorCon F is on the list of known faces of C 
function is_known_face(C,F) 
    return assigned C`faces_cones and F in C`faces_cones;
end function;

// Returns the number of known faces
function number_of_known_faces(C)
    if not assigned C`faces_cones then 
        return 0;
    end if;
    return #C`faces_cones;
end function;

// Checks if the face data of faces of C is known to C. 
// I.e., if F1 is a face of F2 and F2 is a face of C, then F1 becomes a face of
// C (unless C already knows about F1).
forward include_cone_in_faces;
forward has_all_faces;
procedure get_cone_faces_from_faces(C)
    if not has_all_faces(C : check:=false) then
        if not assigned C`faces_numbers_of_known_subfaces then 
            C`faces_numbers_of_known_subfaces:=[Integers()|];
        end if;
        i:=0;
        while i lt number_of_known_faces(C) do 
            i +:= 1;
            F:=C`faces_cones[i];
            if not IsDefined(C`faces_numbers_of_known_subfaces,i) then 
                C`faces_numbers_of_known_subfaces[i]:=0;
            end if;
            for j in [C`faces_numbers_of_known_subfaces[i] + 1..
                                                number_of_known_faces(F)] do
                include_cone_in_faces(C,F`faces_cones[j]);
            end for;
            C`faces_numbers_of_known_subfaces[i]:=number_of_known_faces(F);
        end while;
    end if;
end procedure;

function known_cone_faces(C : get_from_faces:=true)
    if not assigned C`faces_cones then
        C`faces_cones:=[PowerStructure(TorCon)|];
    end if;
    if get_from_faces then 
        get_cone_faces_from_faces(C);
    end if;
    return C`faces_cones;
end function;

// Returns the set of integers S, with i is in S iff i-th MinRGen of C is in F.
// This is the set of indices for face F of C.  
function make_indices_for_cone(C,F)
        RgensC:=MinimalRGenerators(C);
        if are_R_generators_minimal(F) then 
             RgensF:=MinimalRGenerators(F);
             set:={Integers() | i : i in [1..#RgensC] | RgensC[i] in RgensF};
             if #set eq #RgensF then
                return set;
             end if;
        end if;
        return {Integers() | i : i in [1..#RgensC] | RgensC[i] in F};
end function;

// Returns the indices of minimal R generators of known_cone_faces(C)[k] 
// in minimal R generators of C 
function get_face_indices(C,k)
    if not assigned C`faces_indices then 
        C`faces_indices:=[PowerSet(Integers())|];
    end if;
    if not IsDefined(C`faces_indices, k) then 
        F:=known_cone_faces(C: get_from_faces:=false)[k];
	C`faces_indices[k]:=make_indices_for_cone(C,F);
    end if;
    return C`faces_indices[k];
end function;

// Returns the sequence of indices of minimal R generators of known_cone_faces(C)[k] 
// in minimal R generators of C for all k.
function get_all_face_indices(C)
    if not assigned C`faces_indices_top then 
        C`faces_indices_top:=0;
    end if;
    if not assigned C`faces_indices then 
        C`faces_indices:=[PowerSet(Integers())|];
    end if;
    n:=number_of_known_faces(C);
    for i in [C`faces_indices_top+1..n] do
        _:=get_face_indices(C,i);
    end for;
    C`faces_indices_top:=n;
    return C`faces_indices;
end function;

// A sequence of sequences of integers S, such that S[d] is an increasing sequence 
// with the following property:
//  i in S[d] iff codimension of known_cone_faces(C)[i] eq d
function get_codim_seq(C);
    dimC:=Dimension(C);
    if not assigned C`faces_codim_seq then 
        C`faces_codim_seq:=[PowerSequence(Integers()) | [Integers()|] :
                                                            i in [1..dimC]];
    end if;
    if not assigned C`faces_codim_seq_last_check then 
        C`faces_codim_seq_last_check:=0;
    end if;
    cones:=known_cone_faces(C: get_from_faces:=false);
    n:=#cones;
    for i in [C`faces_codim_seq_last_check + 1..n] do
	   Append(~C`faces_codim_seq[dimC - Dimension(cones[i])], i);
    end for;
    C`faces_codim_seq_last_check:=n;
    return C`faces_codim_seq;
end function;

// The number of known faces of the given codimension
function number_of_known_faces_of_codim(C,k : get_from_faces:=true)
    return #get_codim_seq(C)[k];
end function;

// Returns the list of all known faces of C which have codim k in C. Also gets
// faces from subfaces.
function get_known_faces_of_codim(C,k)
    faces:=known_cone_faces(C);
    if k gt Dimension(C) or k le 0 then 
        return [PowerStructure(TorCon)|];         
    end if;
    dim_seq:=get_codim_seq(C)[k];
    return faces[dim_seq];
end function;

// Sets all faces of C of codim k in C.
procedure set_faces_all(C,k: iterate:=true)
    if not assigned C`faces_all then 
        C`faces_all:=[Booleans()|];
    end if;
    C`faces_all[k]:=true;
    if iterate then 
        for F in known_cone_faces(C : get_from_faces:=false)[&cat get_codim_seq(C)[1..k]] do 
            codim:=Dimension(C) - Dimension(F);
            if codim lt k then 
                $$(F,k - codim : iterate:=false);
            end if;
        end for;
    end if;
end procedure;

// True iff C already has enough info to decide the number of faces of codim k 
function can_get_number_of_faces(C,k : iterate:=true)
    if k gt Dimension(C) or k le 0 then 
        return true;
    end if;
    if not assigned C`number_of_faces then 
        C`number_of_faces:=[Integers()|];
    end if;
    if not IsDefined(C`number_of_faces,k) then
        if IsSimplicial(C) then
            // if C is simplicial, that is easy. 
            C`number_of_faces[k]:=Binomial(Dimension(C),k);
        else
            // We calculate the dimension of linear subspace contained in C 
            dual_codim:=Dimension(Ambient(C)) - Dimension(Dual(C));
            if k eq Dimension(C) - dual_codim - 1 then 
                // In this case we are basically asking for rays (if codim = 0)
                // or for the first non-trivial faces
                n_gens:=#MinimalRGenerators(C);
                C`number_of_faces[k]:=n_gens -
                            (IsZero(dual_codim) select 0 else dual_codim + 1);
            elif k eq 1 then 
                // In this case we are asking for facets
                codim:=Dimension(Ambient(C)) - Dimension(C);
                n_ineqs:=#MinimalInequalities(C);
                C`number_of_faces[k]:=n_ineqs -
                            (IsZero(codim) select 0 else codim + 1);
            elif k eq Dimension(C)-dual_codim then
                // In this case we are basicly asking for vertex (if codim = 0)
                C`number_of_faces[k]:=1;
            elif k gt Dimension(C) - dual_codim then 
                // If codim > 0 then there is nothing
                C`number_of_faces[k]:=0;
            elif assigned C`faces_all and IsDefined(C`faces_all,k) and
                                                            C`faces_all[k] then
                // Perhaps we already know that we have all the faces?
                C`number_of_faces[k]:=number_of_known_faces_of_codim(C,k); 
            elif iterate and &and[$$(C,i: iterate:=false) :
                             i in [1..Dimension(C) - dual_codim] | i ne k] then 
                // Maybe we can get the number from the Euler characteristic?
                C`number_of_faces[k]:=
                    (-1)^(k + 1) * (            // Oposite of sign at k-th term 
                    euler_characteristic(C)     // The characteristic
                    + (-1)^(Dimension(C) + 1)   // The term for C
                    - &+[(-1)^(Dimension(C) - i) * C`number_of_faces[i] 
                    : i in [1..Dimension(C) - dual_codim] | i ne k]);
            end if;
        end if;
    end if;
    return IsDefined(C`number_of_faces,k);
end function;

// True iff C knows all its faces of codim k.
function has_all_faces_of_codim(C,k : get_from_faces:=true)
    if k le 0 or k gt Dimension(C) then 
        return true;
    end if;
    if not assigned C`faces_all_last_check then 
        C`faces_all_last_check:=[Integers()|];
    end if;
    if not IsDefined(C`faces_all_last_check,k) then 
        C`faces_all_last_check[k]:=0;
    end if;
    if not assigned C`faces_all then 
        C`faces_all:=[Booleans()|];
    end if;
    if not IsDefined(C`faces_all,k) then 
        C`faces_all[k]:=false;
    end if;
    if get_from_faces then 
        get_cone_faces_from_faces(C);
    end if;
    n:=number_of_known_faces_of_codim(C,k);
    if n lt C`faces_all_last_check[k] then 
        if not C`faces_all[k] then
            if can_get_number_of_faces(C,k) then
                if n eq C`number_of_faces[k] then 
                    set_faces_all(C,k);
                end if;
            elif $$(C, k-1) and &and[Booleans() | $$(c, 1) :
                                    c in get_known_faces_of_codim(C,k-1)] then 
                set_faces_all(C,k);
            end if;
        end if;
        C`faces_all_last_check[k]:=n;
    end if;
    return C`faces_all[k];
end function;

// True iff C already knows all its faces.
// If 'check' is true, then it actually tests if the known faces are all.
// If 'check' is false, then it only reads the attribute. Used to avoid
// infinite loops. 
function has_all_faces(C : check:=true)
    if not assigned C`faces_all_all then 
        C`faces_all_all:=false;
    end if;
    if check then 
        if not assigned C`faces_all_all_last_check then 
           C`faces_all_all_last_check:=0;
        end if;
        n:= #known_cone_faces(C);
        if  C`faces_all_all_last_check lt n then 
            C`faces_all_all:=&and[Booleans() | has_all_faces_of_codim(C,k) :
                                                        k in [1..Dimension(C)]];
            C`faces_all_all_last_check:=n;
        end if;
    end if;
    return C`faces_all_all;
end function;

// If F1 and F2 are faces of C, then checks if F1 subset F2. If so, then F1 is
// included in faces of F2. 
procedure propagate_face(C,k)
    cones:=known_cone_faces(C : get_from_faces:=false);
    cone:=cones[k];
    dim_cone:=Dimension(cone);
    cone_indices:=get_face_indices(C,k);
    for i in [1..k-1] cat [k+1..#cones] do
        c:=cones[i];
        c_indices:=get_face_indices(C,i);
        dim_c:=Dimension(cones[i]);
        if not has_all_faces_of_codim(cone,dim_cone-dim_c:get_from_faces:=false)
          and c_indices subset cone_indices then
            include_cone_in_faces(cone,c : propagate:=false);
        elif not has_all_faces_of_codim(c,dim_c-dim_cone:get_from_faces:=false)
          and cone_indices subset c_indices then
            include_cone_in_faces(c,cone : propagate:=false);
        end if;
    end for;
end procedure;

// Adds F to the list of known faces of C. 
// Note: Assumes F is not on the list. Assumes F really is a face of C.
procedure add_cone_to_faces(C,F : propagate:=true, indices:=false)
    if not assigned C`faces_cones then 
        C`faces_cones:=[F];
        if not indices cmpeq false then 
            C`faces_indices:=[indices];
        end if;
    else
        Append(~C`faces_cones,F);
        n:=number_of_known_faces(C);
        if not indices cmpeq false then 
            if not assigned C`faces_indices then 
                C`faces_indices:=[PowerSequence(Integers())|];
            end if;
            C`faces_indices[n]:=indices;
        end if;
        if propagate then 
            propagate_face(C,n);
        end if;
    end if;
end procedure;

// Adds F to the list of known faces of C, unless F is already there 
// Note: Assumes F really is a face of C. Does not check faces of faces.
procedure include_cone_in_faces(C,F: propagate:=true)
    codim:=Dimension(C) - Dimension(F);
    if not has_all_faces_of_codim(C, codim: get_from_faces:=false) then 
// We need to determine if the F is already known to C. 
// We have a few options:
// Version 1: Get the indices of this face, and of all faces of C. This,
// however, turns out to be slightly more expensive.
//      set:=make_indices_for_cone(C,F);
//      ind:=Index(get_all_face_indices(C), set);
// Version 2: Get the index of F in the sequence of all faces of C. It works
// reasonably well.
//      ind:=Index(known_cone_faces(C: get_from_faces:=false), F); 
//      set:=false;
// Version 3: Instead try constructing the smaller sequence with only cones of
// the right dimension. At the moment it seems to be the fastest. In general it
// might be worth to store faces sorted by codimension, thus avoiding
// reconstructing the sequence.
        ind:=Index(known_cone_faces(C :
                    get_from_faces:=false)[get_codim_seq(C)[codim]], F); 
        set:=false;
        if IsZero(ind) then 
            add_cone_to_faces(C,F: propagate:=propagate, indices:=set);
        end if; 
    end if;
end procedure;

// Does k-th face of C know its supporting hyperplane?
function has_face_support(C,k)
    return assigned C`faces_supports and IsDefined(C`faces_supports,k);
end function;

// Support of k-th face of C.
// Note: Assumes it is known.
function face_support(C,k)
    return C`faces_supports[k];
end function;

// Sets support of k-th face of C to be v.
procedure set_face_support(C,k, v)
    if not assigned C`faces_supports then
        C`faces_supports:=[Dual(Ambient(C))|];
    end if;
    C`faces_supports[k]:=v;
end procedure;

// Returns the index of F among the known faces of C, 0 otherwise.
function known_face_index(C,F)
    if not assigned C`faces_cones then return 0; end if;
    return Index(known_cone_faces(C),F);
end function;

// Adds missing faces to known faces in C. 'missing' is a set of sets of
// integers, representing indices of the MinRGens of C.
// Assumes MinRGens were calculated before and these are really faces, and that
// they are not known to C yet. If simplicial is true, then assumes that all
// these faces are simplicial.
procedure faces_constructor_add_missing_faces(C,missing : simplicial:=false)
    Rgens:=MinimalRGenerators(C);
    for set in missing do
        F:=Cone(Rgens[Sort(Setseq(set))]);
        if simplicial then 
            F`dim:=#set;
            F`is_simplicial:=true;
        end if;
        F`are_Rgens_minimal:=true;
        add_cone_to_faces(C,F: indices:=set);
    end for;
end procedure;

// Construct the set of indices for faces of C of dim d, assuming C is
// simplicial. If k=-1, then constructs all of them.
function faces_constructor_indices_simplicial(C,d)
    S:=known_cone_faces(C);
    Rgens:=MinimalRGenerators(C);
    set:={1..#Rgens};
    if d eq -1 then
        missing:=Subsets(set);
    else 
        missing:=Subsets(set,d);
    end if;
    return missing diff (Seqset(get_all_face_indices(C)) join {set});
end function;

function faces_constructor_intersecting_sets(faces_indices)
    all_faces:=faces_indices;
    repeat
        n :=#all_faces;
        all_faces join:= {&meet S : S in Subsets({F : F in all_faces},2)};
    until n eq #all_faces;
    return Setseq(all_faces diff faces_indices);
end function;

function faces_constructor_indices_non_simplicial(C,d)
    Rgens:=MinimalRGenerators(C);
    _:=Facets(C);
    faces_indices:=Seqset(get_all_face_indices(C));
    if IsEmpty(faces_indices) then 
         return {PowerSet(Integers())|};
    end if;
    if IsStrictlyConvex(C) then
        all_faces:=faces_indices;
        all_faces_have:={Integers()|};
        r:=0;
    else
        all_faces_have:=&meet faces_indices;
        all_faces:={F diff all_faces_have : F in faces_indices};
        if d ne -1 then
            r:=Rank(Matrix(Rgens[Setseq(all_faces_have)]));
        end if;
    end if;
    all:=faces_constructor_intersecting_sets(all_faces);
    if d eq -1 then
        known:=Seqset(get_all_face_indices(C));
    else
        all:={PowerSet(Integers())| set : set in all | Rank(Matrix(Rgens[Setseq(set)])) eq d-r};
        known:={get_face_indices(C,k) : k in get_codim_seq(C)[Dimension(C)-d]};
    end if;
    return {i join all_faces_have : i in all} diff known;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic IsFace(C::TorCon, F::TorCon)-> BoolElt
{True iff the cone F is a face of the cone C}
    L:=Ambient(C);
    require L eq Ambient(F): "Cones must lie in the same space";     
    // First we check if we already have this face on our list
    get_cone_faces_from_faces(C);
    if is_known_face(C,F) then 
        return true;
    end if;
    codim:=Dimension(C)- Dimension(F);
    if codim eq 0 then
        return C eq F;
    end if;
    if has_all_faces_of_codim(C,codim) then
        return false;
    end if;
    if IsZero(F) then 
        if IsStrictlyConvex(C) then 
            add_cone_to_faces(C,F);
            return true;
        else
            return false;
        end if;
    end if;
    support:=SupportingHyperplane(C,F);
    // If the supporting form is zero, then F is not contained in any proper
    // face of C. So it is enough to compare if F eq C.
    if IsZero(support) then
        return F eq C;
    end if;
    // Otherwise F is a face iff F eq (C meet (support=0)). 
    // This is iff F subset C and (C meet (support=0)) subset F. 
    // Note: +support already is an inequality of C, so it is enought to add
    // -support. We do not want to constuct the extra cone spanned by -support.
    // We want to contstruct as few hackobjs as possible.
    bool:=F subset C and Dual(F) subset Cone(Append(Inequalities(C),-support));
    // If this is true, then we add F to the known faces of C
    if bool then  
        add_cone_to_faces(C,F);
        set_face_support(C,number_of_known_faces(C),support); 
    end if;
    return bool;
end intrinsic;

intrinsic NumberOfFacets(C::TorCon) -> RngIntElt
{The number of facets of the cone C}
    assert can_get_number_of_faces(C,1);
    return C`number_of_faces[1];
end intrinsic;

intrinsic Facets(C::TorCon) -> SeqEnum[TorCon]
{A sequence of facets of the cone C}
    S:=get_known_faces_of_codim(C,1);
    if not has_all_faces_of_codim(C,1) then
        if IsSimplicial(C) then
            // If the cone is simplicial, this is easy
            mingens:=MinimalRGenerators(C);
            if IsEmpty(S) then 
                missing:=seq_of_k_subsets(mingens,Dimension(C) - 1);
            else
                missing:=[Exclude(mingens,R) : R in MinimalRGenerators(S[1]) |
                             &and[R in MinimalRGenerators(s) : s  in S[2..#S]]];
            end if;
            for set in missing do
                F:=Cone(set);
                F`dim:=Dimension(C) - 1;
                F`are_Rgens_minimal:=true;
                F`is_simplicial:=true;
                Append(~S,F);
                add_cone_to_faces(C,F);
            end for;
        else
            // Otherwise we need to do more work
            L:=Ambient(C);
            ineqs:=MinimalInequalities(C);
            if IsMaximumDimensional(C) then
                // if C is of max dim, then the supporting hyperplane is unique
                // and we can eliminate creating some cones:
                supports_S:={Dual(L) | SupportingHyperplane(C,F) : F in S};
                ineqs:=[Dual(L) | H : H in ineqs | not H in supports_S];
                IRgens:=[PowerSequence(L) | [L | gen : gen in RGenerators(C)
                                                  | H * gen eq 0] : H in ineqs];
            else
                // If not, then we are not interested in some of the
                // inequalities (that do not give facets).
                ineqs:=[Dual(L) | H : H in ineqs |
                                    not &and[r * H eq 0 : r in RGenerators(C)]];
                CRgens:=RGenerators(C);
                SRgens:=[PowerSequence(Integers()) | [Integers() | i :
                                  i in [1..#CRgens] | CRgens[i] in F] : F in S];
                i:=1;
                IRgens:=[PowerSequence(L)|];
                while i le #ineqs do
                    H:=ineqs[i];
                    rgens:=[Integers() | j : j in [1..#CRgens] |
                                                            H * CRgens[j] eq 0];
                    j:=Index(SRgens,rgens);
                    if IsZero(j) then 
                        Append(~IRgens,[L | CRgens[k] : k in rgens]);
                        i +:= 1;
                    else
                        Remove(~ineqs,i);
                        Remove(~SRgens,j);
                    end if;
                end while;
            end if;    
            for i in [1..#ineqs] do
                H:=ineqs[i];
                rgens:=IRgens[i];
                F:=ConeWithInequalities(Append(Inequalities(C),-H));
                F`Rgens:=rgens;
                F`dim:=Dimension(C) - 1;
                if are_R_generators_minimal(C) then
                    F`are_Rgens_minimal:=true;
                end if;
                Append(~S,F);
                add_cone_to_faces(C,F);
                set_face_support(C,number_of_known_faces(C),H);
            end for;
        end if;
        set_faces_all(C,1);
    end if;
    return S;
end intrinsic;

intrinsic Faces(C::TorCon) -> SeqEnum[SeqEnum[TorCon]]
{A sequence of sequences of cones, where the (i + 1)-th sequence contains the i-dimensional faces of the cone C}
    if not has_all_faces(C) then 
        // If C is simplicial this is easy
        if IsSimplicial(C) then
            missing:=faces_constructor_indices_simplicial(C,-1);
            faces_constructor_add_missing_faces(C,missing : simplicial:=true);
        else
            // Otherwise we have to do more work
            missing:=faces_constructor_indices_non_simplicial(C,-1);
            faces_constructor_add_missing_faces(C,missing);
        end if;
        for i in [2..Dimension(C)] do 
            set_faces_all(C,i);
        end for;
    end if;
    return [get_known_faces_of_codim(C,i) : i in [Dimension(C)..1 by -1]];
end intrinsic;

intrinsic Faces(C::TorCon, i::RngIntElt) -> SeqEnum[TorCon]
{The sequence of i-dimensional faces of the cone C}
    if i eq Dimension(C) then 
        return [C];
    end if;
    if i eq Dimension(C) - 1 then 
        return Facets(C);
    end if; 
    // We check if we already know all the faces. Note that if C is not strictly
    // convex and i is small, then we are done.
    if not has_all_faces_of_codim(C,Dimension(C) - i) then
        if IsSimplicial(C) or (i in {0,1} and IsStrictlyConvex(C)) then
            missing:=faces_constructor_indices_simplicial(C,i);
            faces_constructor_add_missing_faces(C,missing : simplicial:=true);
        else
            missing:=faces_constructor_indices_non_simplicial(C,i);
            faces_constructor_add_missing_faces(C,missing);
        end if;
        set_faces_all(C,Dimension(C) - i);
    end if;
    return get_known_faces_of_codim(C,Dimension(C) - i);
end intrinsic;

intrinsic FaceSupportedBy(C::TorCon, H::TorLatElt) -> TorCon
{The face of the cone C supported by the hyperplane defined by H}
    L:=Ambient(C);
    require IsInDual(H,L):
        "Argument 2 must be a form on the ambient lattice of argument 1";
    require &and[r * H ge 0 : r in RGenerators(C)]:
        "Argument 2 does not support any face of argument 1";
    if IsZero(H) or &and[IsZero(r * H)  : r in RGenerators(C)] then 
        return C;
    end if;
    Rgens:=MinimalRGenerators(C);
    indices:={Integers() | i : i in [1..#Rgens] | Rgens[i] * H eq 0};
    ind:=Index(get_all_face_indices(C),indices);
    if IsZero(ind) then
        F:=Cone([Universe(Rgens) | Rgens[i] : i in Sort(Setseq(indices))]);
        if assigned C`is_simplicial and IsSimplicial(C) then
            F`is_simplicial:=true;
        end if;
        if assigned C`is_smooth and C`is_smooth then
            F`is_smooth:=true;
        end if;
        if assigned C`is_terminal and C`is_terminal then
            F`is_terminal:=true;
        end if;
        if assigned C`is_canonical and C`is_canonical then
            F`is_canonical:=true;
        end if;
        F`are_Rgens_minimal:=true;
        if cone_has_inequalities(C) then
            D:=Dual(F);
            D`Rgens:=Append(Inequalities(C),-PrimitiveLatticeVector(H));
        end if;
        add_cone_to_faces(C,F);
        set_face_support(C,number_of_known_faces(C),PrimitiveLatticeVector(H)); 
    else
        if not has_face_support(C,ind) then
            set_face_support(C,ind,PrimitiveLatticeVector(H));
        end if;
        F:=C`faces_cones[ind];
    end if;
    return F;
end intrinsic;

intrinsic SupportingHyperplane(C1::TorCon, C2::TorCon) -> TorLatElt
{The form on the ambient of C1, which vanishes on C2 and C1 is on positive side and such that the dimension of intersection of C1 and zero locus of this form is minimal. If C2 is a face, then this is the supporting hyperplane. Otherwise, this is the supporting hyperplane of minimal face containing C2.}
    require Ambient(C1) eq Ambient(C2): "Cones must live in the same lattice";
    k:=known_face_index(C1,C2);
    if not IsZero(k) and has_face_support(C1,k) then
        return face_support(C1,k);
    end if;
    D:=Cone(RGenerators(C1) cat LinearConeGenerators(RGenerators(C2)));
    support:=PointInInterior(Dual(D));
    if not IsZero(k) then 
        set_face_support(C1,k,support);
    end if;
    return support;
end intrinsic;
