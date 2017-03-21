freeze;

/////////////////////////////////////////////////////////////////////////
// fan.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 49685 $
// $Date: 2015-01-14 21:41:53 +1100 (Wed, 14 Jan 2015) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for manipulating fans in toric lattices.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": seq_of_k_subsets, remove_repetitions;
import "../utilities/strings.m": seq_to_string, seq_calc_widths, seq_to_aligned_string;
import "../lattice/lattice.m": lattice_from_cache, lattice_get_Zlattice, lattice_get_Qlattice;
import "../cone/faces.m": number_of_known_faces, get_cone_faces_from_faces, include_cone_in_faces, has_all_faces, has_all_faces_of_codim;
import "../cone/generators.m": cone_has_inequalities;

declare type TorFan;
declare attributes TorFan:
    // Essential attributes:
    lattice,
    cones,                          // The sequence of cones in the fan F.
    cones_all,                      // True iff F knows all its cones.
    // Optional attributes:
    rays,
    virtual_ray_indices,
    has_all_virtual_rays,
    cones_numbers_of_known_faces,   // Number of faces of C which have already
                                    // been checked to lie in F.
    cones_superfaces,               // Seq of seqs of integers refering to
                                    // numbers of superface.
    cone_indices,                   // Seq of seqs of integers refering to ray
                                    // indices.
    cones_maximal,                  // Either seq of integers refering to
                                    // indices of maximal cones, or an integer n
                                    // meaning that the maximal cones are among
                                    // the first n cones.
    cones_intersections,            // Array of pairs of indices \mapsto index
                                    // which tells about intersection of cones.
    cones_propagation_array,        // Array indexed by RngIntElt x RngIntElt
                                    // s.t. (i,j)-th entry is true iff j-th cone
                                    // has been tested for being a subcone of
                                    // the i-th cone.
    cones_propagation_seq,          // Seq of integers s.t. i-th entry is n if
                                    // i-th cone has been tested for being a
                                    // subcone of all the cones of the fan with
                                    // numbers [1..n].
    cones_propagation_int,          // Integer n, where all pairs of cones with
                                    // numbers [1..n] have been tested for being
                                    // a subcone of one another.
    is_complete,                    // Is F a complete fan?
    resolution,                     // A resolution of singularities.
    terminalisation,                // A simplicial terminal refinement of F.
    canonicalisation;               // A simplicial canonical refinement of F.

///////////////////////////////////////////////////////////////////////
// Fan validation
///////////////////////////////////////////////////////////////////////

// Returns true iff the sequence S of cones defines a fan. If true, then the
// intersection table for the cones is returned as the second return value.
// If false, then the first obstruction to defining a fan is returned as the
// second return value.
function does_defines_fan(S)
    intersections:=[[PowerStructure(TorCon)|] : i in [1..#S]];
    known:=S;
    for i in [1..#S] do
        if not IsStrictlyConvex(S[i]) then
            msg:=Sprintf("Cone %o is not strictly convex.",i);
            return false,msg;
        end if;
        for j in [1..i-1] do
            F:=S[i] meet S[j];
            ind:=Index(known, F);
            if  IsZero(ind) then
                Append(~known,F);
            else
                F:=known[ind];
            end if;
            if not IsFace(S[j],F) then
                msg:=Sprintf("Intersection of cones %o and %o is not a face of cone %o.",j,i,j);
                return false,msg;
            end if;
            if not IsFace(S[i],F) then
                msg:=Sprintf("Intersection of cones %o and %o is not a face of cone %o.",j,i,i);
                return false,msg;
            end if;
            intersections[j][i]:=F;
        end for;
    end for;
    return true,intersections;
end function;

///////////////////////////////////////////////////////////////////////
// Setting Cone Data
///////////////////////////////////////////////////////////////////////

// For a fan F, sets the propagation data: j-th cone in F has been tested for
// being a subcone of i-th cone.
procedure set_propagation_data(F,i,j)
    if not assigned F`cones_propagation_array then
        F`cones_propagation_array:=AssociativeArray(
                                        CartesianPower(Integers(),2));
    end if;
    F`cones_propagation_array[<i,j>]:=true;
end procedure;

// For a fan F, sets the superface data: face-th cone knows that sup-th cone in
// F is its superfaces.
procedure set_superface_data(F,sup,face, bool)
    if not assigned F`cones_superfaces then
        F`cones_superfaces:=AssociativeArray(CartesianPower(Integers(),2));
    end if;
    if not IsDefined(F`cones_superfaces, <sup,face>) then
        if sup eq face then
            F`cones_superfaces[<sup,face>]:=true;
        else
            F`cones_superfaces[<sup,face>]:=bool;
        end if;
    end if;
end procedure;

// For a fan F, sets the intersection of i-th and j-th cone in F to be the cone
// number ind
procedure set_intersection_data(F,i,j,ind)
    if not assigned F`cones_intersections then
        F`cones_intersections:=AssociativeArray(PowerSet(Integers()));
    end if;
    if not IsDefined(F`cones_intersections, {i,j}) then
        F`cones_intersections[{i,j}]:=ind;
        set_superface_data(F,i,ind, true);
        set_superface_data(F,j,ind, true);
        set_superface_data(F,ind,j, false);
        set_superface_data(F,ind,i, false);
    end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// getting fan cones
/////////////////////////////////////////////////////////////////////////
// Input:   F -- a fan, C --- a cone
// Output:  varies
/////////////////////////////////////////////////////////////////////////
//
// Functions and procedures for handling cones in the fan.
// Usually check if C is in known to the fan and then act accordingly.
//
/////////////////////////////////////////////////////////////////////////

// true, iff F has its rays defined already
function internal_has_rays(F)
      return assigned F`rays;
end function;

//The list of all cones already known to F.
function known_cones(F)
      if not assigned F`cones then
          F`cones:=[PowerStructure(TorCon)|];
      end if;
      return F`cones;
end function;

// creates or reads the indices of i-th cone of F.
function internal_cone_indices(F,i)
       if not assigned F`cone_indices then
           F`cone_indices:=[PowerSet(Integers())|];
       end if;
       if not IsDefined(F`cone_indices, i) then
            F`cone_indices[i]:={Integers()| Index(Rays(F), ray)
                                 : ray in MinimalRGenerators(known_cones(F)[i])};
       end if;
       return F`cone_indices[i];
end function;

function internal_get_cones_maximal(F)
       if not assigned F`cones_maximal then
            F`cones_maximal:=#known_cones(F);
       end if;
       if Type(F`cones_maximal) eq RngIntElt then
            kcF:=known_cones(F);
            cones_maximal:=[1..F`cones_maximal];
            if internal_has_rays(F) then
                 cones:=[internal_cone_indices(F,i) :  i  in cones_maximal];
                 is_zero_cone_test:=IsEmpty;
            else
                 cones:=kcF[1..F`cones_maximal];
                 is_zero_cone_test:=IsZero;
            end if;
            for i in [1..#cones] do
                 cone:=cones[i];
                 if is_zero_cone_test(cone) then
                     Exclude(~cones_maximal, i);
                     for j in [1..#kcF] do
                         set_propagation_data(F,i,j);
                         set_propagation_data(F,j,i);
                         set_intersection_data(F,i,j,i);
                     end for;
                 else
                     bool:=true;
                     k:=1;
                     while bool and k le #cones_maximal do
                         j:=cones_maximal[k];
                         if i ne j and cone subset cones[j] then
                               Exclude(~cones_maximal, i);
                               include_cone_in_faces(kcF[j],kcF[i]);
                               set_propagation_data(F,i,j);
                               set_intersection_data(F,i,j,i);
                               bool:=false;
                         else
                               k+:=1;
                         end if;
                         set_propagation_data(F,j,i);
                     end while;
                 end if;
            end for;
            F`cones_maximal:=cones_maximal;
       end if;
       return F`cones_maximal;
end function;

forward  put_and_get_index_of_cone_in_fan;
forward  propagate_all_cones;

// Checks if the face data of cones of F is known to F.
// I.e., if C1 is a face of C2 and C2 is in F,
// then C1 becomes a cone in F (unless F already knows about C1).
procedure get_fan_cones_from_cone_faces(F : propagate:=true)
        if not assigned F`cones_numbers_of_known_faces then
             F`cones_numbers_of_known_faces:=[Integers()|];
        end if;
        S:=known_cones(F);
        for i in [1..#S] do
             C:=S[i];
             get_cone_faces_from_faces(C);
             if not IsDefined(F`cones_numbers_of_known_faces, i) then
                   F`cones_numbers_of_known_faces[i]:=0;
             end if;
             for j in [F`cones_numbers_of_known_faces[i]+1..number_of_known_faces(C)] do
                   ind:=put_and_get_index_of_cone_in_fan(F,C`faces_cones[j]
                                              : without_faces:=true, propagate:=propagate);
                   set_intersection_data(F,ind,j,ind);
                   set_propagation_data(F,ind,j);
                   set_propagation_data(F,j,ind);
             end for;
             F`cones_numbers_of_known_faces[i]:= number_of_known_faces(C);
        end for;
end procedure;

// If C is not known to F, adds it to the list of known cones.
// then returns index of C in known cones of F.
// To be used ONLY if C is known to be a cone of F.
function put_and_get_index_of_cone_in_fan(F,C: without_faces:=false , propagate:=true)
      if not without_faces then
          get_fan_cones_from_cone_faces(F);
      end if;
      cones:=known_cones(F);
      ind:=Index(cones,C);
      if not IsZero(ind) then
           return ind;
      end if;
      Append(~F`cones,C);
      if propagate then
         propagate_all_cones(F);
      end if;
      return #F`cones;
end function;

// If C is not known to F, checks if it belongs to F.
// If so, then adds it to the list of known cones.
// Then returns index of C in known cones of F.
// Assumes C and F have the same ambient.
function check_and_get_index_of_cone_in_fan(F,C)
      get_fan_cones_from_cone_faces(F);
      cones:=known_cones(F);
      ind:=Index(cones,C);
      if not IsZero(ind) then
           return ind;
      end if;
      if F`cones_all then
           return 0;
      end if;
      if IsZero(C) then
           return put_and_get_index_of_cone_in_fan(F,C);
      end if;

      gens:=MinimalRGenerators(C);
      rays:=PureRays(F);
      indices:={Index(rays,r): r in gens};
      if 0 in indices then
           return 0;
      end if;
      index:=Index([indices subset cone_ind : cone_ind in ConeIndices(F)],true);
      if IsZero(index) then
           return 0;
      end if;
      cone:=Cone(F,index);
      if IsFace(cone,C) then
           return put_and_get_index_of_cone_in_fan(F,C);
      end if;
      return 0;
end function;

// If C is known to F, then replaces C with the object known to F;
// otherwise leaves C along and adds C to the known cones of F.
// to be used ONLY if C is known to a be a cone of F
procedure get_fan_cone(~C,F)
      ind:=put_and_get_index_of_cone_in_fan(F,C);
      C:=known_cones(F)[ind];
end procedure;

// Returns the intersection of i-th and j-th cone in F.
function get_intersection(F,i,j)
     if not assigned F`cones_intersections or not IsDefined(F`cones_intersections,{i,j}) then
           S:=known_cones(F);
           C1:=S[i];
           C2:=S[j];
           Ci1:=ConeIndices(F,C1);
           Ci2:=ConeIndices(F,C2);
           Ci:=Ci1 meet Ci2;
           if IsEmpty(Ci) then
               C:=ZeroCone(Ambient(F));
           elif Ci eq Ci1 then
               C:=C1;
           elif Ci eq Ci2 then
               C:=C2;
           else
               C:=Cone([Ray(F,i) : i in Ci]);
               C`are_Rgens_minimal:=true;
               if cone_has_inequalities(C1) and cone_has_inequalities(C2) then
                    D:=Dual(C);
                    D`Rgens:=Inequalities(C1) cat Inequalities(C2);
               end if;
           end if;
           ind:=put_and_get_index_of_cone_in_fan(F,C);
           set_intersection_data(F,i,j,ind);
           F`cone_indices[ind]:=Ci;
     end if;
     return known_cones(F)[F`cones_intersections[{i,j}]];
end function;

///////////////////////////////////////////////////////////////////////
//              propagating data to cones
///////////////////////////////////////////////////////////////////////

// check if i-th cone is a subset of j-th cone.
// If it is, then include i-th cone in faces of j-th cone.
procedure propagate_cone_to_cone(F,i,j)
  if i ne j and not assigned F`cones_propagation_array or not IsDefined(F`cones_propagation_array, <i,j>)
                                      or not F`cones_propagation_array[<i,j>] then
   if not (assigned F`cones_maximal and Type(F`cones_maximal) eq SeqEnum and i in F`cones_maximal) then
     cones:=known_cones(F);
     if internal_has_rays(F) then
         Ci:=internal_cone_indices(F,i);
         Cj:=internal_cone_indices(F,j);
     else
         Ci:=cones[i];
         Cj:=cones[j];
     end if;
     if Ci subset Cj then
           include_cone_in_faces(cones[j],cones[i]);
           set_propagation_data(F,i,j);
           set_intersection_data(F,i,j,i);
     end if;
   end if;
   set_propagation_data(F,j,i);
  end if;
end procedure;

// check if i-th cone is a subset of some other cone of F.
// If it is, then include i-th cone in faces of that other cone.
procedure propagate_cone(F,i)
        if not assigned F`cones_propagation_seq then
             F`cones_propagation_seq:=[Integers()|];
        end if;
        if not IsDefined(F`cones_propagation_seq,i) then
             F`cones_propagation_seq[i]:=0;
        end if;
        n:=#known_cones(F);
        for j in Exclude([F`cones_propagation_seq[i]+1..n],i) do
            propagate_cone_to_cone(F,i,j);
        end for;
        F`cones_propagation_seq[i]:=n;
end procedure;

// check if some cone of F is a subset of some other cone of F.
// If it is, then include that cone in faces of that other cone.
procedure propagate_all_cones(F)
    get_fan_cones_from_cone_faces(F : propagate:=false);
    if not assigned F`cones_propagation_int then
             F`cones_propagation_int:=0;
    end if;
    n:=#known_cones(F);
    for i in [F`cones_propagation_int+1..n] do
            propagate_cone(F,i);
    end for;
    F`cones_propagation_int:=n;
end procedure;

///////////////////////////////////////////////////////////////////////
//              Printing
///////////////////////////////////////////////////////////////////////

intrinsic PrintNamed(F::TorFan,level::MonStgElt,name::MonStgElt)
{}
    // First we collect together the strings we'll need
    prefix:="    ";
    if level eq "Maximal" then
        desc:="";
        if IsComplete(F) then
            desc:="Complete ";
        end if;
        if IsNonsingular(F) then
            if #desc eq 0 then
                desc:="Nonsingular ";
            else
                desc cat:= "nonsingular ";
            end if;
        else
            if IsQFactorial(F) then
                if IsIsolated(F) then
                    desc cat:= "Q-factorial isolated ";
                else
                    desc cat:= "Q-factorial ";
                end if;
            end if;
            if IsTerminal(F) then
                if #desc eq 0 then
                    desc:="Terminal ";
                else
                    desc cat:= "terminal ";
                end if;
            elif IsCanonical(F) then
                if #desc eq 0 then
                    desc:="Canonical ";
                else
                    desc cat:= "canonical ";
                end if;
            end if;
            if IsGorenstein(F) then
                desc cat:= "Gorenstein ";
            end if;
        end if;
        if #desc eq 0 then
            desc:="Fan";
        else
            desc cat:= "fan";
        end if;
        ambient:=Sprintf("in %o ", Ambient(F));
    else
        desc:="Fan";
        ambient:="";
    end if;
    gens:="";
    if assigned F`rays then
        num:=#F`rays;
        if num eq #VirtualRayIndices(F) then
            gens:="supported at 0";
        end if;
        if num ne 0 then
            if #gens gt 0 then
                gens cat:= " ";
            end if;
            if num eq 1 then
                gens cat:= "with one ray";
            else
                gens cat:= Sprintf("with %o rays",num);
            end if;
            if level ne "Minimal" and num ne 0 and
               (level eq "Maximal" or num le 10) then
                rays:=[Eltseq(ray) : ray in Rays(F)];
                widths:=seq_calc_widths(rays);
                gens cat:= Sprintf(":\n%o%o", prefix,
                            seq_to_aligned_string(rays, widths,
                            "(", ",", prefix));
                if assigned F`virtual_ray_indices and
                    #F`virtual_ray_indices ne 0 then
                    num:=#F`virtual_ray_indices;
                    if num eq 1 then
                        gens cat:= Sprintf("\nwhere ray %o is virtual",
                                                      F`virtual_ray_indices[1]);
                    else
                        gens cat:= "\nwhere rays " cat seq_to_string(F`virtual_ray_indices[1..num - 1],"",",");
                        if num gt 2 then
                            gens cat:=",";
                        end if;
                        gens cat:= " and " cat IntegerToString(F`virtual_ray_indices[num]) cat " are virtual";
                    end if;
                    newline:=false;
                else
                    newline:=true;
                end if;
                printedrays:=true;
            else
                printedrays:=false;
            end if;
            if level ne "Minimal" then
                CI:=ConeIndices(F);
                num:=#CI;
                if num gt 0 then
                    if printedrays then
                        if newline then
                            gens cat:="\n";
                        else
                            gens cat:=", ";
                        end if;
                        if num eq 1 then
                            gens cat:= "and one cone";
                        else
                            gens cat:= Sprintf("and %o cones",num);
                        end if;
                        if level eq "Maximal" or num le 10 then
                            gens cat:= " with indices:\n";
                            for i in [1..num] do
                                gens cat:= prefix cat
                                            seq_to_string(CI[i],"[",",");
                                if i ne num then
                                    gens cat:= ",\n";
                                end if;
                            end for;
                        end if;
                    else
                        if num eq 1 then
                            gens cat:= " and one cone";
                        else
                            gens cat:= Sprintf(" and %o cones",num);
                        end if;
                    end if;
                end if;
            end if;
        end if;
    elif assigned F`cones then
        cones:=Cones(F);
        num:=#cones;
        if num eq 0 then
            gens:="supported at 0";
        else
            if num eq 1 then
                if level ne "Minimal" then
                    gens:=Sprintf("generated by a %o",cones[1]);
                else
                    gens:="generated by one cone";
                end if;
            else
                gens:=Sprintf("generated by %o cones",num);
                if level ne "Minimal" and num ne 0 and
                   (level eq "Maximal" or num le 10) then
                    gens cat:= ":\n";
                    for i in [1..#cones] do
                        gens cat:= Sprintf(" %o) %o",i,cones[i]);
                        if i ne #cones then
                            gens cat:= "\n";
                        end if;
                    end for;
                end if;
            end if;
        end if;
    end if;
    // Now output the data to screen
    if name eq "$" then
        printf "%o %o%o",desc,ambient,gens;
    else
        printf "%o %o %o%o",desc,name,ambient,gens;
    end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//             Verification of input data for fans
///////////////////////////////////////////////////////////////////////

intrinsic DoesDefineFan( S::[TorCon] : verbose:=false )
    -> BoolElt,SeqEnum[SeqEnum[TorCon]]
{True iff the sequence of cones S defines a fan. If true, then the intersection table for the cones is also given. If the optional parameter 'verbose' (default: false) is set to true then the first obstruction to defining a fan will be printed.}
    require not IsNull(S): "Illegal null sequence.";
    require Type(verbose) cmpeq BoolElt:
        "The parameter 'verbose' must be a boolean.";
    bool,data:=does_defines_fan(S);
    if bool then
        return true,data;
    else
        if verbose then
            printf "%o\n",data;
        end if;
        return false,_;
    end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//             Creating and checking virtual rays
///////////////////////////////////////////////////////////////////////

intrinsic CreateVirtualRays(S::[TorLatElt]) -> SeqEnum[TorLatElt]
{Given a sequence S of rays of a fan, computes the remaining virtual rays which form a basis of the lattice complementary to the linear span of S. Virtual rays are useful, for example, when calculating the coordinate ring of the toric variety associated to the fan when the variety is a product of a torus and a smaller toric variety.}
    require not IsNull(S): "Illegal null sequence.";
    SS:=LinearSpanGenerators(S);
    L, phi:=Quotient(SS);
    return Basis(L)@@phi;
end intrinsic;

intrinsic VirtualRayIndices(F::TorFan) -> SeqEnum[RngIntElt]
{The indices of virtual rays of the fan F calculated so far}
      if assigned F`virtual_ray_indices then
           return F`virtual_ray_indices;
      end if;
      return [Integers()|];
end intrinsic;

intrinsic PureRayIndices(F::TorFan) -> SeqEnum[RngIntElt]
{The indices of pure rays among all known rays of the fan F}
      if assigned F`virtual_ray_indices then
           return [Integers()|i : i in [1..#Rays(F)]|  not i in F`virtual_ray_indices];
      end if;
      return [Integers()|1..#Rays(F)];
end intrinsic;

intrinsic VirtualRays(F::TorFan) -> SeqEnum[TorLatElt]
{All the virtual rays of the fan F}
      if not F`has_all_virtual_rays then
          R:=CreateVirtualRays(Rays(F));
          if not assigned F`virtual_ray_indices then
              F`virtual_ray_indices:=[Integers()|];
          end if;
          F`virtual_ray_indices cat:=[Integers()| n+1..n+#R] where n is #Rays(F);
          F`rays cat:=R;
          F`has_all_virtual_rays:=true;
      end if;
      return [Ambient(F)| F`rays[i] :  i in VirtualRayIndices(F)];
end intrinsic;

///////////////////////////////////////////////////////////////////////
//             Creation
///////////////////////////////////////////////////////////////////////

//
// in Dim =2 from given rays construct all the sensible cones (as indices with respect to ray)
// to make a 2-dimensional fan from the given rays.
// assumes rays are primitive and have no redundancy (in particular, there is no zero).
// second returned argument says how to reorder, to get the rays ordered in nice way.
/*
//cases:
//NOT FINISHED!!!


//3) Contained in a halfspace and spanning the halfplane
//4) spanning a stricly convex cone
//5) spanning whole plane


function internal_get_cones_for_two_dimensional_fan(rays)
     // Case 1): there is only only one ray:
     if #rays eq 1 then
         return [{1}], [1];
     end if;
     // Case 2) there are two oposite rays:
     if #rays eq 2 and rays[1] eq -rays[2] then
         return [{1},{2}], [1,2];
     end if;

     L:=Universe(rays);
     C:=Cone(rays);
     ineqs:=MinimalInequalities(C);
     // Case 3) Rays span a halfspace:
     if #ineqs eq 1 then




     P:=PointInInterior(Dual(C));

     b:=L.1;
     QtimesZ:=CartesianProduct(Rationals(),Integers());
     positives:=[QtimesZ|<r[1]/r[2],i > : i in [1..#rays] | r[1] gt 0 where r is Eltseq(rays[i]) ];
     negatives:=[QtimesZ|<r[1]/r[2],i > : i in [1..#rays] | r[1] lt 0 where r is Eltseq(rays[i]) ];
     ray0_plus1:=Index(rays, b);
     ray0_minus1:=Index(rays, -b);
     new_order:=




end function;
*/

// Makes a fan out of given cones.
// It is assumed that the cones really define a fan and there is at least one
// cone (so that the lattice might be read from this cone).
// If max_cones is true, then it does not check, if there is any redundancy
// among the cones (i.e. one of the cones is a face of another).
// If extra_cones are given, they will be included at the end of the list of
// cones (with redundancy check).
// If intersection_data is included (seq of seq of cones, might have holes),
// then these cones will be included as well; these cones are assumed to be
// intersections of i-th and j-th cones in cones.
// This function does not propagate cones.
function construct_fan_from_cones(cones :
    max_cones:=false, extra_cones:=[], intersection_data:=[])
    F:=New(TorFan);
    F`lattice:=Ambient(Representative(cones));
    F`cones_all:=false;
    if max_cones then
        F`cones:=cones;
        F`cones_maximal:=[1..#cones];
    else
        i:=1;
        F`cones:=cones;
        remove_repetitions(~F`cones);
        F`cones_maximal:=#F`cones;
    end if;
    for C in extra_cones do
        ind:= put_and_get_index_of_cone_in_fan(F,C: propagate:=false);
    end for;
    for i in [1..#intersection_data] do
        if IsDefined(intersection_data,i) then
            for j in [1..#intersection_data[i]] do
                if IsDefined(intersection_data[i], j) then
                    ind:=put_and_get_index_of_cone_in_fan(F,
                                     intersection_data[i][j] : propagate:=true);
                    set_intersection_data(F,i,j,ind);
                end if;
            end for;
        end if;
    end for;
    F`has_all_virtual_rays:=false;
    return F;
end function;

// Makes a fan out of given rays and cones.
// See above for assumptions on cones, max_cones, extra_cones,intersection_data.
// It is assumed, there is no repetition among rays.
// If min_rays are set to true, it is assumed, there are no virtual rays, nor
// there are rays, which are not MinRgens of either of the cones.
// Returns true followed by the fan on success, false followed by an error
// message otherwise.
function construct_fan_from_rays(rays,cones:
    max_cones:=false, min_rays:=false, extra_cones:=[], intersection_data:=[])
    F:=construct_fan_from_cones(cones : max_cones:=max_cones,
                intersection_data:=intersection_data, extra_cones:=extra_cones);
    F`rays:=rays;
    if min_rays then
       F`virtual_ray_indices:=[Integers()|];
    else
       rays2:=&cat[MinimalRGenerators(cone) : cone in Cones(F)];
       F`virtual_ray_indices:=[Integers()| i : i in [1..#rays] | not rays[i] in rays2];
       if not IsEmpty(F`virtual_ray_indices) then
             rays_not_in_cones:=[rays[i] : i in F`virtual_ray_indices];
             S:=LinearSpanGenerators(rays2) cat rays_not_in_cones;
             g:=Index(S);
             if not g eq 1 or Rank(Matrix(S)) lt #S then
                 return false,"The virtual rays cannot be extended to a basis of lattice complementary to linear span of the fan. Try removing from rays the unnecessary vectors or construct Cones first and then fan - virtual rays will be ignored.";
             end if;
             F`has_all_virtual_rays:=#S eq Dimension(Ambient(F));
       end if;
    end if;
    propagate_all_cones(F);
    return true,F;
end function;

intrinsic Fan(R::[SeqEnum[RngIntElt]], S::[SeqEnum[RngIntElt]] :
    define_fan:=false, min_rays:=false, max_cones:=false, is_complete:=false)
    -> TorFan
{}
    require #R ne 0: "Argument 1 cannot be an empty sequence.";
    dim:=#Representative(R);
    require &and[#r eq dim : r in R]:
        "Argument 1 must consist of sequences of the same length.";
    require Type(define_fan) eq BoolElt:
        "The parameter 'define_fan' must be a boolean.";
    require Type(min_rays) eq BoolElt:
        "The parameter 'min_rays' must be a boolean.";
    require Type(max_cones) eq BoolElt:
        "The parameter 'max_cones' must be a boolean.";
    require Type(is_complete) eq BoolElt:
        "The parameter 'is_complete' must be a boolean.";
    L:=lattice_from_cache(dim);
    return Fan([L | v : v in R], S : max_cones:=max_cones, min_rays:=min_rays,
                              define_fan:=define_fan, is_complete:=is_complete);
end intrinsic;

intrinsic Fan(R::[TorLatElt], S::[SeqEnum[RngIntElt]] :
    define_fan:=false, min_rays:=false, max_cones:=false, is_complete:=false)
    -> TorFan
{The fan with rays generated by the toric lattice points in R and cone indices specified by S. If optional parameter 'define_fan' (default: false) is set to true then the verification that the data defines a fan is skipped. If optional parameter 'min_rays' (default: false) is set to true then it is assumed that there are no virtual rays. If the optional parameter 'max_cones' (default: false) is set to true then it is assumed that the cones are maximal. If the optional parameter 'is_complete' (default: false) is set to true then it is assumed that the fan is complete.}
    require not IsNull(R): "Illegal null sequence.";
    require Type(define_fan) eq BoolElt:
        "The parameter 'define_fan' must be a boolean.";
    require Type(min_rays) eq BoolElt:
        "The parameter 'min_rays' must be a boolean.";
    require Type(max_cones) eq BoolElt:
        "The parameter 'max_cones' must be a boolean.";
    require Type(is_complete) eq BoolElt:
        "The parameter 'is_complete' must be a boolean.";
    require #S ge 1:
        "Argument 2 must be non empty, i.e. fan must have at least one cone.";
    require Max(&cat S) le #R and Min(&cat S) ge 1:
        Sprintf("Argument 2 must be in the range 1..%o.",#R);
    RR:=[PrimitiveLatticeVector(ray) : ray in R];
    remove_repetitions(~RR);
    require #RR eq #R: "There are repetitions in the given sequence of rays.";
    cones:=Cones(RR,S);
    if not define_fan then
       bool,intersection_data:=does_defines_fan(cones);
       require bool: Sprintf("The input data does not define a fan: %o",
                                                             intersection_data);
    else
       intersection_data:=[];
    end if;
    bool,F:=construct_fan_from_rays(RR,cones : max_cones:=max_cones,
                      min_rays:=min_rays, intersection_data:=intersection_data);
    require bool: F;
    if is_complete then
        F`is_complete:=true;
    end if;
    return F;
end intrinsic;

intrinsic Fan(S::[TorCon]: define_fan:=false, max_cones:=false,
    is_complete:=false) -> TorFan
{The fan generated by the sequence of cones S. If the optional parameter 'define_fan' (default: false) is set to true then the verification that the data defines a fan is skipped. If the optional parameter 'max_cones' (default: false) is set to true then it is assumed that the cones are maximal. If the optional parameter 'is_complete' (default: false) is set to true then it is assumed that the fan is complete.}
    require not IsEmpty(S): "The fan must be defined by at least one cone.";
    require Type(define_fan) eq BoolElt:
        "The parameter 'define_fan' must be a boolean.";
    require Type(is_complete) eq BoolElt:
        "The parameter 'is_complete' must be a boolean.";
    if not define_fan then
        bool,intersection_data:=does_defines_fan(S);
        require bool: Sprintf("The input data does not define a fan: %o",
                                                             intersection_data);
    else
        intersection_data:=[];
    end if;
    F:=construct_fan_from_cones(S: max_cones:=max_cones,
                                   intersection_data:=intersection_data);
    propagate_all_cones(F);
    if is_complete then
        F`is_complete;
    end if;
    return F;
end intrinsic;

intrinsic Fan(C::TorCon) -> TorFan
{The fan consisting of a single cone C}
    require IsStrictlyConvex(C): "The cone must be strictly convex.";
    if IsZero(C) then
        max_cone:=false;
    else
        max_cone:=true;
    end if;
    F:=construct_fan_from_cones([C]: max_cones:=max_cone);
    F`is_complete:=false;
    return F;
end intrinsic;

intrinsic FanWithWeights( W::SeqEnum[SeqEnum[RngIntElt]] : ample:=false,
    define_fan:=false ) -> TorFan
{The fan generated by the weights W. The optional parameter 'ample' can be used to specify the ample divisor to use. If the optional parameter 'define_fan' (default: false) is set to true then the verification that the weights define a fan is skipped.}
    // Sanity check
    require #W ne 0 and #W[1] ne 0:
        "The fan must be defined by at least one weight.";
    n:=#W[1];
    require &and[#wt eq n : wt in W]:
        "The weights must all be of the same length.";
    require Type(define_fan) eq BoolElt:
        "The parameter 'define_fan' must be a boolean.";
    if not ample cmpeq false then
        require Type(ample) eq SeqEnum and #ample eq #W:
            Sprintf("The parameter 'ample' must be a sequence of integers of length %o.",#W);
        bool,ample:=CanChangeUniverse(ample,Integers());
        require bool: "The parameter 'ample' must be a sequence of integers.";
    end if;
    // Create the weight matrix
    wts:=Matrix(Integers(),W);
    // Generate the sequence of toric divisors
    divisors:=RowSequence(Transpose(wts));
    D:=lattice_from_cache(#W);
    ChangeUniverse(~divisors,D);
    // If no ample divisor is given, use -K as our ample divisor
    if ample cmpeq false then
        ample:=&+divisors;
    else
        ample:=D ! ample;
    end if;
    // Calculate the rays
    rays:=RowSequence(Transpose(KernelMatrix(Transpose(wts))));
    require #rays ne 0: "The weights have empty kernel.";
    // Calculate the maximal cone indices; see:
    //    Coates-Iritani-Jiang, http://arxiv.org/pdf/1410.0024v2.pdf
    //    Notation 4.1 and Definition 4.2
    max_cone_idxs:=[PowerSet(Integers())|];
    // We need to special-case the empty anti-cone, because our convention is
    // that this has empty interior
    if IsZero(ample) then
        Append(~max_cone_idxs,{1..#rays});
    end if;
    // Now build the rest of the maximal cones
    for num_rays in [#rays-1..0 by -1] do
        possible_max_cone_idxs:=[sigma : sigma in Subsets({1..#rays},num_rays)|
                              not &or[sigma subset max : max in max_cone_idxs]];
        max_cone_idxs cat:= [sigma : sigma in possible_max_cone_idxs |
		                      IsInInterior(ample,Cone([D | divisors[k] :
                              k in [1..#rays] | not k in sigma]))];
    end for;
    // Create the cones
    L:=lattice_from_cache(#rays[1]);
    ChangeUniverse(~rays,L);
    cones:=[Cone([L | PrimitiveLatticeVector(rays[i]) : i in I]) :
                                                            I in max_cone_idxs];
    // Does this define a fan?
    if not define_fan then
        require DoesDefineFan(cones): "The weights do not define a fan.";
    end if;
    // Calculate the fan
    F:=Fan(cones : max_cones:=true, define_fan:=define_fan);
    return F;
end intrinsic;

intrinsic ZeroFan(n::RngIntElt) -> TorFan
{The fan in a toric lattice of dimension n supported at 0}
    require n ge 0: "Dimension must be non-negative.";
    return ZeroFan(lattice_from_cache(n));
end intrinsic;

intrinsic ZeroFan(L::TorLat) -> TorFan
{The fan in the toric lattice L supported at 0}
    if not assigned L`zero_fan then
        F:=construct_fan_from_cones([ZeroCone(L)]);
        F`cones_all:=true;
        F`rays:=Basis(L);
        F`cone_indices:=[PowerSet(Integers())|];
        F`virtual_ray_indices:=[Integers()|1..Dimension(L) ];
        L`zero_fan:=F;
        F`has_all_virtual_rays:=true;
        F`is_complete:=Dimension(L) eq 0;
    end if;
    return L`zero_fan;
end intrinsic;

intrinsic FanOfAffineSpace(d::RngIntElt) -> TorFan
{The fan of affine space of dimension d}
    require d ge 1: "Dimension must be strictly positive.";
    L:=lattice_from_cache(d);
    C:=PositiveQuadrant(L);
    bool,F:=construct_fan_from_rays(MinimalRGenerators(C),[C] : max_cones:=true,
                                                                min_rays:=true);
    require bool: F;
    F`is_complete:=false;
    return F;
end intrinsic;

intrinsic FanOfWPS(n::RngIntElt) -> TorFan
{The fan of n-dimensional projective space}
    require n gt 0: "Dimension must be a positive integer.";
    return FanOfWPS([Integers() | 1 : i in [1..n + 1]]);
end intrinsic;

intrinsic FanOfWPS(W::[RngIntElt]) -> TorFan
{The fan of weighted projective space with weights W}
    dim:=#W-1;
    require dim ge 1: "Number of weights must be at least 2.";
    require &and[w ge 0 : w in W]: "Weights must be non-negative.";
    weight_lattice:=lattice_from_cache(#W);
    basis:=Basis(weight_lattice);
    weights_in_lattice:=weight_lattice!W;
    fan_lattice, quotient_map:=Quotient(weights_in_lattice);
    rays:=[PrimitiveLatticeVector(ray): ray in Image(quotient_map,basis)];
    if 0 in W then
        zeros:=[Integers() | i: i in [1..#W] | W[i] eq 0];
        rest:=[Integers() | i : i in  [1..#W] | not i in  zeros];
        indices:=[PowerSequence(Integers()) |
                             i cat zeros: i in  seq_of_k_subsets(rest,#rest-1)];
    else
        indices:= seq_of_k_subsets([1..#W],#W-1);
    end if;
    F:=Fan(rays, indices : define_fan:=true, is_complete:=true);
    return F;
end intrinsic;

intrinsic FanOfFakeProjectiveSpace(W::[RngIntElt], Q::[SeqEnum[FldRatElt]])
    -> TorFan
{The fan of fake weighted projective space (i.e the quotient of weighted projective space with weights W by a finite group action with weights Q)}
    qq:={#q : q in Q};
    require #qq eq 1 and #W eq Representative(qq):
        "Weights must have the same length.";
    F:=FanOfWPS(W);
    L:=Ambient(F);
    L, phi:=AddVectorToLattice([L |&+[q[i]*Rays(F)[i]
              : i in [1..#q]] : q in Q]);
    F:=Image(phi,F);
    return F;
end intrinsic;

intrinsic Fan(F1::TorFan, F2::TorFan)
    -> TorFan, Map[TorLat,TorLat], Map[TorLat,TorLat],
               Map[TorLat,TorLat], Map[TorLat,TorLat]
{The product of fans F1 and F2, together with the following lattice maps: the embedding of the ambient lattice of F1, the embedding of the ambient lattice of F2, the projection onto the ambient lattice of F1, and the projection onto the ambient lattice of F2.}
        F,embs,projs:=Fan([F1,F2]);
        return F, embs[1],embs[2],projs[1],projs[2];
end intrinsic;

intrinsic Fan(S::[TorFan])
    -> TorFan, SeqEnum[Map[TorLat,TorLat]], SeqEnum[Map[TorLat,TorLat]]
{The product of the fans in S, together with the following sequences of lattice maps: the embeddings of ambient lattices of the fans in S, and the projections onto the ambient lattices of the fans in S.}
    require not IsEmpty(S): "The product cannot be empty.";
    s:=#S;
    ZZ,embs,projs:=DirectSum([PowerStructure(TorLat)|Ambient(F) : F in S]);
    rays:=&cat[PowerSequence(ZZ)|embs[i](Rays(S[i])) :  i in [1..s]];
    ray_number:=Zero(Integers());
    if s eq 1 then
        F:=S[1];
    elif IsEmpty(rays) then
        F:=ZeroFan(ZZ);
    elif s ge 2 then
        product_cones := ConeIndices(S[1]);
        virt_ray_inds:=VirtualRayIndices(S[1]);
        for i in [2..s] do
            ray_number+:=#Rays(S[i-1]);
            cones:=[{Integers()| ray_number + j  :  j in C} : C in ConeIndices(S[i])];
            virt_ray_inds cat:=[Integers()| ray_number + j  :  j in VirtualRayIndices(S[i])];
            product_cones:=[cone1 join cone2 : cone1 in product_cones, cone2 in cones];
        end for;
        product_cones_tmp := [ Setseq(cone) : cone in product_cones ];
        F:=Fan(rays, product_cones_tmp: define_fan:=true, max_cones:=true, min_rays:=true);
        F`virtual_ray_indices:=virt_ray_inds;
    end if;
    return F, embs,projs;
end intrinsic;

intrinsic '*'(F1::TorFan, F2::TorFan) -> TorFan
{The product of the fans F1 and F2}
        F:=Fan(F1,F2);
        return F;
end intrinsic;

intrinsic '^'(F::TorFan, n::RngIntElt) -> TorFan
{The product of n copies of the fan F}
        return Fan([F: i in [1..n]]);
end intrinsic;

intrinsic Blowup(F::TorFan, R::TorLatElt) -> TorFan
{The fan given by subdividing the fan F at the ray R (represented by a toric lattice point)}
    require Parent(R) eq Ambient(F):
        "The ray must lie in the same ambient toric lattice as the fan.";
    if not IsInSupport(R,F) or IsZero(R) then
        return F;
    end if;
    R:=PrimitiveLatticeVector(R);
    ind:=Index(Rays(F),R);
    cones:=Cones(F);
    if ind eq 0 then
        rays:=Append(Rays(F),R);
    else
        cones_that_matter:=[cones[i] : i in [1..#cones] | ind in cone_inds[i]]
                                              where cone_inds is ConeIndices(F);
        if &and[IsSimplicial(c) : c in cones_that_matter] then
            return F;
        end if;
        rays:=Rays(F);
    end if;
    new_cones:=[PowerStructure(TorCon)|];
    extra_cones:=[PowerStructure(TorCon)|];
    for cone in cones do
        if R in cone then
            facets:=[facet : facet in Facets(cone) | not R in facet];
            new_cones cat:=[Cone(Append(RGenerators(facet),R)):facet in facets];
            extra_cones cat:=facets;
        else
            Append(~new_cones, cone);
        end if;
    end for;
    bool,F:=construct_fan_from_rays(rays,new_cones : max_cones:=true,
                                                     extra_cones:=extra_cones);
    require bool: F;
    return F;
end intrinsic;

intrinsic NormalFan(F::TorFan, C::TorCon) -> TorFan, Map[TorLat,TorLat]
{The normal fan of the fan F in the quotient lattice, and the corresponding quotient map (does not check that the cone C is a face in F)}
     if IsZero(C) then
        return F, IdentityMap(Ambient(F));
     end if;
     ind:= check_and_get_index_of_cone_in_fan(F,C);
     require not IsZero(ind):
        "Then cone (argument 2) must be a member of the fan (argument 1).";
     L,phi:=Quotient(C);
     new_cones:=[Image(phi,CC): CC in Cones(F)| C subset CC];
     rgens_of_cones:=&cat[MinimalRGenerators(CC) : CC in new_cones];
     new_rays:=[L|r:   i in [1..#S]  | not IsZero(r) and
                         (i in VirtualRayIndices(F) or r in rgens_of_cones)
                          where r is PrimitiveLatticeVector(S[i])]
                          where S is Image(phi,Rays(F));
     remove_repetitions(~new_rays);
     bool,new_fan:=construct_fan_from_rays(new_rays,new_cones: max_cones:=true);
     require bool: new_fan;
     return new_fan, phi;
end intrinsic;

intrinsic Skeleton(F::TorFan, n::RngIntElt) -> TorFan
{The fan generated by the cones of dimension at most n in the fan F}
     requirerange n,1,Dimension(Ambient(F));
     if #Cones(F) eq 0 then
          return F;
     end if;
     cones:=Cones(F,n) cat [C : C in Cones(F) | Dimension(C) lt n];
     bool,skeleton:=construct_fan_from_rays(Rays(F),cones);
     require bool: skeleton;
     return skeleton;
end intrinsic;

intrinsic OneSkeleton(F::TorFan) -> TorFan
{The fan generated by the rays of the fan F}
        return Skeleton(F,1);
end intrinsic;

///////////////////////////////////////////////////////////////////////
//             Recover attributes
///////////////////////////////////////////////////////////////////////

intrinsic Cones(F::TorFan) -> SeqEnum[TorCon]
{The cones generating the fan F}
        cones_max:=internal_get_cones_maximal(F);
        cones:=known_cones(F);
        return [PowerStructure(TorCon)| cones[i]: i in cones_max];
end intrinsic;

intrinsic Cone(F::TorFan, i::RngIntElt) -> SeqEnum[TorCon]
{The i-th cone generating the fan F}
        max_cones:=internal_get_cones_maximal(F);
        requirerange i,1,#max_cones;
        j:=max_cones[i];
        return known_cones(F)[j];
end intrinsic;

intrinsic Cone(F::TorFan, S::[RngIntElt]: in_fan:=true, extend:=false)
    -> TorCon
{The cone C spanned by those rays in the fan F whose indices appear in S. By default C must be a cone in F. If the optional parameter 'extend' is set to true (default: false), then the smallest cone in F containing C will be found (if such a cone exists). If the parameter 'in_fan' is set to false (default: true) then the cone is created even if it failed previous tests.}
        rays:=Rays(F);
        SS:=Seqset(S);
        require not in_fan or SS subset Seqset(PureRayIndices(F)):
            "Argument 2 must be a subset of PureRayIndices of Argument 1.";
        require in_fan or SS subset [1..#rays]:
            Sprintf("Argument 2 must be a subset of 1..%o.",#rays);
        indices:=[PowerSet(Integers())|internal_cone_indices(F,i) :  i in [1..#known_cones(F)]];
        i:=Index(indices, SS);
        if IsZero(i) then
            C:=Cone(rays[Sort(Setseq(SS))]);
            i:=check_and_get_index_of_cone_in_fan(F,C);
        end if;
        if not IsZero(i) then
            return known_cones(F)[i];
        end if;
        if not extend and not in_fan then
            return C;
        end if;
        require extend: "Argument 2 does not define a cone in the fan.";
        // THINK: Can we do better here??
        faces:=&cat[Cones(F,i) : i in [Dimension(Ambient(F))..Dimension(C)+1 by -1]];
        candidates:=[f : f in faces | C subset f];
        dims:=[Dimension(f) : f in candidates];
        mindim:=Minimum(dims);
        i:=Index(dims, mindim);
        if not IsZero(i) then
            return candidates[Index(dims, mindim)];
        end if;
        if not in_fan then
            return C;
        end if;
        require false: "Argument 2 is not a subset of any cone in the fan.";
end intrinsic;

intrinsic Rays(F::TorFan) -> SeqEnum[TorLatElt]
{The rays of the fan F}
       if not assigned F`rays then
           rays:=[Ambient(F)|];
           cones:=Cones(F);
           for cone in cones do
                for ray in MinimalRGenerators(cone) do
                        Include(~rays, ray);
                end for;
           end for;
           rays:=Sort(rays);
           F`rays:=rays;
       end if;
       return F`rays;
end intrinsic;

intrinsic Ray(F::TorFan,i::RngIntElt) -> TorLatElt
{The i-th ray of the fan F}
    rays:=Rays(F);
    requirerange i,1,#rays;
    return rays[i];
end intrinsic;

intrinsic PureRays(F::TorFan) -> SeqEnum[TorLatElt]
{The pure rays of F (i.e. those that are not virtual - a vector is pure iff it is a minimal R-generator of one of the cones in F)}
       return Rays(F)[ PureRayIndices(F)];
end intrinsic;

intrinsic AllRays(F::TorFan) -> SeqEnum[TorLatElt]
{The rays of the fan F. This will include all virtual rays.}
       _:=VirtualRays(F);
       return Rays(F);
end intrinsic;

intrinsic ConeIndices(F::TorFan,C::TorCon) -> SeqEnum
{The sequence S of integers such that the cone C is generated by rays with indexes S[i]. C must be a member of the fan F.}
       require Ambient(F) eq Ambient(C): "Arguments have different ambients.";
       ind:=check_and_get_index_of_cone_in_fan(F,C);
       require not IsZero(ind): "Argument 2 is not contained in the fan.";
       return internal_cone_indices(F,ind);
end intrinsic;

intrinsic ConeIndices(F::TorFan : rays:=false) -> SeqEnum[SetEnum[RngIntElt]]
{The sequence S of sets of integers such that the i-th cone of the fan F is generated by the rays with indices S[i]. If the optional parameter 'rays' is given then the indices are relative to this sequence.}
   if rays cmpeq false then
      return [internal_cone_indices(F,i): i in internal_get_cones_maximal(F)];
   end if;
   require ExtendedCategory(rays) eq SeqEnum[TorLatElt] and
        Universe(rays) cmpeq Ambient(F):
        "The optional parameter rays must be a sequence of lattice elements in the ambient of fan.";
   indices:=[Integers()|Index(rays, ray) : ray in Rays(F)];
   require not 0 in indices: "The sequence rays must contain Rays(F).";
   return [PowerSet(Integers())|{Integers()|indices[i]: i in cone}: cone in ConeIndices(F)];
end intrinsic;

intrinsic Ambient(F::TorFan) -> TorLat
{The toric lattice containing the cones of the fan F}
        return F`lattice;
end intrinsic;

intrinsic Face(F::TorFan,C::TorCon) -> TorCon
{The smallest cone containing the cone C in the fan F. If no such cone exists in F then an error is produced.}
         cones:=Cones(F);
	 i:=Index([C subset cone : cone in cones], true);
         require i ne 0:
            "Argument 2 is not contained in any of the cones of the fan.";
         cone:=cones[i];
         support:=SupportingHyperplane(cone, C);
         face:=FaceSupportedBy(cone, support);
         propagate_all_cones(F);
         return face;
end intrinsic;

intrinsic MaxCones(F::TorFan) -> SeqEnum[TorCon]
{The cones of maximal dimension in the fan F}
     return [PowerStructure(TorCon)|C : C in Cones(F) | Dimension(C) eq Dimension(Ambient(F))];
end intrinsic;

intrinsic AllCones(F::TorFan) -> SeqEnum[SeqEnum[TorCon]]
{The cones of the fan F}
    if not F`cones_all then
       for C in Cones(F) do
            _:=Facets(C);
            propagate_all_cones(F);
       end for;
       if not &and[has_all_faces(C) : C in Cones(F)] then
            rays:=Rays(F);
            cones:=known_cones(F);
            n_cones:=#cones;
            faces_indices:=[internal_cone_indices(F,k) : k in [1..n_cones]];
            all_faces:=Seqset(faces_indices);
            k:=1;
            repeat
                n :=#all_faces;
                all_faces join:={&meet S : S in Subsets(all_faces,2)};
                k+:=1;
            until n eq #all_faces or k ge Dimension(Ambient(F));
            all_faces:=[Sort(Setseq(i)) : i in all_faces | not i in faces_indices];
            for set in all_faces do
                rgens:=rays[set];
                C:=Cone(rgens);
                C`are_Rgens_minimal:=true;
                Append(~F`cones, C);
                F`cone_indices[#F`cones]:=Seqset(set);
            end for;
            propagate_all_cones(F);
        end if;
        F`cones_all:=true;
    end if;
    return [[C:  C in known| Dimension(C) eq i] : i in [0..Dimension(Ambient(F))]] where known is known_cones(F);
end intrinsic;

intrinsic Cones(F::TorFan, n::RngIntElt) -> SeqEnum[TorCon]
{The n-dimensional cones in the fan F}
  if not F`cones_all then
    max:=Max([Dimension(C) : C in Cones(F)]);
    if n eq 0 then
       return [ZeroCone(Ambient(F))];
    elif n eq 1 then
       if not F`cones_all then
          not_known:=[Cone(Ray(F,r)) : r in PureRayIndices(F)| not r in known]
                     where known is [Representative(ConeIndices(F,C)) : C in known_cones(F) | Dimension(C) eq 1];
          F`cones cat:= not_known;
          propagate_all_cones(F);
       end if;
    elif n eq max-1 then
       for C in Cones(F) do
            _:=Facets(C);
            propagate_all_cones(F);
       end for;
    elif n lt max then
       //THINK: Might be worth improving if it turns out it is long.
       _:= AllCones(F);
    end if;
  end if;
  return [PowerStructure(TorCon)|C : C in known_cones(F) | Dimension(C) eq n];
end intrinsic;

intrinsic Representative(F::TorFan) -> TorCon
{A representative cone in the fan F}
    Cs:=Cones(F);
    if #Cs eq 0 then
        return Zero(F);
    else
        return Representative(Cs);
    end if;
end intrinsic;

intrinsic Zero(F::TorFan) -> TorCon
{The 0-dimensional cone of the fan F}
    return Representative(Cones(F,0));
end intrinsic;

intrinsic ConesOfCodimension(F::TorFan, n::RngIntElt) -> SeqEnum[TorCon]
{The codimension n cones in the fan F}
   return Cones(F,Dimension(Ambient(F)) - n);
end intrinsic;

intrinsic ConeIntersection(F::TorFan,C1::TorCon,C2::TorCon) -> TorCon
{The intersection of two cones C1 and C2 in the fan F. This is usually more efficient than C1 meet C2.}
    require Ambient(F) eq Ambient(C1):
        "Argument 2 must have the same ambient as the fan.";
    require Ambient(F) eq Ambient(C2):
        "Argument 3 must have the same ambient as the fan.";
    ind1:=check_and_get_index_of_cone_in_fan(F,C1);
    ind2:=check_and_get_index_of_cone_in_fan(F,C2);
    require not IsZero(ind1): "Argument 2 is not in the fan.";
    require not IsZero(ind2): "Argument 3 is not in the fan.";
    return get_intersection(F,ind1,ind2);
end intrinsic;

//THINK: Can we improve, to not contstruct intermediate fans/cones?
//       Or at least to create less of them?
intrinsic SimplicialSubdivision(F::TorFan) -> TorFan
{A simplicial fan subdividing the fan F}
    rays:=Rays(F);
    cones:=Cones(F);
    j:=0;
    repeat
        j+:=1;
        if j gt #cones then
            return F;
        end if;
        C:=cones[j];
    until not IsQFactorial(C);
    Rgens:=MinimalRGenerators(C);
    i:=0;
    repeat
        i+:=1;
        others:=Remove(Rgens, i);
    until Rank(Matrix(others)) eq Dimension(C);
    R:=Rgens[i];
    return $$(Blowup(F,R));
end intrinsic;

// Input: A (not necessarily simplicial) fan F.
// Output: A non-deterministic resolution of F.
function get_resolution_random(F)
    cones:=Cones(F);
    i:=1;
    while i le #cones do
        C:=cones[i];
        if IsNonsingular(C) then
            i +:= 1;
        else
            if IsSimplicial(C) then
                if Dimension(C) eq 2 or Index(C) le 20 then
                    zgens:=ZGenerators(C);
                    bool:=true;
                    repeat
                        v:=Random(zgens);
                        if not v in MinimalRGenerators(C) then
                            bool:=false;
                        end if;
                    until not bool;
                else
                    v:=PointToBlowUp(C);
                end if;
            else
                v:=Random(MinimalRGenerators(C));
            end if;
            Bl:=Blowup(F,v);
            return $$(Bl);
        end if;
    end while;
    return F;
end function;

// Input: A simplicial cone C and a lattice point v in C.
// Output: True iff the maximum-dimensional cones of the resulting subdivision
// of C will all have index strictly less that the index of C (where by index we
// mean the index of the sublattice generated by the rays of the cone).
function subdivision_reduces_index(C,v)
    idx:=Index(C);
    rays:=Rays(C);
    d:=#rays;
    // Check through the resulting indices
    for I in Subsets({1..#rays},#rays - 1) do
        newrays:=[v] cat [rays[i] : i in I];
        if Rank(Matrix(Rationals(),newrays)) eq d and Index(newrays) ge idx then
            return false;
        end if;
    end for;
    // If we're here then it was a success
    return true;
end function;

// Input: A simplicial fan F.
// Output: A (deterministic) resolution of F.
function get_resolution(F)
    // Get a singular cone to work with
    for C in Cones(F) do
        if not IsNonsingular(C) then
            // Find points to blow-up that result in a subdivision with strictly
            // smaller indices
            r,u:=GorensteinIndex(C);
            i:=0;
            repeat
                i +:= 1;
                found:=false;
                for v in Points(C,u,i/r) do
                    if IsPrimitive(v) and subdivision_reduces_index(C,v) then
                        found:=true;
                        pt:=v;
                        break;
                    end if;
                end for;
            until found;
            // Recurse on the subdivided fan
            return $$(Blowup(F,pt));
        end if;
    end for;
    // If we're here then the fan is nonsingular
    return F;
end function;

// Input: A simplicial fan F.
// Output: A (deterministic) refinement of F with only terminal singularities.
function get_terminalisation(F)
    // Get a singular cone to work with
    for C in Cones(F) do
        if not IsTerminal(C) then
            // Find a point in C at height i/r
            r,u:=GorensteinIndex(C);
            i:=0;
            repeat
                i +:= 1;
                found:=false;
                for v in Points(C,u,i/r) do
                    if IsPrimitive(v) then
                        found:=true;
                        pt:=v;
                        break;
                    end if;
                end for;
            until found;
            // Recurse on the subdivided fan
            return $$(Blowup(F,pt));
        end if;
    end for;
    // If we're here then the fan is terminal
    return F;
end function;

// Input: A simplicial fan F.
// Output: A (deterministic) refinement of F with only canonical singularities.
function get_canonicalisation(F)
    // Get a singular cone to work with
    for C in Cones(F) do
        if not IsTerminal(C) then
            // Find a point in C at height i/r
            r,u:=GorensteinIndex(C);
            i:=0;
            repeat
                i +:= 1;
                found:=false;
                for v in Points(C,u,i/r) do
                    if IsPrimitive(v) then
                        found:=true;
                        pt:=v;
                        break;
                    end if;
                end for;
            until found;
            // Recurse on the subdivided fan
            return $$(Blowup(F,pt));
        end if;
    end for;
    // If we're here then the fan is canonical
    return F;
end function;

intrinsic Resolution(F::TorFan : deterministic:=true) -> TorFan
{A resolution of singularities of the fan F. If the optional parameter 'deterministic' (default: true) is set to false then a non-deterministic algorithm will be used to calculate the resolution.}
    if not assigned F`resolution then
        require Type(deterministic) eq BoolElt:
            "The parameter 'deterministic' must be a boolean.";
        if deterministic then
            FF:=SimplicialSubdivision(F);
            F`resolution:=get_resolution(FF);
            if not assigned FF`resolution then
                FF`resolution:=F`resolution;
            end if;
        else
            F`resolution:=get_resolution_random(F);
        end if;
    end if;
    return F`resolution;
end intrinsic;

intrinsic Terminalisation(F::TorFan) -> TorFan
{A Q-factorial terminal refinement of the fan F}
    if not assigned F`terminalisation then
	   FF:=SimplicialSubdivision(F);
	   if not assigned FF`terminalisation then
	       FF`terminalisation:=get_terminalisation(FF);
	   end if;
	   F`terminalisation:=FF`terminalisation;
    end if;
    return F`terminalisation;
end intrinsic;

intrinsic Canonicalisation(F::TorFan) -> TorFan
{A Q-factorial canonical refinement of the fan F}
    if not assigned F`canonicalisation then
        FF:=SimplicialSubdivision(F);
        if not assigned FF`canonicalisation then
            FF`canonicalisation:=get_canonicalisation(FF);
        end if;
        F`canonicalisation:=FF`canonicalisation;
    end if;
    return F`canonicalisation;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//             fan equality, support  and inclusions
///////////////////////////////////////////////////////////////////////

intrinsic 'eq'(F1::TorFan, F2::TorFan) -> BoolElt
{True iff the fans F1 and F2 are equal}
     if not Ambient(F1) eq Ambient(F2) then
        return false;
     end if;
     if Dimension(Ambient(F1)) eq 0 then
        return true;
     end if;
     _:=VirtualRays(F1);
     _:=VirtualRays(F2);
     if not (Rays(F1) subset Rays(F2) and Rays(F2) subset Rays(F1)) then
 	return false;
     end if;
     indices1:=ConeIndices(F1);
     indices2:=ConeIndices(F2:rays:=Rays(F1));
     return indices1 subset indices2 and indices2 subset indices1;
end intrinsic;

intrinsic IsComplete(F::TorFan) -> BoolElt
{True iff the fan F is complete}
    if not assigned F`is_complete then
        if Dimension(Ambient(F)) eq 0 then
            F`is_complete:=true;
        else
            max_cones:=[Sort([Index(Rays(F),ray) :
                             ray in MinimalRGenerators(C)]) : C in MaxCones(F)];
            facets:=[Sort([Index(Rays(F),ray) :
                 ray in MinimalRGenerators(C)]) : C in ConesOfCodimension(F,1)];
            F`is_complete:={#[cone : cone in max_cones | facet subset cone] :
                                                        facet in facets} eq {2};
        end if;
    end if;
    return F`is_complete;
end intrinsic;

intrinsic IsProjective(K::Rng, F::TorFan) -> BoolElt
{True iff the fan F defines a projecive variety over the ring K (i.e. iff F is complete and the nef cone is of maximum dimension)}
    if not IsComplete(F) then
        return false;
    end if;
    return IsProjective(ToricVariety(K,F));
end intrinsic;

intrinsic IsInSupport(v::TorLatElt,F::TorFan) -> BoolElt, RngIntElt
{True iff the toric lattice point v is in support of the fan F. If true, then the index of the first cone in F found to contain v is also given.}
  i:=1;
  while i le #Cones(F) do
     if v in Cones(F)[i] then
        return true, i;
     end if;
     i +:=1;
  end while;
  return false, _;
end intrinsic;

intrinsic InnerNormals(F::TorFan) -> SeqEnum[TorLatElt]
{If all the cones of the fan F are Q-Gorenstein, gives a sequence of elements in the dual lattice where the i-th element is the inner normal of the i-th cone of F.}
    require IsQGorenstein(F):
        "The fan contains at least one cone that is not Q-Gorenstein.";
    return [Dual(Ambient(F)) | InnerNormal(C) : C in Cones(F)];
end intrinsic;

intrinsic OuterNormals(F::TorFan) -> SeqEnum[TorLatElt]
{If all the cones of the fan F are Q-Gorenstein, gives a sequence of elements in the dual lattice where the i-th element is the outer normal of the i-th cone of F.}
    require IsQGorenstein(F):
        "The fan contains at least one cone that is not Q-Gorenstein.";
    return [Dual(Ambient(F)) | OuterNormal(C) : C in Cones(F)];
end intrinsic;

///////////////////////////////////////////////////////////////////////
//             Geometric properties of associated varieties
///////////////////////////////////////////////////////////////////////

intrinsic IsGorenstein(F::TorFan) -> BoolElt
{True iff all cones of the fan F are Gorenstein}
     return &and[IsGorenstein(C): C in Cones(F)];
end intrinsic;

intrinsic IsQGorenstein(F::TorFan) -> BoolElt
{True iff all cones of the fan F are Q-Gorenstein}
     return &and[IsQGorenstein(C): C in Cones(F)];
end intrinsic;

intrinsic IsQFactorial(F::TorFan) -> BoolElt
{True iff all cones of the fan F are Q-factorial}
     return &and[IsQFactorial(C): C in Cones(F)];
end intrinsic;

intrinsic IsIsolated(F::TorFan) -> BoolElt
{True iff all cones of the fan F are isolated}
    return &and[IsIsolated(C): C in Cones(F)];
end intrinsic;

intrinsic IsTerminal(F::TorFan) -> BoolElt
{True iff all cones of the fan F are terminal}
     return &and[IsTerminal(C): C in Cones(F)];
end intrinsic;

intrinsic IsCanonical(F::TorFan) -> BoolElt
{True iff all cones of the fan F are canonical}
     return &and[IsCanonical(C): C in Cones(F)];
end intrinsic;

intrinsic IsSingular(F::TorFan) -> BoolElt
{True iff there exists a singular cone in the fan of F}
    return not IsNonsingular(F);
end intrinsic;

intrinsic IsNonSingular(F::TorFan) -> BoolElt
{True iff all cones of the fan F are nonsingular}
    return IsNonsingular(F);
end intrinsic;

intrinsic IsNonsingular(F::TorFan) -> BoolElt
{True iff all cones of the fan F are nonsingular}
    return &and[IsNonsingular(C) : C in Cones(F)];
end intrinsic;

intrinsic SingularCones(F::TorFan)
    -> SeqEnum[TorCon], SeqEnum[SeqEnum[RngIntElt]]
{The minimum sequence of singular cones of the fan F. Also gives the sequences
of indices of the rays of F defining each singular cone.}
     faces:=AllCones(F);
     faces_indices:=[[ConeIndices(F,C) : C in cones]: cones in faces];
     singular:=[];
     for dim in [3..#faces_indices] do
        for i in [1..#faces_indices[dim]] do
           if not (&or[faces_indices[s[1]][s[2]] subset faces_indices[dim][i] : s in singular]
                 or IsNonsingular(faces[dim][i])) then
              Append(~singular,[dim,i]);
           end if;
        end for;
     end for;
     return [faces[s[1]][s[2]] : s in singular ],
            [faces_indices[s[1]][s[2]] : s in singular ];
end intrinsic;


intrinsic NonSimplicialCones(F::TorFan)
    -> SeqEnum[TorCon],SeqEnum[SeqEnum[RngIntElt]]
{The minimum sequence of non-simplicial cones of the fan F. Also gives the
sequences of indices of the rays of F defining each non-simplicial cone.}
     faces:=AllCones(F);
     faces_indices:=[[ConeIndices(F,C) : C in cones]: cones in faces];
     non_simplicial:=[];
     // AllCones start from dimension 0; We want to start from Dimension=3
     for dim in [4..#faces_indices] do
        for i in [1..#faces_indices[dim]] do
           if not (#faces_indices[dim][i] eq dim-1 or
                &or[faces_indices[s[1]][s[2]] subset faces_indices[dim][i]
                : s in non_simplicial]) then
              Append(~non_simplicial,[dim,i]);
           end if;
        end for;
     end for;
     return [faces[s[1]][s[2]] : s in non_simplicial ],
            [faces_indices[s[1]][s[2]] : s in non_simplicial ];
end intrinsic;


///////////////////////////////////////////////////////////////////////
//              Fan maps
///////////////////////////////////////////////////////////////////////

intrinsic Image(phi::Map[TorLat,TorLat],F::TorFan) -> TorFan
{The image of the fan F under the toric lattice map phi}
    require IsEmpty(KernelBasis(phi)): "The map must be injective.";
    if assigned F`rays then
        bool,FF:=construct_fan_from_rays([PrimitiveLatticeVector(phi(r)) :
                                            r in Rays(F)],Image(phi,Cones(F)) :
                                            max_cones:=true, min_rays:=true);
        require bool: FF;
    else
        FF:=construct_fan_from_cones(Image(phi,Cones(F)): max_cones:=true);
        propagate_all_cones(FF);
    end if;
    return FF;
end intrinsic;

intrinsic '@'(F::TorFan,phi::Map[TorLat,TorLat]) -> TorFan
{The image of the fan F under the toric lattice map phi}
    require IsEmpty(KernelBasis(phi)): "The map must be injective.";
    return Image(phi,F);
end intrinsic;

intrinsic IsFanMap(F1::TorFan,F2::TorFan) -> BoolElt
{True iff the toric lattice identity map determines a map of fans F1 -> F2 (i.e. iff each cone of F1 is a subcone of some cone of F2)}
    require Ambient(F1) eq Ambient(F2): "Fans must live in the same ambient.";
    return &and[&or[cone_source subset cone_target : cone_target in Cones(F2)] :
                                                      cone_source in Cones(F1)];
end intrinsic;

intrinsic IsFanMap(F1::TorFan,F2::TorFan, phi::Map[TorLat,TorLat]) -> BoolElt
{True iff the lattice map phi is a map of fans F1 -> F2, i.e. if phi applied to each cone of F1 is a subcone of some cone of F2}
     require Ambient(F1) eq Domain(phi):
        "The domain of the map must be the ambient of Argument 1.";
     require Ambient(F2) eq Codomain(phi):
        "The codomain of the map must be the ambient of Argument 2.";
     return &and[&or[Image(phi,cone_source) subset cone_target
                : cone_target in Cones(F2)]
                : cone_source in Cones(F1)];
end intrinsic;

intrinsic 'in'(C::TorCon, F::TorFan) -> BoolElt
{True iff C a cone of F (not necessary maximal, could be a face of any other cone)}
     require Ambient(C) eq Ambient(F):
        "Arguments must live in the same ambient.";
     return not IsZero(check_and_get_index_of_cone_in_fan(F,C));
end intrinsic;

//THINK: this function should work for other lattice maps too (not only for identity):
intrinsic ResolveFanMap(F1::TorFan, F2::TorFan) -> TorFan
{Given two fans F1 and F2 in the same lattice, finds the fan F such that the lattice identity induces fan maps: F->F1 and F->F2. F1 and F2 are expected to have the same support, otherwise non-proper resolution (more precisely supported at the intersection of the supports of F1 and F2) will be returned.}

    cones:=[cone1 meet cone2 : cone1 in Cones(F1), cone2 in Cones(F2)];
    R:=&cat[MinimalRGenerators(C) : C in cones];
    R12:=PureRays(F1) cat PureRays(F2);
    remove_repetitions(~R);
    remove_repetitions(~R12);
    i:=1;
    while i le #R12  do
        j:=Index(R, R12[i]);
        if j eq 0 then
            Remove(~R12,i);
        else
            Remove(~R,j);
            i+:=1;
        end if;
    end while;

    bool,F:=construct_fan_from_rays(R12 cat R, cones);
    require bool: F;
    return F;
end intrinsic;
