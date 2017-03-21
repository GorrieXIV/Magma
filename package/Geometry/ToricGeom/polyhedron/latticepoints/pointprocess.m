freeze;

/////////////////////////////////////////////////////////////////////////
// pointprocess.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 37396 $
// $Date: 2012-02-16 17:18:38 +1100 (Thu, 16 Feb 2012) $
// $LastChangedBy: allan $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Processes for listing lattice points in a polytope.
/////////////////////////////////////////////////////////////////////////

import "../../utilities/functions.m": bounding_box;
import "../../lattice/hyperplane.m": cmp_hyperplane_and_point;
import "../convexhull/sublattice.m": fp_emb_map, fp_emb_lattice;
import "../convexhull/convexhull.m": fp_get_pullback_vertices, fp_get_pullback_halfspaces;
import "../faces/support.m": amb_has_volume_form;

/////////////////////////////////////////////////////////////////////////
// Functions for the zero dimensional polytope process
/////////////////////////////////////////////////////////////////////////

// True iff the process is empty.
function pt_is_empty(info)
    return info[1];
end function;

// Returns the current value.
function pt_value(info)
    error if info[1], "The process has finished.";
    return info[2];
end function;

// Returns the current label.
function pt_label(info)
    error if info[1], "The process has finished.";
    return 1;
end function;

// Advances the process to the next value.
procedure pt_advance(~info)
    error if info[1], "The process has finished.";
    info[1]:=true;
end procedure;

// Create a new point process for a 0-dimensional P
function create_pt_process(P)
    pt:=Vertices(P)[1];
    info:=IsIntegral(pt) select <false,pt> else <true>;
    return InternalCreateProcess("Point",info,pt_is_empty,pt_advance,
                                                             pt_value,pt_label);
end function;

/////////////////////////////////////////////////////////////////////////
// Functions for the general dimensional polytope process
/////////////////////////////////////////////////////////////////////////

// True iff the process is empty.
function ft_is_empty(info)
    return info[1];
end function;

// Returns the current value.
function ft_value(info)
    error if info[1], "The process has finished.";
    return info[4](info[2] ! info[8]) + info[5];
end function;

// Returns the current label.
function ft_label(info)
    error if info[1], "The process has finished.";
    return info[9];
end function;

// Returns true followed by the next point in the bounding box, or false if
// there are no more points.
function ft_find_next_point(embL,hs,min,max,pt)
    while true do
        i:=#pt;
        pt[i] +:= 1;
        while pt[i] gt max[i] do
            if i eq 1 then return false,_; end if;
            pt[i]:=min[i];
            i -:= 1;
            pt[i] +:= 1;
        end while;        
        v:=embL ! pt;
        if &and[cmp_hyperplane_and_point(h[1],v) * h[2] ge 0 : h in hs] then
            return true,pt;
        end if;
    end while;
end function;

// Advances the process to the next value.
procedure fp_advance(~info)
    error if info[1], "The process has finished.";
    bool,pt:=ft_find_next_point(info[2],info[3],info[6],info[7],info[8]);
    if bool then
        info[8]:=pt;
        info[9] +:= 1;
    else
        info[1]:=true;
    end if;
end procedure;

// Returns true followed by the first point in the bounding box, or false if
// there are no points.
function ft_find_first_point(embL,hs,min,max)
    pt:=min;
    v:=embL ! pt;
    if &and[cmp_hyperplane_and_point(h[1],v) * h[2] ge 0 : h in hs] then
        return true,pt;
    end if;
    bool,pt:=ft_find_next_point(embL,hs,min,max,pt);
    if bool then
        return true,pt;
    else
        return false,_;
    end if;
end function;

// Create a new point process for the polytope P
function create_ft_process(P)
    // Handle the degenerate case
    if not amb_has_volume_form(P) then
        return InternalCreateProcess("Point",<true>,ft_is_empty,fp_advance,
                                                         ft_value,ft_label);
    end if;
    // We do the calculation in the "finite part" lattice L' and lift the points
    // back to the ambient lattice L as needed
    trans,emb:=fp_emb_map(P);
    hs:=fp_get_pullback_halfspaces(P);
    embL:=fp_emb_lattice(P);
    // Generate the bounding box
    min,max:=bounding_box([Eltseq(v) : v in fp_get_pullback_vertices(P)]);
    min:=[Integers() | Ceiling(c) : c in min];
    max:=[Integers() | Floor(c) : c in max];
    // Return the process
    bool,pt:=ft_find_first_point(embL,hs,min,max);
    info:=bool select <false,embL,hs,emb,trans,min,max,pt,1> else <true>;
    return InternalCreateProcess("Point",info,ft_is_empty,fp_advance,
                                                         ft_value,ft_label);
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic PointProcess(P::TorPol) -> Process
{A process generating all points in the polytope P}
    require IsPolytope(P): "The polyhedron must be a polytope";
    if Dimension(P) eq 0 then
        return create_pt_process(P);
    else
        return create_ft_process(P);
    end if;
end intrinsic;
