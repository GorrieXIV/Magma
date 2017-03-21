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
// Processes for listing lattice points in a cone.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Functions for the 0-dimensional cone process
/////////////////////////////////////////////////////////////////////////

// True iff the process is empty.
function zero_is_empty(info)
    return info[1];
end function;

// Returns the current value.
function zero_value(info)
    error if info[1], "The process has finished.";
    return info[2];
end function;

// Returns the current label.
function zero_label(info)
    error if info[1], "The process has finished.";
    return 1;
end function;

// Advances the process to the next value.
procedure zero_advance(~info)
    error if info[1], "The process has finished.";
    info[1]:=true;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Functions for the ray process
/////////////////////////////////////////////////////////////////////////

// True iff the process is empty.
function ray_is_empty(info)
    return false;
end function;

// Returns the current value.
function ray_value(info)
    return info[2];
end function;

// Returns the current label.
function ray_label(info)
    return info[3];
end function;

// Advances the process to the next value.
procedure ray_advance(~info)
    info[2]:=info[1] * info[3];
    info[3] +:= 1;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Functions for the general dimensional pointed cone process
/////////////////////////////////////////////////////////////////////////

// True iff the process is empty.
function ptd_is_empty(info)
    return false;
end function;

// Returns the current value.
function ptd_value(info)
    return info[1](Current(info[4]));
end function;

// Returns the current label.
function ptd_label(info)
    return info[5];
end function;

// Advances the process to the next value.
procedure ptd_advance(~info)
    Advance(~info[4]);
    while IsEmpty(info[4]) do
        h:=info[3] + 1;
        info[3]:=h;
        info[4]:=PointProcess(h * info[2]);
    end while;
    info[5] +:= 1;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic PointProcess(C::TorCon) -> Process
{A process generating all points in the cone C}
    // Special case for the zero cone
    if IsZero(C) then
        info:=<false,Zero(Ambient(C))>;
        return InternalCreateProcess("Point",info,zero_is_empty,zero_advance,
                                                         zero_value,zero_label);
    end if;
    // We require that the cone is pointed (i.e. strictly convex)
    require IsStrictlyConvex(C): "The cone must be strictly convex";
    // Special case for a ray
    if Dimension(C) eq 1 then
        info:=<Rays(C)[1],Zero(Ambient(C)),1>;
        return InternalCreateProcess("Point",info,ray_is_empty,ray_advance,
                                                           ray_value,ray_label);
    end if;
    // Move to the sublattice containing C
    C,emb:=ConeInSublattice(C);
    // We need to choose a halfspace containing C
    if IsQGorenstein(C) then
        _,h:=GorensteinIndex(C);
        h:=PrimitiveLatticeVector(h);
    else
        h:=PrimitiveLatticeVector(&+Rays(Dual(C)));
    end if;
    // Create the process
    Q:=Polytope([v / (v * h) : v in Rays(C)] : areVertices:=true);
    P:=PointProcess(Polytope([Zero(Ambient(C))] : areVertices:=true));
    info:=<emb,Q,0,P,1>;
    return InternalCreateProcess("Point",info,ptd_is_empty,ptd_advance,
                                                           ptd_value,ptd_label);
end intrinsic;
