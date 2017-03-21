freeze;

// Package for standard processes.
//
// Alexandra Flynn	March 1998
//
//
// To create a process (in category Process):
//
//    p := InternalCreateProcess(name, info, IsEmptyFunc, AdvanceFunc, CurrentFunc, LabelFunc);
//
// 'name' is a string used in printing the process ("'name' Process").
// 'info' is a tuple containing all the info needed for this particular process.
// The remaining arguments are Programs which accept the info tuple
//  as an argument.
//
// Standard Process functions:
//
// IsEmpty(p): true if no objects remain in the process p
// Advance(~p): move the process p to its next group
// Current(p): the current object of the process p
// CurrentLabel(p): the label of the current object of p
//
// For an example of the use of processes see the GrpPerm/trngps.m package.

intrinsic IsEmpty(p :: Process) -> BoolElt
{True if no objects remain in the process}

    return (InternalGetProcessIsEmpty(p))(InternalGetProcessInfo(p));

end intrinsic;

intrinsic Advance(~p :: Process)
{Advance to the next object in the process}

    info := InternalGetProcessInfo(p);
    (InternalGetProcessAdvance(p))(~info);
    InternalSetProcessInfo(p, info);

end intrinsic;

intrinsic Current(p :: Process) -> .
{Get the current object of the process}

    return (InternalGetProcessCurrent(p))(InternalGetProcessInfo(p));

end intrinsic;

intrinsic CurrentLabel(p :: Process) -> .
{The Label of the current object of the process}

    return (InternalGetProcessLabel(p))(InternalGetProcessInfo(p));

end intrinsic;

/* This function is here to be called from C-level */
intrinsic InternalAdvanceFunc(p :: Process)
{Advance to the next object in the process}

    info := InternalGetProcessInfo(p);
    (InternalGetProcessAdvance(p))(~info);
    InternalSetProcessInfo(p, info);

end intrinsic;
