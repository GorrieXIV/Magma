freeze;
// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

/*
    Intrinsics for jacobians of hyperelliptic curves 
    (types JacHyp and JacHypPt)

    RR, July 1998
*/

intrinsic '+:='(~pt1::JacHypPt, pt2::JacHypPt)
{ Change pt1 to pt1 + pt2. }
    pt1 := pt1 + pt2;
end intrinsic;
 
intrinsic '-:='(~pt1::JacHypPt, pt2::JacHypPt)
{ Change pt1 to pt1 - pt2. }
    pt1 := pt1 - pt2;
end intrinsic;
 
intrinsic '*:='(~pt::JacHypPt, n::RngIntElt)
{ Change pt to n*pt. }
    pt := n * pt;
end intrinsic;
 


