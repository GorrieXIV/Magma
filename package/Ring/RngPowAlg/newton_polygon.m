// *********************************************************************
// * Package: newton_polygon.mag                                       *
// * ===========================                                       *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 29.12.2005                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Tools for computing Newton polygons and generators of certain   *
// *   rational cones.                                                 *
// *                                                                   *
// *********************************************************************
freeze;

import "power_series.m" : Trailing;




// ======================================
// = Auxillary functions (not exported) =
// ======================================

// find leftmost points in a sequence
// ----------------------------------
// input:  a sequence 'pts' of points of the form '<x,y>'
// output: a sequence of points (ordered by the 'y'-component and a subset
//         of 'pts') consisting of those elements with smallest 'x'-component
function FindStartPoints(pts)
	spts := [];
	for pt in pts do
		i := 1; for pt2 in spts do
			// new point on known 'y'-coord?
			if (pt2[2] eq pt[2]) then
				if (pt[1] lt pt2[1]) then
					spts[i] := pt;
				end if;
				continue pt;
			end if;
			// new point on new 'y'-coord?
			if (pt2[2] gt pt[2]) then
				Insert(~spts, i, pt);
				continue pt;
			end if;
			i := i + 1;
		end for;
		// new maximum 'y'-coord!
		Append(~spts, pt);
	end for;
	
	return Reverse(spts);
end function;


// find convex hull with positive line
// -----------------------------------
// input:  a sequence 'spts' of points of the form '<x,y>' and two
//         functions 'add' and 'mult' for adding and multiplying
//         elements of the 'x'-component, assuming that each 'y'-component
//         appears only once (see output of 'FindStartPoints')
// output: the subset of 'spts' which lies on the compact faces of the
//         Minkowski sum of the convex hull of 'spts' and the positive
//         line in 'x'-direction
function HullWithPositiveLine(spts, add, mult : OnlyVertices := false)
	// trivial case
	if #spts eq 0 then
		return spts;
	end if;
	
	// find edges successively
	l := #spts; i := 1; hull := [spts[1]];
	while (i lt l) do
		// start with obvious choice for edge
		pt1 := spts[i]; i := i+1; pt2 := spts[i]; edge := [pt2];
		
		// modify edge according to remaining points
		for j := i+1 to l do
			// test next point pt
			pt := spts[j];
			
			// slopes to be compared:
			// s2 := (pt1[2]-pt2[2])/(pt2[1]-pt1[1]);
			// s3 := (pt1[2]- pt[2])/( pt[1]-pt1[1]);
			// s2 := pt1[2]* pt[1] + pt2[2]*pt1[1] +  pt[2]*pt2[1];
			// s3 := pt1[2]*pt2[1] +  pt[2]*pt1[1] + pt2[2]* pt[1];
			s2 := add(add(mult(pt1[2],  pt[1]),
			              mult(pt2[2], pt1[1])),
			          mult( pt[2], pt2[1]));
			s3 := add(add(mult(pt1[2], pt2[1]),
			              mult( pt[2], pt1[1])),
			          mult(pt2[2],  pt[1]));
			
			if s2 gt s3 then
				// pt in strict interior of the halfplane
			        // above pt1pt2 => nothing to do!
			elif s2 eq s3 then
				// pt on line pt1pt2
				Append(~edge, pt); pt2 := pt; i := j;
			else
				// pt below the halfplane above pt1pt2
				edge := [pt]; pt2 := pt; i := j;
			end if;
		end for;
		
		// add edge or vertex to contour
		if OnlyVertices then
			Append(~hull, pt2);    // just the vertex
		else
			hull := hull cat edge; // the point subset on the edge
		end if;
	end while;
	
	return hull;
end function;


// find convex hull with positive quadrant
// ---------------------------------------
// input:  a sequence 'hull' of points of the form '<x,y>', the points
//         already lie on the compact faces of the Minkowski sum of the
//         convex hull of 'hull' and the positive line in 'x'-direction
//         (see output of 'HullWithPositiveLine')
// output: the subset of 'hull' which lies on the compact faces of the
//         Minkowski sum of the convex hull of 'pts' and the positive
//         quadrant
function HullWithPositiveQuadrant(hull)
	// trivial case
	if #hull eq 0 then
		return hull;
	end if;
	
	// delete edges with wrong slope
	pt := hull[#hull]; Prune(~hull);
	nhull := [pt];
	while not IsEmpty(hull) do
		pt2 := hull[#hull]; Prune(~hull);
		if pt2[1] lt pt[1] then
			Append(~nhull, pt2);
			pt := pt2;
		end if;
	end while;
	
	return Reverse(nhull);
end function;




// ======================
// = Exported functions =
// ======================

// compute the classical Newton Polygon with integer vertices
intrinsic GetIntegerNewtonPolygon(pts::SeqEnum : OnlyVertices := true)
-> SeqEnum
{
Given a sequence 'pts' of points in 'Z^2'. Return the subset of 'pts' which
lies on the compact faces of the Minkowski sum of the convex hull of 'pts'
and the positive quadrant, if 'OnlyVertices' is true only the vertices are
returned.
}
	spts := FindStartPoints(pts);
	hull1 := HullWithPositiveLine(spts, func<x,y|x+y>, func<x,y|x*y> :
	                              OnlyVertices := OnlyVertices);
	hull2 := HullWithPositiveQuadrant(hull1);
	
	return hull2;
end intrinsic;


// compute the Newton Polygon with monoid vertices
intrinsic GetMonoidNewtonPolygon(poly::RngUPolElt)
-> SeqEnum
{
Given a univariate polynomial 'poly' over a multivariate polynomial ring.
Compute the vertices of the generalized Newton polygon. Here a vertex is
of the form '<z,X>' where 'z' is an integer and 'X' is a monomial in the
coefficient ring.
}
	d := Degree(poly);
	
	// Find trailing terms
	spts := []; for i := d to 0 by -1 do
		_, exp := Trailing(Coefficient(poly, i));
		if not (exp eq 0) then
			Append(~spts, <exp, i>);
		end if;
	end for;
	
	// Find hull with 'positive line'
	// (only vertices needed)
	hull := HullWithPositiveLine(spts, func<x,y|x*y>, func<x,y|y^x>
	                             : OnlyVertices := true);
	
	// swap x and y coordinate
	return [<pt[2], pt[1]> : pt in hull];
end intrinsic;
