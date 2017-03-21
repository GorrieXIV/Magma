freeze;

/////////////////////////////////////////////////////////////////////////
// svg.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36857 $
// $Date: 2012-01-09 07:02:03 +1100 (Mon, 09 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Outputs a polygon to an svg file.
/////////////////////////////////////////////////////////////////////////

import "javaview.m": get_date, get_version, order_vertices;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Outputs the svg file's headers
procedure write_header(file,scale,width,height,diag,padding)
    // Extract the horizontal and vertical padding
    if Type(padding) eq SeqEnum then
        paddingh:=padding[1];
        paddingv:=padding[2];
    else
        paddingh:=padding;
        paddingv:=padding;
    end if;
    // Output the headers
    fprintf file,"<?xml version=\"1.0\" standalone=\"no\"?>\n";
    fprintf file,"<!DOCTYPE svg PUBLIC \"-//W3C//DTD SVG 1.1//EN\" \"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd\">\n";
    fprintf file,"<!-- Created with %o (http://magma.maths.usyd.edu.au/) -->\n",
                                                                  get_version();
    date:=get_date();
    if date ne "" then
        fprintf file, "<!-- Created on %o -->\n", date;
    end if;
    fprintf file,"<svg width=\"100%%\" height=\"100%%\" viewBox=\"0 0 %o %o\" version=\"1.1\" xmlns=\"http://www.w3.org/2000/svg\">\n",
                                    2 * paddingh + scale * width + 2 * diag,
                                    2 * paddingv + scale * height + 2 * diag;
    fprintf file,"  <g transform=\"translate(%o,%o)\">\n",
                                    paddingh + diag, paddingv + diag;
end procedure;

// Writes a [0..n] x [0..m] grid of lattice points to the given svg file.
procedure write_lattice(file,scale,n,m,diag : colour:=[178,178,178])
    colour:=Sprintf("%o,%o,%o",colour[1],colour[2],colour[3]);
    for i in [0..n] do
        for j in [0..m] do
            ii:=i * scale;
            jj:=j * scale;
            fprintf file, "    <line x1=\"%o\" y1=\"%o\" x2=\"%o\" y2=\"%o\" style=\"stroke:rgb(%o)\"/>\n", ii - diag, jj - diag, ii + diag, jj + diag, colour;
            fprintf file, "    <line x1=\"%o\" y1=\"%o\" x2=\"%o\" y2=\"%o\" style=\"stroke:rgb(%o)\"/>\n", ii - diag, jj + diag, ii + diag, jj - diag, colour;
        end for;
    end for;
end procedure;

// Writes a [0..n] x [0..m] grid to the given svg file.
procedure write_grid(file,scale,n,m : colour:=[178,178,178])
    colour:=Sprintf("%o,%o,%o",colour[1],colour[2],colour[3]);
    mm:=m * scale;
    for i in [0..n] do
        ii:=i * scale;
        fprintf file, "    <line x1=\"%o\" y1=\"%o\" x2=\"%o\" y2=\"%o\" style=\"stroke-dasharray: 3, 3;stroke:rgb(%o)\"/>\n", ii, 0, ii, mm, colour;
    end for;
    nn:=n * scale;
    for i in [0..m] do
        ii:=i * scale;
        fprintf file, "    <line x1=\"%o\" y1=\"%o\" x2=\"%o\" y2=\"%o\" style=\"stroke-dasharray: 3, 3;stroke:rgb(%o)\"/>\n", 0, ii, nn, ii, colour;
    end for;
end procedure;

// Writes the origin to the given svg file.
procedure write_origin(file,lattice,scale,orig,diag)
    orig:=Eltseq(orig * scale);
    if lattice eq "grid" then
        fprintf file, "    <circle cx=\"%o\" cy=\"%o\" r=\"%o\" style=\"fill:none;stroke:black\"/>\n", orig[1], orig[2], diag;
    else
        fprintf file, "    <line x1=\"%o\" y1=\"%o\" x2=\"%o\" y2=\"%o\" style=\"stroke:black\"/>\n", orig[1] - diag, orig[2] - diag, orig[1] + diag, orig[2] + diag;
        fprintf file, "    <line x1=\"%o\" y1=\"%o\" x2=\"%o\" y2=\"%o\" style=\"stroke:black\"/>\n", orig[1] - diag, orig[2] + diag, orig[1] + diag, orig[2] - diag;
    end if;
end procedure;

// Writes the edges of the polygon P to the given svg file.
procedure write_polygon(file,scale,P)
    verts:=Vertices(P);
    verts:=[Eltseq(verts[i + 1] * scale) : i in order_vertices(P,{1..#verts})];
    fprintf file, "    <polygon points=\"";
    for i in [1..#verts - 1] do
        fprintf file, "%o,%o ", verts[i][1], verts[i][2];
    end for;
    fprintf file, "%o,%o\" style=\"fill:none;stroke:black\"/>\n", verts[#verts][1], verts[#verts][2];
end procedure;

// Outputs the svg file's footers
procedure write_footer(file)
    fprintf file, "  </g>\n</svg>\n";
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

// Outputs the polygon P to the given svg file.
intrinsic WritePolytopeToSvgFile( P::TorPol, F::MonStgElt : scale:=1,
    lattice:="points", padding:=0, mark_origin:=true )
{Writes the polygon P to an svg file F. Optional parameter 'lattice' can be used to select an output style for the lattice. Valid styles are "points", "grid", and "none".}
    // Sanity check
    require IsPolytope(P) and Dimension(P) eq 2:
        "The polyhedron must be a two dimensional polytope";
    require IsMaximumDimensional(P):
        "The polygon must be of maximum dimension in the ambient lattice";
    require (Type(scale) eq RngIntElt or Type(scale) eq FldReElt or
             Type(scale) eq FldRatElt) and scale gt 0:
        "Parameter 'scale' must be greater than zero";
    require Type(lattice) eq MonStgElt and lattice in {"points","grid","none"}:
        "Parameter 'lattice' must be one of \"points\", \"grid\", or \"none\"";
    require (Type(padding) eq RngIntElt and padding ge 0) or
            (Type(padding) eq SeqEnum and #padding eq 2 and
             Universe(padding) cmpeq Integers() and
             padding[1] ge 0 and padding[2] ge 0):
        "Parameter 'padding' must be a positive integer, or a sequence of two positive integers";
    require Type(mark_origin) eq BoolElt:
        "Parameter 'mark_origin' must be a boolean";
    // Compute the scale
    scale:=Floor(13 * scale);
    // Compute the bounding box
    B,min,max:=BoundingBox(P);
    min:=Parent(min) ! [Floor(c) : c in Eltseq(min)];
    max:=Parent(max) ! [Ceiling(c) : c in Eltseq(max)];
    n:=Eltseq(max)[1] - Eltseq(min)[1];
    m:=Eltseq(max)[2] - Eltseq(min)[2];
    // Open the file for writing
    F:=Open(F,"w");
    // Output the header
    diag:=lattice eq "points" select 3 else 2;
    write_header(F,scale,n,m,diag,padding);
    // Output the lattice
    if lattice ne "none" then
        if lattice eq "points" then
            write_lattice(F,scale,n,m,diag);
        elif lattice eq "grid" then
            write_grid(F,scale,n,m);
        end if;
    end if;
    // Indicate the origin
    if mark_origin and Zero(Ambient(B)) in B then
        write_origin(F,lattice,scale,-min,diag);
    end if;
    // Output the polygon
    write_polygon(F,scale,P - min);
    // Output the footer and close the file
    write_footer(F);
    delete F;
end intrinsic;
