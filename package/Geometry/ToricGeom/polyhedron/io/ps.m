freeze;

/////////////////////////////////////////////////////////////////////////
// ps.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48810 $
// $Date: 2014-11-01 22:14:16 +1100 (Sat, 01 Nov 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Outputs a polygon to a PostScript file.
/////////////////////////////////////////////////////////////////////////

import "javaview.m": get_date, get_version, order_vertices;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Computes the bounding box for the given data. Returns the box (as a
// polytope), along with the bottom-left and top-right corners.
function bounding_box(P,point_labels,mark_points)
    // Do we need to enlarge P?
    pts:={Ambient(P)|};
    if Type(point_labels) eq Assoc then
        pts join:= {Ambient(P) | v : v in Keys(point_labels) | not v in P};
    end if;
    if Type(mark_points) eq SetEnum or Type(mark_points) eq SeqEnum then
        pts join:= {Ambient(P) | v : v in mark_points | not v in P};
    end if;
    if Type(mark_points) eq Assoc then
        pts join:= {Ambient(P) | v : v in Keys(mark_points) | not v in P};
    end if;
    Q:=#pts eq 0 select P else Polytope(Vertices(P) cat SetToSequence(pts));
    // Return the bounding box
    B,min,max:=BoundingBox(Q);
    return B,min,max;
end function;

// Outputs the PS file's headers
procedure write_header(file, scale, lattice, width, height, padding, textfuncs,
                                                                       fontsize)
    // Choose the size of the lattice points
    diag:=lattice eq "points" select 3 else 2;
    // Extract the horizontal and vertical padding
    if Type(padding) eq SeqEnum then
        paddingh:=padding[1];
        paddingv:=padding[2];
    else
        paddingh:=padding;
        paddingv:=padding;
    end if;
    // Output the header information
    fprintf file, "%%!PS-Adobe-2.0 EPSF-1.2\n%%%%Creator: %o\n",get_version();
    date:=get_date();
    if date ne "" then
        fprintf file, "%%%%CreationDate: %o\n",date;
    end if;
    fprintf file, "%%%%Pages: 1\n%%%%BoundingBox: 0 0 %o %o\n%%%%EndComments\n\n",
                                    2 * paddingh + scale * width + 2 * diag,
                                    2 * paddingv + scale * height + 2 * diag;
    // Translate the page's origin enough to allow the lattice points to fit
    fprintf file, "%o %o translate\n\n", paddingh + diag, paddingv + diag;
    // Output the commands for drawing text
    if textfuncs then
        fprintf file,"%%%%Text output functions\n";
        fprintf file,"/fontheight { currentfont /FontMatrix get 3 get } def\n";
        fprintf file,"/lineheight { fontheight 1.2 mul } def\n";
        fprintf file,"/voffset { fontheight 0.2 mul %o add } def\n",diag;
        fprintf file,"/addlabel_tr {\n  /data exch def\n  moveto data 0 voffset rmoveto show\n} def\n";
        fprintf file,"/addlabel_tl {\n  /data exch def\n  moveto data dup stringwidth pop neg voffset rmoveto show\n} def\n";
        fprintf file,"/addlabel_tc {\n  /data exch def\n  moveto data dup stringwidth pop 2 div neg voffset rmoveto show\n} def\n";
        fprintf file,"/addlabel_br {\n  /data exch def\n  moveto data 0 fontheight neg rmoveto show\n} def\n";
        fprintf file,"/addlabel_bl {\n  /data exch def\n  moveto data dup stringwidth pop neg fontheight neg rmoveto show\n} def\n";
        fprintf file,"/addlabel_bc {\n  /data exch def\n  moveto data dup stringwidth pop 2 div neg fontheight neg rmoveto show\n} def\n";
        fprintf file,"/addlabel_cr {\n  /data exch def\n  moveto data %o lineheight %o sub 2 div neg rmoveto show\n} def\n",diag,2 * diag;
        fprintf file,"/addlabel_cl {\n  /data exch def\n  moveto data dup stringwidth pop %o add neg lineheight %o sub 2 div neg rmoveto show\n} def\n",diag,2 * diag;
        fprintf file, "/Times-Roman findfont\n%o scalefont\nsetfont\n\n",
                                                                       fontsize;
    end if;
    // Output the command for drawing a lattice point
    fprintf file,"%%%%Lattice point output functions\n";
    if lattice eq "grid" then
        fprintf file, "/latticepoint {\n  %o 0 360 arc\n} def\n\n", diag;
        fprintf file, "/soildlatticepoint {\n  latticepoint gsave fill grestore stroke\n} def\n\n";
    else
        fprintf file, "/latticepoint {\n  moveto %o %o rmoveto %o %o rlineto\n",
                                    -diag, diag, 2 * diag, -2 * diag;
        fprintf file, "  %o %o rmoveto %o %o rlineto\n} def\n\n",
                                    0, 2 * diag, -2 * diag, -2 * diag;
        fprintf file, "/soildlatticepoint {\n  latticepoint\n} def\n\n";
    end if;
end procedure;

// Writes a [0..n] x [0..m] grid of lattice points to the given PS file.
procedure write_lattice(file,scale,n,m)
    fprintf file, "%%%%Draw the lattice points\ngsave\n  0.7 setgray\n";
    for i in [0..n] do
        for j in [0..m] do
            fprintf file, "  %o %o latticepoint stroke\n", i * scale, j * scale;
        end for;
    end for;
    fprintf file, "grestore\n\n";
end procedure;

// Writes a [0..n] x [0..m] grid to the given PS file.
procedure write_grid(file,scale,n,m)
    fprintf file, "%%%%Draw the lattice as a grid\ngsave\n  0.7 setgray\n  [3] 0 setdash\n";
    for i in [0..n] do
        fprintf file, "  %o 0 moveto 0 %o rlineto stroke\n", i * scale, m * scale;
    end for;
    for i in [0..m] do
        fprintf file, "  0 %o moveto %o 0 rlineto stroke\n", i * scale, n * scale;
    end for;
    fprintf file, "grestore\n\n";
end procedure;

// Returns a string representation of the given point.
function point_to_string(scale,v)
    v *:= scale;
    cs:=Eltseq(v);
    if IsIntegral(v) then
        str:=IntegerToString(Integers() ! cs[1]) cat " " cat
             IntegerToString(Integers() ! cs[2]);
    else
        if IsIntegral(cs[1]) then
            str:=IntegerToString(Integers() ! cs[1]) cat " ";
        else
            str:=Sprintf("%.5o ",1.0 * cs[1]);
        end if;
        if IsIntegral(cs[2]) then
            str cat:= IntegerToString(Integers() ! cs[2]) cat " ";
        else
            str cat:= Sprintf("%.5o",1.0 * cs[2]);
        end if;
    end if;
    return str;
end function;

// Writes the origin to the given PS file.
procedure write_origin(file,scale,orig)
    cs:=Eltseq(scale * orig);
    fprintf file, "%%%%Draw the origin\n%o %o latticepoint stroke\n\n",
                                    cs[1], cs[2];
end procedure;

// Writes the points to the given PS file.
procedure write_points(file,scale,u,pts)
    fprintf file,"%%%%Draw the points\n";
    if Type(pts) eq SetEnum or Type(pts) eq SeqEnum then
        for v in pts do
            cs:=Eltseq(scale * (v - u));
            fprintf file,"%o %o soildlatticepoint stroke\n",cs[1],cs[2];
        end for;
    end if;
    if Type(pts) eq Assoc then
        for v in Keys(pts) do
            cs:=Eltseq(scale * (v - u));
            t:=pts[v] select "soildlatticepoint" else "latticepoint";
            fprintf file,"%o %o %o stroke\n",cs[1],cs[2],t;
        end for;
    end if;
    fprintf file,"\n";
end procedure;

// Writes the edges of the polygon P to the given PS file.
procedure write_polygon(file,scale,P)
    verts:=Vertices(P);
    verts:=[verts[i + 1] : i in order_vertices(P,{1..#verts})];
    fprintf file, "%%%%Draw the polygon\nnewpath %o moveto",
                                    point_to_string(scale,verts[1]);
    for i in [2..#verts] do
        fprintf file, " %o lineto", point_to_string(scale,verts[i]);
    end for;
    fprintf file, " closepath stroke\n\n";
end procedure;

// Writes the point labels of the polygon P to the given PS file.
procedure write_point_labels(file,scale,min,P,point_labels)
    fprintf file,"%%%%Add the point labels\n";
    fprintf file,"gsave\n";
    if point_labels cmpeq true then
        point_labels:=AssociativeArray(Ambient(P));
        for v in Points(P) do
            vv:=Eltseq(v);
            point_labels[v]:=Sprintf("(%o,%o)",vv[1],vv[2]);
        end for;
    end if;
    for v in Keys(point_labels) do
        fprintf file,"  %o (%o) addlabel_tc\n", point_to_string(scale,v - min),
                                                                point_labels[v];
    end for;
    fprintf file,"grestore\n\n";
end procedure;

// Writes the vertex labels of the polygon P to the given PS file.
procedure write_vertex_labels(file,scale,min,P,vertex_labels)
    fprintf file,"%%%%Add the vertex labels\n";
    fprintf file,"gsave\n";
    verts:=Vertices(P);
    ineqs:=Inequalities(P);
    L:=Dual(Ambient(P));
    if vertex_labels cmpeq true then
        vertex_labels:=[];
        for v in verts do
            vv:=Eltseq(v);
            Append(~vertex_labels,Sprintf("(%o,%o)",vv[1],vv[2]));
        end for;
    end if;
    for i in [1..Min(#verts,#vertex_labels)] do
        if IsDefined(vertex_labels,i) then
            k:=verts[i] * L.2;
            sgns:={Sign(v * L.2 - k) : v in verts} diff {0};
            if #sgns eq 1 then
                sgn:=Representative(sgns);
                if sgn gt 0 then
                    cmd:="addlabel_bc";
                else
                    cmd:="addlabel_tc";
                end if;
            else
                k:=verts[i] * L.1;
                sgns:={Sign(v * L.1 - k) : v in verts} diff {0};
                if #sgns eq 1 then
                    sgn:=Representative(sgns);
                    if sgn gt 0 then
                        cmd:="addlabel_cl";
                    else
                        cmd:="addlabel_cr";
                    end if;
                else
                    ns:=[I[1] : I in ineqs | I[1] * verts[i] eq I[2]];
                    n:=Eltseq(&+[n : n in ns]);
                    c1:=n[2] gt 0 select "b" else "t";
                    c2:=n[1] gt 0 select "l" else "r";
                    cmd:="addlabel_" cat c1 cat c2;
                end if;
            end if;
            fprintf file,"  %o (%o) %o\n",
                   point_to_string(scale,verts[i] - min), vertex_labels[i], cmd;
        end if;
    end for;
    fprintf file,"grestore\n\n";
end procedure;

// Outputs the PS file's footers
procedure write_footer(file)
    fprintf file,"showpage\n";
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic WritePolytopeToPSFile( P::TorPol, F::MonStgElt : scale:=1,
    lattice:="points", padding:=0, vertex_labels:=false, point_labels:=false,
    fontsize:=9, mark_points:=false, mark_origin:=true )
{Writes the polygon P to a PostScript file F. Optional parameter 'lattice' can be used to select an output style for the lattice. Valid styles are "points", "grid", and "none".}
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
    require Type(vertex_labels) eq BoolElt or Type(vertex_labels) eq SeqEnum:
        "Parameter 'vertex_labels' should be a sequence of labels to assign to the vertices";
    require Type(point_labels) eq BoolElt or (Type(point_labels) eq Assoc and
            not IsNull(Keys(point_labels)) and
            Universe(Keys(point_labels)) cmpeq Ambient(P) and
            IsIntegral(Keys(point_labels))):
        "Parameter 'point_labels' should be a boolean, or an associative array whose keys are lattice points in the ambient lattice containing the polytope";
    require Type(mark_points) eq BoolElt or ((Type(mark_points) eq SetEnum or
            Type(mark_points) eq SeqEnum) and
            Universe(mark_points) cmpeq Ambient(P) and
            IsIntegral(mark_points)) or
            (Type(mark_points) eq Assoc and not IsNull(Keys(mark_points)) and
            Universe(Keys(mark_points)) cmpeq Ambient(P) and
            IsIntegral(Keys(mark_points)) and
            &and[Type(mark_points[v]) eq BoolElt : v in Keys(mark_points)]):
        "Parameter 'mark_points' should be a boolean, a set (or sequence) of lattice points in the ambient lattice containing the polytope, or an associative array whose keys are lattice points and whose values are booleans";
    require Type(fontsize) eq RngIntElt and fontsize gt 0:
        "Parameter 'fontsize' must be a positive integer";
    require Type(mark_origin) eq BoolElt:
        "Parameter 'mark_origin' must be a boolean";
    // Compute the scale
    scale:=Floor(13 * scale);
    // Compute the bounding box
    B,min,max:=bounding_box(P,point_labels,mark_points);
    min:=Parent(min) ! [Floor(c) : c in Eltseq(min)];
    max:=Parent(max) ! [Ceiling(c) : c in Eltseq(max)];
    n:=Eltseq(max)[1] - Eltseq(min)[1];
    m:=Eltseq(max)[2] - Eltseq(min)[2];
    // Open the file for writing
    F:=Open(F,"w");
    // Output the header
    textfuncs:=not vertex_labels cmpeq false or not point_labels cmpeq false;
    write_header(F,scale,lattice,n,m,padding,textfuncs,fontsize);
    // Output the lattice
    if lattice ne "none" then
        if lattice eq "points" then
            write_lattice(F,scale,n,m);
        elif lattice eq "grid" then
            write_grid(F,scale,n,m);
        end if;
    end if;
    // Indicate the origin
    if mark_origin and Zero(Ambient(B)) in B then
        write_origin(F,scale,-min);
    end if;
    // Mark the points
    if not mark_points cmpeq false then
        if Type(mark_points) eq BoolElt then mark_points:=Points(P); end if;
        write_points(F,scale,min,mark_points);
    end if;
    // Output the polygon
    write_polygon(F,scale,P - min);
    // Output the point labels
    if not point_labels cmpeq false then
        write_point_labels(F,scale,min,P,point_labels);
    end if;
    // Output the vertex labels
    if not vertex_labels cmpeq false then
        write_vertex_labels(F,scale,min,P,vertex_labels);
    end if;
    // Output the footer and close the file
    write_footer(F);
    delete F;
end intrinsic;
