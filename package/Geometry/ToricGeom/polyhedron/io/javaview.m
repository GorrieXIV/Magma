freeze;

/////////////////////////////////////////////////////////////////////////
// javaview.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 49968 $
// $Date: 2015-03-06 06:57:45 +1100 (Fri, 06 Mar 2015) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Output a polytope in jvx format for Javaview.
//  http://www.javaview.de/
// You can specify the path to the javaview script via the environment
// variable "JAVAVIEW_BIN". Otherwise it will be guessed from
// the "JAVAVIEW_HOME" environment variable.
/////////////////////////////////////////////////////////////////////////

import "../../utilities/functions.m": bounding_box;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns a temporary name derived from the given string. This is a workaround
// for a UNIX bug in Tempname.
function temp_name(P)
    return Tempname(P) cat IntegerToString(Random(100000));
end function;

// Returns the path to Javaview.
function get_javaview()
    path:=GetEnv("JAVAVIEW_BIN");
    if #path ne 0 then
        path:=Trim(path);
    end if;
    if #path eq 0 then
        path:=GetEnv("JAVAVIEW_HOME");
        if #path ne 0 then
            path:=Trim(path);
            if #path ne 0 then
                path cat:= "/bin/javaview";
            end if;
        end if;
    end if;
    return #path eq 0 select "javaview" else path;
end function;

// Generates the bounding box for the polytope (or sequence of polytopes).
function generate_boundingbox(S)
    if Type(S) eq TorPol then
        vertices:=[PowerSequence(Rationals()) | Eltseq(v) : v in Vertices(S)];
    else
        vertices:=&cat[[PowerSequence(Rationals()) | Eltseq(v) :
                                                  v in Vertices(P)] : P in S];
    end if;
    min,max:=bounding_box(vertices);
    return [Integers()|Floor(c) : c in min],[Integers()|Ceiling(c) : c in max];
end function;

// Returns the sequence of interior lattice points, and the exterior ones.
procedure partition_lattice_points_recursive(min,max,pt,S,~interior,~exterior)
    if #pt eq #min then
        if Type(S) eq TorPol then
            latpt:=Ambient(S) ! pt;
            if latpt in S then
                Append(~interior,pt);
            else
                Append(~exterior,pt);
            end if;
        else
            latpt:=Ambient(Representative(S)) ! pt;
            if &or[latpt in P : P in S] then
                Append(~interior,pt);
            else
                Append(~exterior,pt);
            end if;
        end if;
    else
        for i in [min[#pt + 1]..max[#pt + 1]] do
            $$(min,max,Append(pt,i),S,~interior,~exterior);
        end for;
    end if;
end procedure;

function partition_lattice_points(S)
    min,max:=generate_boundingbox(S);
    interior:=[PowerSequence(Integers())|];
    exterior:=[PowerSequence(Integers())|];
    for i in [min[1]..max[1]] do
        partition_lattice_points_recursive(min,max,[Integers() | i],
                                                         S,~interior,~exterior);
    end for;
    return interior,exterior,min,max;
end function;

// Returns the current date if possible, otherwise an empty string.
function get_date()
    try
        date:=Pipe("date && echo \"*\"","");
        idx:=Index(date,"*");
        if idx eq 0 then
            date:="";
        else
            date:=Trim(date[1..idx-1]);
        end if;
    catch e
        date:="";
    end try;
    return date;
end function;

// Returns the version string.
function get_version()
    return Sprintf("Magma V%o.%o-%o",a,b,c) where a,b,c:=GetVersion();
end function;

// Escapes the special XML characters in the string.
function escape_characters(str)
    str:=SubstituteString(str,"&","&amp;");
    str:=SubstituteString(str,"<","&lt;");
    str:=SubstituteString(str,">","&gt;");
    str:=SubstituteString(str,"\"","&quot;");
    str:=SubstituteString(str,"'","&apos;");
    return str;
end function;

// Outputs the header to the jvx file.
procedure write_header(file,title)
    fprintf file, "<?xml version=\"1.0\" encoding=\"ISO-8859-1\" standalone=\"no\"?>\n";
    fprintf file, "<!DOCTYPE jvx-model SYSTEM \"http://www.javaview.de/rsrc/jvx.dtd\">\n";
    fprintf file, "<jvx-model>\n\t<meta generator=\"%o\"/>\n", get_version();
    date:=get_date();
    if #date gt 0 then
        fprintf file, "\t<meta date=\"%o\"/>\n", date;
    end if;
   fprintf file, "\t<version type=\"final\">2.00</version>\n";
   title:=escape_characters(title);
   fprintf file, "\t<title>%o</title>\n\t<geometries>\n", title;
end procedure;

// Outputs the footer to the jvx file.
procedure write_footer(file)
    fprintf file, "\t</geometries>\n</jvx-model>\n";
end procedure;

// Returns the point in string format.
function point_to_string(v)
    // Convert the point to a string
    str:="";
    for c in Eltseq(v) do
        if IsIntegral(c) then
            str cat:= IntegerToString(Integers() ! c) cat " ";
        else
            str cat:= Sprintf("%o ",RealField(10) ! c);
        end if;
    end for;
    // Return the string
    return str[1..#str - 1];
end function;

// Outputs the lattice point to the jvx file.
procedure write_point(file,pt)
    fprintf file, "\t\t\t\t\t<p>%o</p>\n",point_to_string(pt);
end procedure;

// Given a set of vertex indices, returns the vertex indices in order. Also
// subtracts 1 from the indicies (so that they're indexed from 0).
function order_vertices(P,facetidxs)
    edgeidxs:=[edge : edge in EdgeIndices(P) | edge subset facetidxs];
    facetidxs:=Sort(SetToSequence(facetidxs));
    idx:=facetidxs[1];
    Remove(~facetidxs,1);
    orderedidxs:=[Integers() | idx - 1];
    while #facetidxs gt 1 do
        found:=0;
        for i in [1..#edgeidxs] do
            if idx in edgeidxs[i] then
                found:=i;
                break;
            end if;
        end for;
        idx:=Representative(Exclude(edgeidxs[found],idx));
        Remove(~edgeidxs,found);
        Remove(~facetidxs,Index(facetidxs,idx));
        Append(~orderedidxs,idx - 1);
    end while;
    Append(~orderedidxs,facetidxs[1] - 1);
    return orderedidxs;
end function;

// Outputs the indicated facet to the jvx file.
procedure write_facet(file,idxs,P)
    idxs:=order_vertices(P,idxs);
    str:="";
    for i in idxs do str cat:= IntegerToString(i) cat " "; end for;
    fprintf file, "\t\t\t\t\t<f>%o</f>\n",str;
end procedure;

// Outputs the polytope to the jvx file.
procedure write_polytope(file,P,name)
    // Open the geometry tag
    fprintf file, "\t\t<geometry name=\"%o\">\n",name;
    // Output the points
    if not IsEmpty(P) then
        dim:=Dimension(Ambient(P));
        fprintf file, "\t\t\t<pointSet dim=\"%o\" point=\"show\">\n", dim;
        fprintf file, "\t\t\t\t<points num=\"%o\">\n", NumberOfVertices(P);
        for pt in Vertices(P) do
            write_point(file,pt);
        end for;
        fprintf file, "\t\t\t\t</points>\n\t\t\t</pointSet>\n";
    end if;
    // Output the edges if appropriate
    if Dimension(P) gt 0 and Dimension(P) le 2 then
        fprintf file, "\t\t\t<lineSet line=\"show\">\n";
        fprintf file, "\t\t\t\t<lines num=\"%o\">\n", NumberOfEdges(P);
        for idxs in EdgeIndices(P) do
            str:="";
            for i in idxs do str cat:= IntegerToString(i - 1) cat " "; end for;
            fprintf file, "\t\t\t\t\t<l>%o</l>\n",str;
        end for;
        fprintf file, "\t\t\t\t</lines>\n\t\t\t</lineSet>\n";
    // Or the faces if P is three-dimensional
    elif Dimension(P) eq 3 then
        fprintf file, "\t\t\t<faceSet face=\"hide\" edge=\"show\">\n";
        fprintf file, "\t\t\t\t<faces num=\"%o\">\n", NumberOfFacets(P);
        for idxs in FacetIndices(P) do write_facet(file,idxs,P); end for;
        fprintf file, "\t\t\t\t</faces>\n\t\t\t</faceSet>\n";
    end if;
    // Finally close the geometry tag
    fprintf file, "\t\t</geometry>\n";
end procedure;

// Outputs the lattice to the jvx file.
procedure write_lattice(file,S)
    // Collect the points
    interior,exterior,min,max:=partition_lattice_points(S);
    // Output the interior points
    if #interior ne 0 then
        fprintf file, "\t\t<geometry name=\"Interior lattice points\">\n";
        fprintf file, "\t\t\t<pointSet dim=\"%o\" point=\"show\">\n", #min;
        fprintf file, "\t\t\t\t<points num=\"%o\">\n", #interior;
        for pt in interior do
            write_point(file,pt);
        end for;
        fprintf file, "\t\t\t\t\t<thickness>0.75</thickness>\n";
        fprintf file, "\t\t\t\t\t<color type=\"rgb\">0 0 255</color>\n";
        fprintf file, "\t\t\t\t</points>\n\t\t\t</pointSet>\n";
        fprintf file, "\t\t</geometry>\n";
    end if;
    // Output the exterior points
    if #exterior ne 0 then
        fprintf file, "\t\t<geometry name=\"Exterior lattice points\">\n";
        fprintf file, "\t\t\t<pointSet dim=\"%o\" point=\"show\">\n", #min;
        fprintf file, "\t\t\t\t<points num=\"%o\">\n", #exterior;
        for pt in exterior do
            write_point(file,pt);
        end for;
        fprintf file, "\t\t\t\t\t<thickness>0.75</thickness>\n";
        fprintf file, "\t\t\t\t\t<color type=\"rgb\">0 255 0</color>\n";
        fprintf file, "\t\t\t\t</points>\n\t\t\t</pointSet>\n";
        fprintf file, "\t\t</geometry>\n";
    end if;
    // Now we mark the origin if it's in the lattice
    if &and[min[i] le 0 and max[i] ge 0 : i in [1..#min]] then
        if Type(S) eq TorPol then
            contained:=Zero(Ambient(S)) in S;
        else
            zero:=Zero(Ambient(Representative(S)));
            contained:=&or[zero in P : P in S];
        end if;
        fprintf file, "\t\t<geometry name=\"origin\">\n";
        fprintf file, "\t\t\t<pointSet dim=\"%o\" point=\"show\">\n", #min;
        fprintf file, "\t\t\t\t<points num=\"1\">\n";
        write_point(file,ZeroSequence(Integers(),#min));
        if contained then
            fprintf file, "\t\t\t\t\t<color type=\"rgb\">0 0 255</color>\n";
        else
            fprintf file, "\t\t\t\t\t<color type=\"rgb\">0 255 0</color>\n";
        end if;
        fprintf file, "\t\t\t\t</points>\n\t\t\t</pointSet>\n";
        fprintf file, "\t\t</geometry>\n";
    end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic ViewWithJavaview( P::TorPol :
                            path:=get_javaview(),
                            drawLattice:=true,
                            title:="Polytope",
                            open_in_background:=false )
{View the polytope P using Javaview. The dimension of the ambient lattice must be at most three.}
    // Sanity checks
    require IsPolytope(P) and not IsEmpty(P):
        "The polyhedron must be a non-empty polytope";
    require Dimension(Ambient(P)) le 3:
        "The ambient lattice must be at most three-dimensional";
    require not InternalIsPC(): "Operation not supported on Windows";
    require Type(drawLattice) eq BoolElt:
        "Parameter 'drawLattice' must be a boolean";
    require Type(title) eq MonStgElt:
        "Parameter 'title' must be a string";
    require Type(path) eq MonStgElt: "Parameter 'path' must be a string";
    require Type(open_in_background) eq BoolElt:
        "Parameter 'open_in_background' must be a boolean";
    // First create the temporary file
    F:=GetTempDir() cat "/magma." cat temp_name("javaview") cat ".jvx";
    WritePolytopeToJVX(P,F : drawLattice:=drawLattice, title:=title);
    // Open it with Javaview
    if open_in_background then
        // Launch Javaview using nohup
        cmd:="nohup " cat path cat " " cat F cat " &>/dev/null &";
        try
            res:=Pipe(cmd,"");
        catch e
            res:="FAILED";
        end try;
    else
        // Launch Javaview
        cmd:=path cat " " cat F cat " 2>&1 || echo \"FAILED\"";
        try
            res:=Pipe(cmd,"");
        catch e
            res:="FAILED";
        end try;
        // Remove the file
        try
            _:=Pipe("rm -f " cat F cat " > /dev/null 2>&1","");
        catch e;
        end try;
    end if;
    // Do we need to throw an error? Is there a message?
    require Index(res,"FAILED") eq 0:
        "Unable to send polytope to Javaview.\n(Using path: " cat path cat ")";
    if #res ne 0 then printf "%o: %o\n",path,Trim(res); end if;
end intrinsic;

intrinsic ViewWithJavaview( S::SeqEnum[TorPol] :
                            path:=get_javaview(),
                            drawLattice:=true,
                            title:="Polytopes",
                            open_in_background:=false )
{View the sequence of polytopes S using Javaview. The polytopes in S must lie in the same ambient lattice. The dimension of the ambient lattice must be at most three.}
    // Sanity checks
    require #S ne 0: "The sequence must not be empty";
    require &and[IsPolytope(P) and not IsEmpty(P) : P in S]:
        "The polyhedra must all be non-empty polytopes";
    L:=Ambient(Representative(S));
    require &and[Ambient(P) eq L : P in S]:
        "The polytopes must be contained in the same ambient lattice";
    require Dimension(L) le 3:
        "The ambient lattice must be at most three-dimensional";
    require not InternalIsPC(): "Operation not supported on Windows";
    require Type(drawLattice) eq BoolElt:
        "Parameter 'drawLattice' must be a boolean";
    require Type(title) eq MonStgElt:
        "Parameter 'title' must be a string";
    require Type(path) eq MonStgElt: "Parameter 'path' must be a string";
    require Type(open_in_background) eq BoolElt:
        "Parameter 'open_in_background' must be a boolean";
    // First create the temporary file
    F:=GetTempDir() cat "/magma." cat temp_name("javaview") cat ".jvx";
    WritePolytopesToJVX(S,F : drawLattice:=drawLattice, title:=title);
    // Open it with Javaview
    try
        res:=Pipe(path cat " " cat F cat " 2>&1 || echo \"FAILED\"","");
    catch e
        res:="FAILED";
    end try;
    // Remove the file
    try
        _:=Pipe("rm -f " cat F cat " > /dev/null 2>&1","");
    catch e;
    end try;
    // Do we need to throw an error? Is there a message?
    require Index(res,"FAILED") eq 0:
        "Unable to send polytopes to Javaview.\n(Using path: " cat path cat ")";
    if #res ne 0 then printf "%o: %o\n",path,Trim(res); end if;
end intrinsic;

intrinsic WritePolytopeToJVX( P::TorPol, F::MonStgElt :
    drawLattice:=true, title:="Polytope" )
{Writes the polytope P to the file F in Javaview's jvx format. The dimension of the ambient lattice must be at most three.}
    // Sanity checks
    require IsPolytope(P) and not IsEmpty(P):
        "The polyhedron must be a non-empty polytope";
    require Dimension(Ambient(P)) le 3:
        "The ambient lattice must be at most three-dimensional";
    require Type(drawLattice) eq BoolElt:
        "Parameter 'drawLattice' must be a boolean";
    require Type(title) eq MonStgElt: "Parameter 'title' must be a string";
    // Open the file for writing
    F:=Open(F,"w");
    // Output the header
    write_header(F,title);
    // Output the lattice
    if drawLattice eq true then
        write_lattice(F,P);
    end if;
    // Output the polytope
    write_polytope(F,P,"Polytope");
    // Output the footer and close the file
    write_footer(F);
    delete F;
end intrinsic;

intrinsic WritePolytopesToJVX( S::SeqEnum[TorPol], F::MonStgElt :
    drawLattice:=true, title:="Polytopes" )
{Writes the sequence of polytope S to the file F in Javaview's jvx format. The polytopes in S must lie in the same ambient lattice. The dimension of the ambient lattice must be at most three.}
    // Sanity checks
    require #S ne 0: "The sequence must not be empty";
    require &and[IsPolytope(P) and not IsEmpty(P) : P in S]:
        "The polyhedra must all be non-empty polytopes";
    L:=Ambient(Representative(S));
    require &and[Ambient(P) eq L : P in S]:
        "The polytopes must be contained in the same ambient lattice";
    require Dimension(L) le 3:
        "The ambient lattice must be at most three-dimensional";
    require Type(drawLattice) eq BoolElt:
        "Parameter 'drawLattice' must be a boolean";
    require Type(title) eq MonStgElt: "Parameter 'title' must be a string";
    // Open the file for writing
    F:=Open(F,"w");
    // Output the header
    write_header(F,title);
    // Output the lattice
    if drawLattice eq true then
         write_lattice(F,S);
    end if;
    // Output the polytopes
    for i in [1..#S] do
        write_polytope(F,S[i],"Polytope " cat IntegerToString(i));
    end for;
    // Output the footer and close the file
    write_footer(F);
    delete F;
end intrinsic;
