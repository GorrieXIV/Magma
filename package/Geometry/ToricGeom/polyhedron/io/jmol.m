freeze;

/////////////////////////////////////////////////////////////////////////
// jmol.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 49968 $
// $Date: 2015-03-06 06:57:45 +1100 (Fri, 06 Mar 2015) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Output a polytope ready for viewing with jmol.
//  http://jmol.sourceforge.net/
// You can specify the path to the jmol script via the environment
// variable "JMOL_BIN".
/////////////////////////////////////////////////////////////////////////

import "javaview.m": temp_name, get_date, get_version, order_vertices;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns the path to jmol.
function get_jmol()
    path:=GetEnv("JMOL_BIN");
    if #path ne 0 then
        path:=Trim(path);
    end if;
    return #path eq 0 select "jmol" else path;
end function;

// Creates a temporary directory. Returns true followed by the directory path
// on success, false followed by an error message otherwise.
function create_temp_dir()
    dir:=GetTempDir() cat "/magma." cat temp_name("jmol") cat "/";
    try
        res:=Pipe("mkdir " cat dir cat " 2>&1 || echo \"FAILED\"","");
    catch e
        res:="FAILED";
    end try;
    if Index(res,"FAILED") eq 0 then
        return true,dir;
    else
        return false,"Unable to create temporary working directory";
    end if;
end function;

// Attempts to delete the given directory and its contents. If this fails,
// it fails silently.
procedure delete_temp_dir(dir)
    try
        _:=Pipe("rm " cat dir cat "* && rmdir " cat dir cat " 2>&1","");
    catch e;
    end try;
end procedure;

// Escapes and quotes the file name, making it safe for use in pipes.
function escape_filename(file)
    file:=SubstituteString(file,"\\","\\\\");
    file:=SubstituteString(file,"\"","\\\"");
    file:=SubstituteString(file,"$","\\\$");
    if file[1] eq "~" and file[2] eq "/" then
        file:="~/\"" cat file[3..#file] cat "\"";
    else
        file:="\"" cat file cat "\"";
    end if;
    return file;
end function;

// Zips the given directory. Returns true followed by the path to the zip
// archive on success, false with an error message otherwise.
function create_zip(dir)
    // Create the temporary archive name
    file:=dir[1..#dir - 1] cat ".zip";
    // Create the zip file
    cmd:="zip -jrq " cat file cat " " cat dir cat " 2>&1 || echo \"FAILED\"";
    try
        res:=Pipe(cmd,"");
    catch e
        res:="FAILED";
    end try;
    if Index(res,"FAILED") ne 0 then
        return false,"Unable to create zip archive";
    end if;
    // Return success
    return true,file;
end function;

// Moves the zip file into position. Returns true followed by the escaped and
// quoted path on success, false with an error message otherwise.
function move_zip(src,archive)
    // Escape the archive name
    archive:=escape_filename(archive);
    // Move the zip file into position
    cmd:="mv " cat src cat " " cat archive cat " 2>&1 || echo \"FAILED\"";
    try
        res:=Pipe(cmd,"");
    catch e
        res:="FAILED";
    end try;
    if Index(res,"FAILED") ne 0 then
        try
            _:=Pipe("rm " cat src cat " 2>&1","");
        catch e;
        end try;
        return false,"Unable to create zip archive";
    end if;
    // Return success
    return true,archive;
end function;

// Returns true iff the given argument can be interpreted as a colour.
function is_colour(val)
    if Type(val) eq SeqEnum and #val eq 3 then
        if Universe(val) cmpeq Integers() then
            return &and[c ge 0 and c le 255 : c in val];
        end if;
        bool,res:=CanChangeUniverse(val,RealField(10));
        if bool then
            return &and[c ge 0 and c le 1 : c in res];
        end if;
    elif Type(val) eq MonStgElt then
        names:={"fuchsia","purple","blue","navy","aqua","teal","lime","green",
                "yellow","olive","red","maroon","white","silver","gray",
                "grey","black"};
        if val in names then return true; end if;
        hex:={"0","1","2","3","4","5","6","7","8","9","a","A","b","B","c","C",
              "d","D","e","E","f","F"};
        if #val eq 7 then
            return val[1] eq "x" and &and[val[i] in hex : i in [2..7]];
        elif #val eq 6 then
            return &and[val[i] in hex : i in [1..6]];
        end if;
    end if;
    // If we're here then it's not a valid colour description
    return false;
end function;

// Returns a string description of the given colour.
function colour_to_string(val)
    if Type(val) eq SeqEnum and #val eq 3 then
        if Universe(val) cmpeq Integers() then
            return Sprintf("[%o, %o, %o]",val[1],val[2],val[3]);
        else
            return Sprintf("{%o, %o, %o}",RealField(10) ! val[1],
                                 RealField(10) ! val[2],RealField(10) ! val[3]);
        end if;
    elif Type(val) eq MonStgElt then
        names:=["fuchsia","purple","blue","navy","aqua","teal",
                "lime","green","yellow","olive","red","maroon",
                "white","silver","gray","grey","black"];
        if val in names then
            hex:=["FF00FF","800080","0000FF","000080","00FFFF","008080",
                  "00FF00","008000","FFFF00","808000","FF0000","800000",
                  "FFFFFF","C0C0C0","808080","808080","000000"];
            return "[x" cat hex[Index(names,val)] cat "]";
        end if;
        if #val eq 7 then
            return "[" cat val cat "]";
        elif #val eq 6 then
            return "[x" cat val cat "]";
        end if;
    end if;
    // We should never get here
    error Sprintf("Illegal colour: %o",val);
end function;

// Returns true iff the given argument can be interpreted as a transparency.
function is_transparency(val)
    if Type(val) eq RngIntElt then
        return val in {0..6} join {32,64,96,128,160,192};
    elif Type(val) eq FldReElt then
        return val in {0.0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75};
    end if;
    // If we're here then it's not a valid transparency description
    return false;
end function;

// Returns a string description of the given transparency.
function transparency_to_string(val)
    if Type(val) eq RngIntElt then
        case val:
            when 0:
                return "OPAQUE";
            when 1:
                return "TRANSLUCENT 0.125";
            when 2:
                return "TRANSLUCENT 0.25";
            when 3:
                return "TRANSLUCENT 0.375";
            when 4:
                return "TRANSLUCENT 0.5";
            when 5:
                return "TRANSLUCENT 0.625";
            when 6:
                return "TRANSLUCENT 0.75";
            when 32:
                return "TRANSLUCENT 0.125";
            when 64:
                return "TRANSLUCENT 0.25";
            when 96:
                return "TRANSLUCENT 0.375";
            when 128:
                return "TRANSLUCENT 0.5";
            when 160:
                return "TRANSLUCENT 0.625";
            when 192:
                return "TRANSLUCENT 0.75";
        end case;
    elif Type(val) eq FldReElt then
        case val:
            when 0:
                return "OPAQUE";
            when 0.125:
                return "TRANSLUCENT 0.125";
            when 0.25:
                return "TRANSLUCENT 0.25";
            when 0.375:
                return "TRANSLUCENT 0.375";
            when 0.5:
                return "TRANSLUCENT 0.5";
            when 0.625:
                return "TRANSLUCENT 0.625";
            when 0.75:
                return "TRANSLUCENT 0.75";
        end case;
    end if;
    // We should never get here
    error Sprintf("Illegal transparency: %o",val);
end function;

// Returns true iff the given argument can be interpreted as a diameter.
function is_diameter(val)
    return Type(val) eq RngIntElt and val ge 0;
end function;

// Validates the parameters. Returns true if they're ok, false followed by an
// error message otherwise.
function validate_parameters(background,transparency,
                             face_color,edge_color,edge_width,
                             point_color,point_size,point_labels,
                             vertex_color,vertex_size,vertex_labels)
    // First check the colour values
    err:="Parameter '%o' should be false to disable drawing of the %o, or a red-green-blue colour in the form of a sequence of three integers in the range [0..255] (e.g. [128, 0, 255]), three rational or floating point values in the range [0..1] (e.g. [1/2, 0, 1] or [0.5, 0.0, 1.0]), a string representing a hexidecimal value (e.g. \"x8800FF\" or \"8800FF\"), or one of the 16 named VGA colours (\"lime\", \"olive\", \"red\", etc.).";
    if not (background cmpeq false or is_colour(background)) then
        return false,Sprintf(err,"background","background");
    end if;
    if not (face_color cmpeq false or is_colour(face_color)) then
        return false,Sprintf(err,"face_color","face");
    end if;
    if not (edge_color cmpeq false or is_colour(edge_color)) then
        return false,Sprintf(err,"edge_color","edges");
    end if;
    if not (point_color cmpeq false or is_colour(point_color)) then
        return false,Sprintf(err,"point_color","points");
    end if;
    if not (vertex_color cmpeq false or is_colour(vertex_color)) then
        return false,Sprintf(err,"vertex_color","vertices");
    end if;
    // Now check the transparency values
    err:="Parameter '%o' should take one of the following values: 0 (opaque), 0.125 (or 1 or 32), 0.25 (or 2 or 64), 0.375 (or 3 or 96), 0.5 (or 4 or 128), 0.625 (or 5 or 160), or 0.75 (or 6 or 192). Larger numbers are more translucent.";
    if not is_transparency(transparency) then
        return false,Sprintf(err,"transparency");
    end if;
    // Now check the diameters
    err:="Parameter '%o' should be 0 to disable drawing of the %o, or a positive integer.";
    if not is_diameter(edge_width) then
        return false,Sprintf(err,"edge_width","edges");
    end if;
    if not is_diameter(point_size) then
        return false,Sprintf(err,"point_size","points");
    end if;
    if not is_diameter(vertex_size) then
        return false,Sprintf(err,"vertex_size","vertices");
    end if;
    // Now check the labels
    if not (vertex_labels cmpeq false) and not (point_labels cmpeq false) then
    	return false,"Parameters 'vertex_labels' and 'point_labels' should not be assigned at the same time: choose one or the other.";
    end if;
    if not (Type(vertex_labels) eq BoolElt or Type(vertex_labels) eq SeqEnum) then
        return false,"Parameter 'vertex_labels' should be a sequence of labels to assign to the vertices.";
    end if;
    if not (Type(point_labels) eq BoolElt or Type(point_labels) eq SeqEnum) then
        return false,"Parameter 'point_labels' should be a sequence of labels to assign to the points. The points of the polytope P will be ordered by Sort(SetToSequence(Points(P))).";
    end if;
    // If we're here then it looks OK
    return true,_;
end function;

// Returns the point in string format.
function point_to_string(v)
    // Ensure that the point is in a three-dimensional ambient space
    v:=Eltseq(v);
    if #v lt 3 then
        v cat:= ZeroSequence(Universe(v),3 - #v);
    end if;
    // Convert the point to a string
    str:="";
    for c in v do
        if IsIntegral(c) then
            str cat:= IntegerToString(Integers() ! c) cat " ";
        else
            str cat:= Sprintf("%o ",RealField(10) ! c);
        end if;
    end for;
    // Return the string
    return str[1..#str - 1];
end function;

// Outputs the vertices to the pmesh file.
procedure output_vertices_to_pmesh(file,P)
    // Add the number of vertices
    str:=IntegerToString(NumberOfVertices(P)) cat "\n";
    // Add the vertices
    for v in Vertices(P) do
        str cat:= point_to_string(v) cat "\n";
    end for;
    // Output the string
    fprintf file,str;
end procedure;

// Returns the given face in string format ready for the pmesh file. Note that
// pmesh only supports triangles and quadrilaterals; if the face has more that
// five vertces we triangulate it. The second return value will indicate how
// many faces were necessary.
function face_to_string(P,idxs)
    // If there are three vertices, this is easy
    if #idxs eq 3 then
        num:=1;
        str:="4\n";
        idxs:=Sort(SetToSequence(idxs));
        Append(~idxs,idxs[1]);
        for i in idxs do str cat:= IntegerToString(i - 1) cat "\n"; end for;
    // If there are 4 vertices then we need to output them in the correct order
    elif #idxs eq 4 then
        num:=1;
        str:="5\n";
        idxs:=order_vertices(P,idxs);
        Append(~idxs,idxs[1]);
        for i in idxs do str cat:= IntegerToString(i) cat "\n"; end for;
    // Otherwise we need to output the face in groups of 3 or 4 vertices
    else
        num:=0;
        str:="";
        idxs:=order_vertices(P,idxs);
        while (#idxs mod 4) ne 0 do
            num +:= 1;
            str cat:= "4\n";
            for i in [1,2,3,1] do
                str cat:= IntegerToString(idxs[i]) cat "\n";
            end for;
            idxs:=[Integers() | idxs[1]] cat idxs[3..#idxs];
        end while;
        while #idxs ge 4 do
            num +:= 1;
            str cat:= "5\n";
            for i in [1,2,3,4,1] do
                str cat:= IntegerToString(idxs[i]) cat "\n";
            end for;
            idxs:=[Integers() | idxs[1]] cat idxs[4..#idxs];
        end while;
    end if;
    // Return the string and the number of faces required
    return str,num;
end function;

// Outputs the faces to the pmesh file.
procedure output_faces_to_pmesh(file,P)
    // First we build the string description and count the number of faces
    num:=0;
    str:="";
    for idxs in FacetIndices(P) do
        fstr,fnum:=face_to_string(P,idxs);
        num +:= fnum;
        str cat:= fstr;
    end for;
    // Output the string
    fprintf file,IntegerToString(num) cat "\n" cat str;
end procedure;

// Outputs the polygon as a face to the pmesh file.
procedure output_polygon_to_pmesh(file,P)
    str,num:=face_to_string(P,{1..NumberOfVertices(P)});
    fprintf file,IntegerToString(num) cat "\n" cat str;
end procedure;

// Outputs the given polytope's data to the given pmesh file.
procedure output_pmesh(file,P)
    // Output the vertices
    output_vertices_to_pmesh(file,P);
    // If this is a three-dimensional polytope, output the faces
    if Dimension(P) eq 3 then
        output_faces_to_pmesh(file,P);
    // If this is a two-dimensional polytope, add the whole polygon as a face
    elif Dimension(P) eq 2 then
        output_polygon_to_pmesh(file,P);
    end if;
end procedure;

// Outputs the commands to include the pmesh file in the given script file.
procedure include_pmesh(file,pmesh_name,transparency,rgb)
    str:="";
    if not rgb cmpeq false then
        // The commands
        commands:=[
            Sprintf("isosurface ID \"%o\" PMESH \"$SCRIPT_PATH$/%o.pmesh\"",
                                                        pmesh_name, pmesh_name),
            Sprintf("isosurface ID \"%o\" FULLYLIT", pmesh_name),
            Sprintf("color $%o %o %o", pmesh_name,
                  transparency_to_string(transparency), colour_to_string(rgb))];
        // Create the string
        for cmd in commands do str cat:= "  " cat cmd cat ";\n"; end for;
    end if;
    // Output the string
    fprintf file,"function _drawFaces() {\n%o}\n\n",str;
end procedure;

// Returns the given edge in string format ready for the script file.
function edge_to_string(P,idx,diameter,rgb)
    // Assign a name to this edge
    name:="edge" cat IntegerToString(idx);
    // Recover the edge indices
    edge:=SetToSequence(EdgeIndices(P)[idx]);
    verts:=Vertices(P);
    // Create the string
    str:=Sprintf("  draw ID \"%o\" diameter %o curve {%o} {%o};\n",
                            name, diameter, point_to_string(verts[edge[1]]),
                            point_to_string((verts[edge[2]])));
    str cat:= Sprintf("  color $%o %o;\n", name, colour_to_string(rgb));
    // Return the string
    return str;
end function;

// Outputs the edges to the given script file.
procedure output_edges(file,P,diameter,rgb)
    str:="";
    if not (diameter eq 0 or rgb cmpeq false) then
        for i in [1..NumberOfEdges(P)] do
            str cat:= edge_to_string(P,i,diameter,rgb);
        end for;
    end if;
    fprintf file,"function _drawEdges() {\n%o}\n\n",str;
end procedure;

// Returns a string description of the given points for the script file.
function points_to_string(pts,labels,tag,diameter,rgb)
    // Create the string
    str:="";
    for i in [1..#pts] do
        pt:=point_to_string(pts[i]);
        name:=tag cat IntegerToString(i);
        if Type(labels) eq SeqEnum and IsDefined(labels,i) then
            if Type(labels[i]) eq MonStgElt then
                label:=labels[i];
            else
                label:=Sprintf("%o",labels[i]);
            end if;
            label:=SubstituteString(label,"\"","\\\"");
            str cat:= Sprintf("  draw ID \"%o\" diameter %o \"%o\" {%o};\n",
                                                     name, diameter, label, pt);
        else
            str cat:= Sprintf("  draw ID \"%o\" diameter %o {%o};\n",
                                                            name, diameter, pt);
        end if;
        str cat:= Sprintf("  color $%o %o;\n", name, colour_to_string(rgb));
    end for;
    // Return the string
    return str;
end function;

// Outputs the points to the given script file.
procedure output_points(file,P,labels,diameter,rgb)
    if diameter eq 0 or rgb cmpeq false then
        str:="";
    else
        pts:=Sort(SetToSequence(Points(P)));
    	if labels cmpeq true then labels:=pts; end if;
        str:=points_to_string(pts,labels,"point",diameter,rgb);
    end if;
    fprintf file,"function _drawPoints() {\n%o}\n\n",str;
end procedure;

// Outputs the vertices to the given script file.
procedure output_vertices(file,P,labels,diameter,rgb)
    if diameter eq 0 or rgb cmpeq false then
        str:="";
    else
        pts:=Vertices(P);
    	if labels cmpeq true then labels:=pts; end if;
        str:=points_to_string(pts,labels,"vertex",diameter,rgb);
    end if;
    fprintf file,"function _drawVertices() {\n%o}\n\n",str;
end procedure;

// Outputs the model list to the given script file.
procedure output_model_list(file,P)
    // Open the model list
    str:="  load data \"model list\"\n" cat IntegerToString(NumberOfPoints(P))
         cat "\nempty\n";
    // Add the vertices
    for v in Vertices(P) do
        str cat:= "Xx " cat point_to_string(v) cat "\n";
    end for;
    // Add the remaining points
    for v in Points(P) diff SequenceToSet(Vertices(P)) do
        str cat:= "Xx " cat point_to_string(v) cat "\n";
    end for;
    // Close the model list
    str cat:= "  end \"model list\";\n";
    // Output the string
    fprintf file,"function _loadModel() {\n%o}\n\n",str;
end procedure;

// Outputs the view data to the given script file.
procedure output_view_data(file,axis,angle,rgb)
    // The commands
    commands:=[
        "show data",
        "select *",
        "wireframe off",
        "spacefill off",
        "set labelOffset 0 3",
        "spin off",
        Sprintf("moveto 0 %o %o %o %o",axis[1],axis[2],axis[3],RealField(5)!angle),
        "centerAt absolute {0 0 0}",
        "zoom 100",
        "frank off",
        "set perspectivedepth true",
        "set specular on" ];
    if not rgb cmpeq false then
        Append(~commands,Sprintf("background %o",colour_to_string(rgb)));
    end if;
    // Output the string
    str:="";
    for cmd in commands do str cat:= "  " cat cmd cat ";\n"; end for;
    fprintf file,"function _setViewData() {\n%o}\n\n",str;
end procedure;

// Outputs the header to the given script file.
procedure output_header(file)
    fprintf file, "# Jmol state\n";
    date:=get_date();
    if date ne "" then fprintf file, "# Created %o\n",date; end if;
    fprintf file, "# %o\n\n",get_version();
end procedure;

// Outputs the footer to the given script file.
procedure output_footer(file,title)
    // The commands
    commands:=[
        "initialize",
        "set refreshing false",
        "_loadModel",
        "_setViewData",
        "_drawFaces",
        "_drawEdges",
        "_drawPoints",
        "_drawVertices",
        "set refreshing true",
        "set antialiasDisplay true",
        "set antialiasTranslucent true",
        "set antialiasImages true" ];
    if title ne "" then
        Append(~commands,Sprintf("frame TITLE \"%o\"",title));
    end if;
    // Output the string
    str:="";
    for cmd in commands do str cat:= "  " cat cmd cat ";\n"; end for;
    fprintf file,"function _drawPolytope() {\n%o}\n\n_drawPolytope;\n",str;
end procedure;

// Outputs the manifest file.
procedure output_manifest(file,script)
    fprintf file, "# Jmol Manifest Zip Format 1.0\n%o\n",script;
end procedure;

// Returns the axis and angle to move the polytope to. In other words, the
// polytope will be rotated "angle" degrees clockwise around "axis".
function create_view_angle(P)
    if Dimension(P) eq 3 then
        return [-764,-346,-545],76.39;
    else
        return [0,0,0],0;
    end if;
end function;

// Outputs the script and pmesh file for the given polytope into the given
// directory.
procedure output_script_and_pmesh(dir,P,title,background,transparency,
                                        face_color,edge_color,edge_width,
                                        point_color,point_size,point_labels,
                                        vertex_color,vertex_size,vertex_labels,
                                        axis,angle);
    // Create the file names
    pmesh:=dir cat "polytope1.pmesh";
    script:=dir cat "main.spt";
    manifest:=dir cat "JmolManifest.txt";
    // Output the pmesh file
    F:=Open(pmesh,"w");
    output_pmesh(F,P);
    delete F;
    // Output the header
    F:=Open(script,"w");
    output_header(F);
    // Output the model list
    output_model_list(F,P);
    // Output the view commands
    output_view_data(F,axis,angle,background);
    // Include the pmesh file
    include_pmesh(F,"polytope1",transparency,face_color);
    // Output the edges
    output_edges(F,P,edge_width,edge_color);
    // Output the points and (possible) labels
    output_points(F,P,point_labels,point_size,point_color);
    // Output the vertices and (possible) labels
    output_vertices(F,P,vertex_labels,vertex_size,vertex_color);
    // Output the footer
    output_footer(F,title);
    delete F;
    // Output the manifest file
    F:=Open(manifest,"w");
    output_manifest(F,"main.spt");
    delete F;
end procedure;

// Creates a zip archive of the jmol files for the given polytope. Returns true
// followed by the path to the archive on success, false followed by an
// error message otherwise.
function create_jmol_archive(P,title,background,transparency,
                               face_color,edge_color,edge_width,
                               point_color,point_size,point_labels,
                               vertex_color,vertex_size,vertex_labels);
    // Choose the axis and angle to move the polytope to
    axis,angle:=create_view_angle(P);
    // Create the temporary directory
    success,dir:=create_temp_dir();
    if not success then return false,dir; end if;
    // Create the script and pmesh file
    output_script_and_pmesh(dir,P,title,background,transparency,
                                  face_color,edge_color,edge_width,
                                  point_color,point_size,point_labels,
                                  vertex_color,vertex_size,vertex_labels,
                                  axis,angle);
    // Create the zip archive
    success,path:=create_zip(dir);
    // Delete the temporary directory
    delete_temp_dir(dir);
    // Return success
    return success,path;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic ViewWithJmol( P::TorPol :
                        path:=get_jmol(),
                        title:="",
                        background:=[255,255,255],
                        transparency:=4,
                        face_color:=[255,215,0],
                        edge_color:=[50,50,50],
                        edge_width:=3,
                        point_color:=[255,0,0],
                        point_size:=10,
                        point_labels:=false,
                        vertex_color:=[255,0,0],
                        vertex_size:=10,
                        vertex_labels:=false,
                        open_in_background:=false )
{View the polytope P using Jmol. The dimension of the ambient lattice must be at most three.}
    // Sanity checks
    require IsPolytope(P) and not IsEmpty(P):
        "The polyhedron must be a non-empty polytope";
    require Dimension(Ambient(P)) le 3:
        "The ambient lattice must be at most three-dimensional";
    require not InternalIsPC(): "Operation not supported on Windows";
    require Type(path) eq MonStgElt:
        "Parameter 'path' must be a string";
    require Type(open_in_background) eq BoolElt:
        "Parameter 'open_in_background' must be a boolean";
    bool,err:=validate_parameters(background,transparency,
                                  face_color,edge_color,edge_width,
                                  point_color,point_size,point_labels,
                                  vertex_color,vertex_size,vertex_labels);
    require bool: err;
    // Create the jmol zip archive
    success,archive:=create_jmol_archive(P,title,background,transparency,
                                        face_color,edge_color,edge_width,
                                        point_color,point_size,point_labels,
                                        vertex_color,vertex_size,vertex_labels);
    require success: archive;
    // Open it with Jmol
    if open_in_background then
        // Launch Jmol using nohup
        cmd:="nohup " cat path cat " -Li " cat archive cat " &>/dev/null &";
        try
            res:=Pipe(cmd,"");
        catch e
            res:="FAILED";
        end try;
    else
        // Launch Jmol
        cmd:=path cat " -Li " cat archive cat " 2>&1 || echo \"FAILED\"";
        try
            res:=Pipe(cmd,"");
        catch e
            res:="FAILED";
        end try;
        // Delete the archive
        try
            _:=Pipe("rm " cat archive cat " 2>&1","");
        catch e;
        end try;
    end if;
    // Do we need to throw an error?
    require Index(res,"FAILED") eq 0:
        "Unable to send polytope to Jmol.\n(Using path: " cat path cat ")";
end intrinsic;
