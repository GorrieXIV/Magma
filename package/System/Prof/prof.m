freeze;

function comp(x, y)
    if x gt y then
	return 1;
    elif x lt y then
	return -1;
    else
	return 0;
    end if;
end function;

// Print x to n digits
function print_real(x, n)
    x := Round(x * 10^n);
    s := IntegerToString(x mod 10^n);
    return IntegerToString(x div 10^n) cat "." cat "0"^(n - #s) cat s;
end function;

intrinsic ProfileGraph() -> GrphDir
{Obtain the profile information as a call graph.}
    node_format := recformat<
	Name : Strings(),
	Time : RealField(), Count : Integers()
    >;
    edge_format := recformat<
	Time : RealField(), Count : Integers()
    >;

    data := InternalProfileDump();
    if #data eq 0 then
	error "No profiler information available -- did you SetProfile(true)?";
    end if;

    edges := &cat[
	[
	    <
		[x[1] + 1, y[1] + 1],
		rec<edge_format | Time := y[3], Count := y[2]>
	    > : y in x[3] | not IsZero(y[2])
	] : x in data
    ];
    G, V, E := Digraph<#data | {x[1] : x in edges}>;
    AssignLabels([E!x[1] : x in edges], [x[2] : x in edges]);

    recs := [];
    for v in V do
	in_verts := InNeighbours(v);
	recs[Index(v)] := rec<
	    node_format |
	    Name := data[Index(v)][2],
	    Time :=
		&+[RealField() | Label(E![u, v])`Time : u in in_verts] -
		data[Index(v)][4],
	    Count := &+[Integers() | Label(E![u, v])`Count : u in in_verts]
	>;
    end for;

    r := V ! 1;
    recs[1] := rec<
	node_format |
	Name := data[1][2],
	Time := &+[RealField() | Label(E![r, u])`Time : u in OutNeighbours(r)],
	Count := 1
    >;

    AssignLabels(V, recs);

    return G;
end intrinsic;

function children_by_time(G, n)
    children := OutNeighbours(n);
    E := Edges(G);
    return Sort(
	SetToSequence(children),
	func<
	    x, y |
	    -comp(Label(E ! [n, x])`Time, Label(E ! [n, y])`Time)
	>
    );
end function;

function children_by_count(G, n)
    children := OutNeighbours(n);
    E := Edges(G);
    return Sort(
	SetToSequence(children),
	func<
	    x, y |
	    -comp(Label(E ! [n, x])`Count, Label(E ! [n, y])`Count)
	>
    );
end function;

procedure print_entry(i, n, t, c)
    if #n le 57 then
	printf "%-6o%-57o%-8o%-8o\n", i, n, t, c;
    else
	printf "%-6o%o\n", i, n;
	printf " "^63 cat "%-8o%-8o\n", t, c;
    end if;
end procedure;

function get_child_time(G, v, w)
    return Label(Edges(G) ! [v, w])`Time;
end function;

function get_child_count(G, v, w)
    return Label(Edges(G) ! [v, w])`Count;
end function;

function get_descendant_time(G, v, w)
    res := 0.0;
    E := Edges(G);
    for x in InNeighbours(w) do
	if Reachable(v, x) then
	    res +:= Label(E ! [x, w])`Time;
	end if;
    end for;
    return res;
end function;

function get_descendant_count(G, v, w)
    res := 0;
    E := Edges(G);
    for x in InNeighbours(w) do
	if Reachable(v, x) then
	    res +:= Label(E ! [x, w])`Count;
	end if;
    end for;
    return res;
end function;

procedure print_list(G, n, children, Percentage, Max, time_fn, count_fn)
    printf "Function: %o\n", Label(n)`Name;
    printf "Function Time: %o\n", print_real(Label(n)`Time, 3);
    printf "Function Count: %o\n", Label(n)`Count;
    printf "\n";

    fmt := "%-6o%-57o%-8o%-8o\n";
    printf fmt, "Index", "Name", "Time", "Count";

    E := Edges(G);

    if Percentage then
	total_time := Label(n)`Time;
	total_count := &+[count_fn(G, n, c) : c in children];
    end if;
    star := false;
    i := 0;
    for c in children do
	if Max ge 0 and i ge Max then
	    break;
	end if;
	i := i + 1;

	cname := Label(c)`Name;
	if Reachable(c, n) then
	    cname *:= " (*)";
	    star := true;
	end if;
	tme := time_fn(G, n, c);
	cnt := count_fn(G, n, c);
	if Percentage then
	    print_entry(
		Index(c), cname,
		print_real(100.0 * tme / total_time, 2),
		print_real(100.0 * cnt / total_count, 2)
	    );
	else
	    print_entry(Index(c), cname, print_real(tme, 3), cnt);
	end if;
    end for;

    if star then
	printf "* A recursive call is made through this child\n";
    end if;
end procedure;

intrinsic ProfilePrintChildrenByTime(
    G::GrphDir, n::GrphVert : Percentage := false, Max := -1
)
{Print the children of n sorted in order of decreasing time.}
    print_list(
	G, n, children_by_time(G, n), Percentage, Max,
	get_child_time, get_child_count
    );
end intrinsic;

intrinsic ProfilePrintChildrenByTime(
    G::GrphDir, n::RngIntElt : Percentage := false, Max := -1
)
{Print the children of n sorted in order of decreasing time.}
    ProfilePrintChildrenByTime(
	G, Vertices(G) ! n : Percentage := Percentage, Max := Max
    );
end intrinsic;

intrinsic ProfilePrintChildrenByCount(
    G::GrphDir, n::GrphVert : Percentage := false, Max := -1
)
{Print the children of n sorted in order of decreasing count.}
    print_list(
	G, n, children_by_count(G, n), Percentage, Max,
	get_child_time, get_child_count
    );
end intrinsic;

intrinsic ProfilePrintChildrenByCount(
    G::GrphDir, n::RngIntElt : Percentage := false, Max := -1
)
{Print the children of n sorted in order of decreasing count.}
    ProfilePrintChildrenByCount(
	G, Vertices(G) ! n : Percentage := Percentage, Max := Max
    );
end intrinsic;

function connected_nodes(G, v)
    res := {};
    left := {v};
    while #left gt 0 do
	ExtractRep(~left, ~w);
	Include(~res, w);
	left join:= OutNeighbours(w) diff res;
    end while;
    return res diff {v};
end function;

function descendants_by_time(G, n)
    E := Edges(G);
    return Sort(
	SetToSequence(connected_nodes(G, n)),
	func<
	    x, y |
	    -comp(get_descendant_time(G, n, x), get_descendant_time(G, n, y))
	>
    );
end function;

function descendants_by_count(G, n)
    E := Edges(G);
    return Sort(
	SetToSequence(connected_nodes(G, n)),
	func<
	    x, y |
	    -comp(get_descendant_count(G, n, x), get_descendant_count(G, n, y))
	>
    );
end function;

intrinsic ProfilePrintDescendantsByTime(
    G::GrphDir, n::GrphVert : Percentage := false, Max := -1
)
{Print the descendants of n sorted in order of decreasing time.}
    print_list(
	G, n, descendants_by_time(G, n), Percentage, Max,
	get_descendant_time, get_descendant_count
    );
end intrinsic;

intrinsic ProfilePrintDescendantsByTime(
    G::GrphDir, n::RngIntElt : Percentage := false, Max := -1
)
{Print the descendants of n sorted in order of decreasing time.}
    ProfilePrintDescendantsByTime(
	G, Vertices(G) ! n : Percentage := Percentage, Max := Max
    );
end intrinsic;

intrinsic ProfilePrintDescendantsByCount(
    G::GrphDir, n::GrphVert : Percentage := false, Max := -1
)
{Print the descendants of n sorted in order of decreasing count.}
    print_list(
	G, n, descendants_by_count(G, n), Percentage, Max,
	get_descendant_time, get_descendant_count
    );
end intrinsic;

intrinsic ProfilePrintDescendantsByCount(
    G::GrphDir, n::RngIntElt : Percentage := false, Max := -1
)
{Print the descendants of n sorted in order of decreasing count.}
    ProfilePrintDescendantsByCount(
	G, Vertices(G) ! n : Percentage := Percentage, Max := Max
    );
end intrinsic;

procedure print_total_list(G, V, Percentage, Max)
    fmt := "%-6o%-57o%-8o%-8o\n";
    printf fmt, "Index", "Name", "Time", "Count";

    E := Edges(G);

    if Percentage then
	total_time := Label(V ! 1)`Time;
	total_count := &+[Label(v)`Count : v in V];
    end if;

    i := 0;
    for v in V do
	if Max ge 0 and i ge Max then
	    break;
	end if;
	i := i + 1;

	l := Label(v);
	if Percentage then
	    print_entry(
		Index(v), l`Name,
		print_real(100.0 * l`Time / total_time, 2),
		print_real(100.0 * l`Count / total_count, 2)
	    );
	else
	    print_entry(Index(v), l`Name, print_real(l`Time, 3), l`Count);
	end if;
    end for;
end procedure;

function by_total_time(G)
    return Sort(
	SetToSequence(Vertices(G)),
	func<x, y | -comp(Label(x)`Time, Label(y)`Time)>
    );
end function;

function by_total_count(G)
    return Sort(
	SetToSequence(Vertices(G)),
	func<x, y | -comp(Label(x)`Count, Label(y)`Count)>
    );
end function;

intrinsic ProfilePrintByTotalTime(: Percentage := false, Max := -1)
{}
    G := ProfileGraph();
    print_total_list(G, by_total_time(G), Percentage, Max);
end intrinsic;

intrinsic ProfilePrintByTotalTime(G::GrphDir : Percentage := false, Max := -1)
{Print the list of functions profiled sorted in order of decreasing time.}
    print_total_list(G, by_total_time(G), Percentage, Max);
end intrinsic;

intrinsic ProfilePrintByTotalCount(: Percentage := false, Max := -1)
{}
    G := ProfileGraph();
    print_total_list(G, by_total_count(G), Percentage, Max);
end intrinsic;

intrinsic ProfilePrintByTotalCount(G::GrphDir : Percentage := false, Max := -1)
{Print the list of functions profiled sorted in order of decreasing count.}
    print_total_list(G, by_total_count(G), Percentage, Max);
end intrinsic;

// Returns the default path to dotty. This can also be specified with the
// environment variable DOTTY_PATH. You can download dotty (part of the
// Graphviz package) from:
//   http://www.graphviz.org/
function dotty_path()
    if InternalIsPC() then return "/usr/local/bin/dotty"; end if;
    try
        path:=GetEnv("DOTTY_PATH");
    catch e;
        path:="";
    end try;
    if #path gt 0 then return path; end if;
    try
        res:=Pipe("test -e /local/usr/bin/dotty 2>/dev/null && echo 1","");
        bool:=Regexp("1",res);
    catch e;
        bool:=false;
    end try;
    return bool select "/local/usr/bin/dotty" else "/usr/local/bin/dotty";
end function;

intrinsic ProfilePrintGraphByCount(G::GrphDir : dotty:=dotty_path())
{}
    require Type(dotty) eq MonStgElt and #dotty ne 0:
        "Parameter 'dotty' must be a non-empty string (the path to dotty).";
    input := "digraph \"Call Graph\" {\n";
    for v in Vertices(G) do
	input *:= Sprintf(
	    "    n%o [label=\"%o (%o)\"];\n",
	    Index(v), Label(v)`Name, Label(v)`Count
	);
    end for;
    for e in Edges(G) do
	input *:= Sprintf(
	    "    n%o -> n%o [label=\"%o\"];\n",
	    Index(InitialVertex(e)), Index(TerminalVertex(e)), Label(e)`Count
	);
    end for;
    input *:= "}\n";
    file := GetTempDir() cat "/" cat Tempname("graph");
    Pipe("cat > " cat file, input);
    System(dotty cat " " cat file cat " &");
end intrinsic;

intrinsic ProfilePrintGraphByTime(G::GrphDir : dotty:=dotty_path())
{}
    require Type(dotty) eq MonStgElt and #dotty ne 0:
        "Parameter 'dotty' must be a non-empty string (the path to dotty).";
    input := "digraph \"Call Graph\" {\n";
    for v in Vertices(G) do
	input *:= Sprintf(
	    "    n%o [label=\"%o (%o)\"];\n",
	    Index(v), Label(v)`Name, print_real(Label(v)`Time, 2)
	);
    end for;
    for e in Edges(G) do
	input *:= Sprintf(
	    "    n%o -> n%o [label=\"%o\"];\n",
	    Index(InitialVertex(e)), Index(TerminalVertex(e)),
	    print_real(Label(e)`Time, 2)
	);
    end for;
    input *:= "}\n";
    file := GetTempDir() cat "/" cat Tempname("graph");
    Pipe("cat > " cat file, input);
    System(dotty cat " " cat file cat " &");
end intrinsic;

function prune_graph(G, verts)
    G2 := sub<G | verts join {Root(G)}>;
    for v in Vertices(G2) do
	AssignLabel(v, Label(Vertices(G) ! v));
    end for;
    for e in Edges(G2) do
	AssignLabel(e, Label(Edges(G) ! e));
    end for;
    G3 := G2;
    for v in Vertices(G2) do
	if not Reachable(Root(G2), v) then
	    G3 := G3 - Vertices(G3) ! v;
	end if;
    end for;
    return G3;
end function;

intrinsic ProfilePruneGraphByCount(G::GrphDir, n::RngIntElt) -> GrphDir
{}
    return prune_graph(G, { v : v in by_total_count(G)[1..n] });
end intrinsic;

intrinsic ProfilePruneGraphByTime(G::GrphDir, n::RngIntElt) -> GrphDir
{}
    return prune_graph(G, { v : v in by_total_time(G)[1..n] });
end intrinsic;
