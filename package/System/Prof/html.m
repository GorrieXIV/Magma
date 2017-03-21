freeze;
 
header :=
"<html>
    <head>
        <style type='text/css'>
            .rel { POSITION: relative; width: 100%%; }
            .abs { POSITION: absolute; width: 100%%; }
            .right { text-align:right; }
            .left { text-align:left; }
            .center { text-align:center; }
        </style>

        <script language='javascript' src='%osorttable.js'></script>
        <script language='javascript'>
";

footer :=
"    </body>
</html>
";

// Print x to n digits
function print_real(x, n)
    x := Round(x * 10^n);
    s := IntegerToString(x mod 10^n);
    return IntegerToString(x div 10^n) cat "." cat "0"^(n - #s) cat s;
end function;

function escape(x)
    y := "";
    for c in Eltseq(x) do
	if c eq "<" then
	    y cat:= "&lt;";
	elif c eq ">" then
	    y cat:= "&gt;";
	elif c eq "&" then
	    y cat:= "&amp;";
	else
	    y cat:= c;
	end if;
    end for;
    return y;
end function;

// Writes a table to file f, with name t, using entries (a sequence of
// tuples <index, name, is_recursive, is_leaf, time, time %, count, count %>).
procedure write_table(prefix, f, t, entries:Dir)
    Puts(f, "            var " cat t cat " = new SortTable('" cat t cat "');");

    Put(f, "            " cat t);
    Puts(f, ".AddColumn('Index', '', '', 'numeric');");

    Put(f, "            " cat t);
    Puts(f, ".AddColumn('Name', '', '', '');");

    Put(f, "            " cat t);
    Puts(f, ".AddColumn('Time', '', '', 'numeric');");

    Put(f, "            " cat t);
    Puts(f, ".AddColumn('Time (%)', '', '', 'numeric');");

    Put(f, "            " cat t);
    Puts(f, ".AddColumn('Count', '', '', 'numeric');");

    Put(f, "            " cat t);
    Puts(f, ".AddColumn('Count (%)', '', '', 'numeric');");

    for x in entries do
	index := x[1];
	name := x[2];
	is_recursive := x[3];
	is_leaf := x[4];
	time_spent := x[5];
	time_pct := x[6];
	count := x[7];
	count_pct := x[8];

	href := "<a href=\"" cat prefix cat Sprint(index) cat ".html\">";

	Put(f, "            " cat t);
	Put(f, ".AddLine('" cat href cat Sprint(index) cat "</a>");
	if is_leaf then
            if Dir eq "" then
              Put(f, "<img src=\"" cat GetLibraryRoot() cat "/prof/leaf.gif\"");
              Put(f, " alt=\"Leaf Function\"></img>");
            else
              Put(f, "<img src=\"leaf.gif\"");
              Put(f, " alt=\"Leaf Function\"></img>");
            end if;
	end if;
	Put(f, "', '");

	Put(f, href cat escape(name) cat "</a>");
	if is_recursive then
	    Put(f, " (<a href=\"#" cat t cat "_star\">*</a>)");
	end if;
	Put(f, "', '");

	Put(f, print_real(time_spent, 3) cat "', '");

	Put(f, print_real(time_pct, 2) cat "', '");

	Put(f, Sprint(count) cat "', '");

	Put(f, print_real(count_pct, 2) cat "');");
	Puts(f, "");

	Puts(
	    f,
	    "            " cat t cat ".AddLineSortData('" cat Sprint(index) cat
	    "', '" cat escape(name) cat "', '', '', '', '');"
	);
    end for;
end procedure;

procedure print_table(f, t)
    table_header :=
"        <p>
        Click on the column headings below to change the sort order.
        <p>
        <table border='1'>
            <tr>";

    Puts(f, table_header);
    Puts(
	f,
	"                <th><a href='javascript:SortRows(" cat t cat
	",0)'>Index</a></th>"
    );
    Puts(
	f,
	"                <th><a href='javascript:SortRows(" cat t cat
	",1)'>Name</a></th>"
    );
    Puts(
	f,
	"                <th><a href='javascript:SortRows(" cat t cat
	",2)'>Time</a></th>"
    );
    Puts(
	f,
	"                <th><a href='javascript:SortRows(" cat t cat
	",3)'>Time (%)</a></th>"
    );
    Puts(
	f,
	"                <th><a href='javascript:SortRows(" cat t cat
	",4)'>Count</a></th>"
    );
    Puts(
	f,
	"                <th><a href='javascript:SortRows(" cat t cat
	",5)'>Count (%)</a></th>"
    );
    Puts(f, "            </tr>");
    Puts(f, "            <script>" cat t cat ".WriteRows()</script>");
    Puts(f, "        </table>");
end procedure;

procedure print_total_list(G, prefix :Dir)
    V := Vertices(G);

    total_time := Label(V ! 1)`Time;
    total_count := &+[Label(v)`Count : v in V];

    entries := [];
    for v in V do
	l := Label(v);

	index := Index(v);
	name := l`Name;
	is_leaf := #OutNeighbours(v) eq 0;
	time_spent := l`Time;
	if IsZero(total_time) then
	    time_pct := 100.0;
	else
	    time_pct := 100.0 * l`Time / total_time;
	end if;
	count := l`Count;
	count_pct := 100.0 * l`Count / total_count;
	Append(
	    ~entries,
	    <
		index, name, false, is_leaf, time_spent, time_pct, count,
		count_pct
	    >
	);
    end for;

    f := Open(Dir cat prefix cat ".html", "wt");
    if Dir eq "" then
      Put(f, Sprintf(header, GetLibraryRoot() * "/prof/"));
    else
      Put(f, Sprintf(header, ""));
    end if;
    write_table(prefix, f, "t", entries : Dir := Dir);

    Puts(f, "        </script>");
    Puts(f, "");
    Puts(f, "        <title>Magma Profiler Output: Function Listing</title>");
    Puts(f, "    </head>");
    Puts(f, "    <body>");
    Puts(f, "        <h1>Magma Profiler Output: Function Listing</h1>");
    Puts(f, "        <p>");
    print_table(f, "t");
    Put(f, footer);
    delete f;
end procedure;

intrinsic ProfileHTMLOutput(prefix::MonStgElt :Dir := "")
{}
  ProfileHTMLOutput(ProfileGraph(), prefix : Dir := Dir);
end intrinsic;

intrinsic ProfileHTMLOutput(G::GrphDir, prefix::MonStgElt :Dir := "")
{Generate an HTML report of the profiler run.}
    E := Edges(G);
    V := Vertices(G);

    if #Dir gt 0 and Dir[#Dir] ne "/" then
      Dir *:= "/";
    end if;

    print_total_list(G, prefix: Dir := Dir);

    for v in V do
	f := Open(Dir cat prefix cat Sprint(v) cat ".html", "wt");
        if Dir eq "" then
          Put(f, Sprintf(header, GetLibraryRoot() cat "/prof/"));
        else
          Put(f, Sprintf(header, ""));
        end if;

	parents := InNeighbours(v);
	if #parents gt 0 then
	    entries := [];

	    total_time := &+[Label(E ! [p, v])`Time : p in parents];
	    total_count := &+[Label(E ! [p, v])`Count : p in parents];

	    parent_star := false;
	    for p in parents do
		l := Label(E ! [p, v]);

		index := Index(p);
		name := Label(p)`Name;
		is_recursive := Reachable(v, p);
		time_spent := l`Time;
		if IsZero(total_time) then
		    time_pct := 100.0;
		else
		    time_pct := 100.0 * l`Time / total_time;
		end if;
		count := l`Count;
		count_pct := 100.0 * l`Count / total_count;
		
		Append(
		    ~entries,
		    <
			index, name, is_recursive, false, time_spent,
			time_pct, count, count_pct
		    >
		);

		parent_star := parent_star or is_recursive;
	    end for;

	    write_table(prefix, f, "p", entries: Dir := Dir);
	end if;

	children := OutNeighbours(v);
	if #children gt 0 then
	    entries := [];

	    total_time := Label(v)`Time;
	    total_count := &+[Label(E ! [v, c])`Count : c in children];

	    child_star := false;
	    for c in children do
		l := Label(E ! [v, c]);

		index := Index(c);
		name := Label(c)`Name;
		is_recursive := Reachable(c, v);
		is_leaf := #OutNeighbours(c) eq 0;
		time_spent := l`Time;
		if IsZero(total_time) then
		    time_pct := 100.0;
		else
		    time_pct := 100.0 * l`Time / total_time;
		end if;
		count := l`Count;
		count_pct := 100.0 * l`Count / total_count;

		Append(
		    ~entries,
		    <
			index, name, is_recursive, is_leaf, time_spent,
			time_pct, count, count_pct
		    >
		);

		child_star := child_star or is_recursive;
	    end for;

	    write_table(prefix, f, "c", entries: Dir := Dir);
	end if;

	vname := escape(Label(v)`Name);

	Puts(f, "        </script>");
	Puts(f, "");
	Puts(
	    f,
	    "        <title>Magma Profiler Output for " cat vname cat "</title>"
	);
	Puts(f, "    </head>");
	Puts(f, "    <body>");
	Puts(f, "        <h1>Magma Profiler Output</h1>");
	Puts(f, "        <p>");
	Puts(f, "        <h3>Function: " cat vname cat "</h3>");
	Puts(
	    f,
	    "        <h3>Function Time: " cat print_real(Label(v)`Time, 3) cat
	    "</h3>"
	);
	Puts(
	    f,
	    "        <h3>Function Count: " cat Sprint(Label(v)`Count) cat
	    "</h3>"
	);

	if #parents gt 0 then
	    Puts(f, "        <p>");
	    Puts(f, "        <h3>Distribution to callers</h3>");
	    print_table(f, "p");
	    if parent_star then
		Puts(f, "        <a name='#p_star'><p></a>");
		Puts(
		    f,
		    "        A recursive call is made through this function."
		);
	    end if;
	end if;

	Puts(f, "        <p>");
	if #children gt 0 then
	    Puts(f, "        <h3>Contributions from children</h3>");
	    print_table(f, "c");
	    if child_star then
		Puts(f, "        <a name='#c_star'><p></a>");
		Puts(f, "        A recursive call is made through this child.");
	    end if;
	else
	    Puts(f, "        <h3>This function called no other functions</h3>");
	end if;

	Puts(f, "        <p>");
	Puts(
	    f,
	    "        <a href='" cat prefix cat
	    ".html'>Go to function listing</a>"
	);
	Put(f, footer);
	delete f;
    end for;
end intrinsic;
