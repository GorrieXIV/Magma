freeze;

/*
Algorithms to find irreducible simple subalgebras of su(N)
Author: Robert Zeier, 17 May 2011
*/

translate_node:=function(rd_str)
  alpha:=rd_str[1];
  numeric:=StringToInteger(rd_str[2..#rd_str]);
  case alpha:
    when "A":
       return "$\\su(" cat IntegerToString(numeric+1) cat")$";
    when "B":
       return "$\\so(" cat IntegerToString(2*numeric+1) cat")$";
    when "C":
       return "$\\ssp(" cat IntegerToString(numeric) cat")$";
    when "D":
       return "$\\so(" cat IntegerToString(2*numeric) cat")$";
    when "E":
       return "$\\fe_{" cat IntegerToString(numeric) cat"}$";
    when "F":
       return "$\\ff_{4}$";
    when "G":
       return "$\\fg_{2}$";
  end case;
end function;


print_vertex:=procedure(v,Gr,FP)
  on:=Sort(SetToSequence(OutNeighbors(v)));
  if (not IsRoot(v)) and IsRoot(RootSide(v)) then
    case (Label(v)`type):
      when -1:
        fprintf FP, "\\color{red}";
      when 1:
        fprintf FP, "\\color{blue}";
      else
        fprintf FP, "\\color{black}";
    end case;
  end if;
  if (#on gt 0) or (IsRoot(v)) then
    fprintf FP, "\\pstree{";
  end if;
  if IsRoot(v) and (Label(v)`type eq -1) then
    fprintf FP, "\\color{red}";
  end if;
  fprintf FP, "\\TR{" cat translate_node(Label(v)`algebra) cat "}";
  if (#on gt 0) or (IsRoot(v)) then
    fprintf FP, "}{%%";
  end if;
  fprintf FP, "\n";

  for i in on do
    $$(i,Gr,FP);
  end for;
  if (#on gt 0) or (IsRoot(v)) then  
    fprintf FP, "}";
  end if;  
end procedure;

print_graph:=procedure(Gr,FP)
  print_vertex(Root(Gr),Gr,FP);
end procedure;

weight_str:=function(w)
  str:="[";
  for k in [1..#w] do
      str_sub:="";
      if Ncols(w[k]) gt 5 then
        str_sub cat:= "$\\{";
        str_sub2:=[];
        for k2 in Sort([i[2]:i in Support(w[k])]) do
          str_sub3:="";
          str_sub3 cat:="\\langle ";
          str_sub3 cat:=IntegerToString(k2);
          str_sub3 cat:=",";
          str_sub3 cat:=IntegerToString((w[k])[1,k2]);
          str_sub3 cat:="\\rangle";
          Append(~str_sub2,str_sub3);
        end for;
        for k2 in [1..#str_sub2] do
          str_sub cat:=str_sub2[k2];
          if k2 ne #str_sub2 then
            str_sub cat:=",\\allowbreak{}";
          end if;      
        end for;
        str_sub cat:= "\\}$";
      else
        str_sub cat:="$(";
        for k2 in [1..Ncols(w[k])] do
          str_sub cat:=IntegerToString((w[k])[1,k2]);
          if k2 ne Ncols(w[k]) then
             str_sub cat:=",\\allowbreak{}";
          end if;      
        end for;
        str_sub cat:=")$";
      end if;
      str cat:=str_sub;
      if k ne #w then
         str cat:=",\\allowbreak{}";
      end if;      
  end for;
  str cat:="]";
  return str;
end function;


print_weights:=procedure(Gr,FP:color:=true)
  seq:=Sort(SetToSequence(Vertices(Gr)));
  for ind in [1..#seq] do
    fprintf FP, "{";

    if color then
      case (Label(seq[ind])`type):
        when -1:
          fprintf FP, "\\color{red}";
        when 1:
          fprintf FP, "\\color{blue}";
        else
          fprintf FP, "\\color{black}";
      end case; 
    end if;

    fprintf FP,weight_str(Label(seq[ind])`weights);

    fprintf FP, "}";

    if ind ne #seq then
      fprintf FP,",\\hfil\\allowbreak{}";
    end if;
  end for;  
end procedure;

procedure print_graphs_write_header(FP)
fprintf FP, "\\documentclass{article}
\\usepackage[left=1.8cm,right=1.5cm,top=1.5cm,bottom=1.5cm,nohead,letterpaper]{geometry}

\\usepackage{graphicx}
\\usepackage[cmex10]{amsmath}
\\interdisplaylinepenalty=2500
\\usepackage{amssymb}
\\usepackage{pstricks}
\\usepackage{pst-node}
\\usepackage{pstricks-add}
\\usepackage{pst-tree}
\\usepackage{multicol}
\\usepackage{color}
\\usepackage{colordvi}

\\newcommand{\\su}{\\mathfrak{su}}
\\newcommand{\\so}{\\mathfrak{so}}
\\newcommand{\\ssp}{\\mathfrak{sp}}
\\newcommand{\\fe}{\\mathfrak{e}}
\\newcommand{\\ff}{\\mathfrak{f}}
\\newcommand{\\fg}{\\mathfrak{g}}
\\newcommand{\\hfilll}{\\multido{}{100}{\\hfill}}

\\begin{document}
\\fontsize{6pt}{7.2pt}\\selectfont
\\setlength{\\columnsep}{10pt}
\\setlength{\\columnseprule}{0.5pt}

\\begin{multicols}{3}
";
end procedure;
procedure print_graphs_write_footer(FP)
  fprintf FP, "\\end{multicols}
\\end{document}
";
end procedure;


intrinsic PrintTreesSU(Q::SeqEnum[SeqEnum[Tup]], F::MonStgElt : FromDegree := 2, ToDegree := #Q, IncludeTrivial := true)
{ Compute subalgebra trees for su(k) in the list of irreducible simple subalgebras
  Q, and print a latex representation of the trees to the file F. }

  require FromDegree ge 2 : "FromDegree must be at least 2";
  require ToDegree le #Q : Sprintf("ToDegree can be at most #Q (%o in this case)", #Q);
  require Type(IncludeTrivial) eq BoolElt : "IncludeTrivial must be a boolean";

  FP:=Open(F,"w");
  print_graphs_write_header(FP);
  fprintf FP, "\\psset{treemode=L,edge=\\ncangles,armA=0.1cm,armB=0.1cm,angleB=0,angleA=180,arrows=->,arrowinset=0,arrowlength=0.5,nodesep=1pt,levelsep=*0.3cm,treesep=0.25}\n";
  for i in [FromDegree..ToDegree] do
    gr:=IrreducibleSimpleSubalgebraTreeSU(Q, i);
    if IncludeTrivial or ((i le 4) or (IsEven(i) and (Order(gr) ne 4)) or (IsOdd(i) and (Order(gr) ne 3))) then
      print_graph(gr,FP);
      fprintf FP," \\\\ {}";
      fprintf FP,"\n";
      print_weights(gr,FP);
      fprintf FP,"\\hfilll{}";
      if i lt ToDegree then
        fprintf FP,"\\\\ {}\n\\rule[+0.1cm]{\\columnwidth}{0.1pt}\n\\\\ {}\n"; 
        fprintf FP,"\\vspace{0.2cm}\n";
      elif i eq ToDegree then
        fprintf FP,"\n";
      end if;
    end if;
  end for;
  print_graphs_write_footer(FP);
end intrinsic;
