freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// Thank you!

////////////////////////////////////////////////////////////////////////
//                                                                    
// This computes the Voronoi cells for a number of sites. It is a pretty 
// mindless implementation of the paper:
// Primitives for the Manipulation of General Subdivisions and the 
// Computation of Voronoi Diagrams, By Leonidas Guibas and Jorge Stolfi, 
// ACM Transactions on Graphics, Vol. 4, No 2, April 1985, Pages 74-123.
//
//  Paul van Wamelen (December 2002)
//                                                                    
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//    Delaunay,
//    Voronoi
//     
//     
////////////////////////////////////////////////////////////////////////

/*
This computes the Voronoi cells for a number of sites. It is a pretty mindless
implementation of the paper:
Primitives for the Manipulation of General Subdivisions and the Computation of Voronoi Diagrams, By Leonidas Guibas and Jorge Stolfi, ACM Transactions on Graphics, Vol. 4, No 2, April 1985, Pages 74-123.
*/

function radd(r,i)
  return ((r+i-1) mod 4)+1;
end function;

function Rot(e,n);
  return <e[1],radd(e[2],n)>;
end function;

procedure Onext(~d,e,~edges);
  d := edges[1][e[1]][e[2]][2];
end procedure;

function Sym(e);
  return Rot(e,2);
end function;

procedure Oprev(~d,e,~edges);
  Onext(~d,Rot(e,1),~edges);
  d := Rot(d,1);
end procedure;

procedure Lnext(~d,e,~edges);
  Onext(~d,Rot(e,-1),~edges);
  d := Rot(d,1);
end procedure;

procedure Rnext(~d,e,~edges);
  Onext(~d,Rot(e,1),~edges);
  d := Rot(d,-1);
end procedure;

procedure Dnext(~d,e,~edges);
  Onext(~d,Rot(e,2),~edges);
  d := Rot(d,2);
end procedure;

procedure Lprev(~d,e,~edges);
  Onext(~d,e,~edges);
  d := Sym(d);
end procedure;

procedure Rprev(~d,e,~edges);
  Onext(~d,Sym(e),~edges);
end procedure;
  
procedure Dprev(~d,e,~edges);
  Onext(~d,Rot(e,3),~edges);
  d := Rot(d,3);
end procedure;
  
procedure MakeEdge(~e,~edges)
  if #edges[2] eq 0 then
    ind := #edges[1]+1;
    Append(~edges[1],<<0,<ind,1>>,<0,<ind,4>>,<0,<ind,3>>,<0,<ind,2>>>);
  else
    ind := edges[2][1];
    Remove(~edges[2],1);
    edges[1][ind] := <<0,<ind,1>>,<0,<ind,4>>,<0,<ind,3>>,<0,<ind,2>>>;
  end if;
  e := <ind,1>;
end procedure;

procedure AssignEdge(a,b,~edges)
  edges[1][a[1]][a[2]] := edges[1][b[1]][b[2]];
end procedure;

procedure SwapOnextPointers(a,b,~edges)
  tmp := edges[1][a[1]][a[2]][2];
  edges[1][a[1]][a[2]][2] := edges[1][b[1]][b[2]][2];
  edges[1][b[1]][b[2]][2] := tmp;
end procedure;

procedure Splice(a,b,~edges);
  Onext(~Ona,a,~edges);
  Onext(~Onb,b,~edges);
  alpha := Rot(Ona,1);
  beta  := Rot(Onb,1);
  SwapOnextPointers(a,b,~edges);
  SwapOnextPointers(alpha,beta,~edges);
end procedure;

procedure Dest(~eDest,e,~edges)
  eDest := edges[1][e[1]][radd(e[2],2)][1];
end procedure;

procedure Org(~eOrg,e,~edges)
  eOrg := edges[1][e[1]][e[2]][1];
end procedure;

function edge2string(e,edges);
  Org(~org,e,~edges);
  Dest(~dest,e,~edges);
  return Sprintf("from %o to %o",org,dest);
end function;

procedure AssignDest(e,data,~edges)
  edges[1][e[1]][radd(e[2],2)][1] := data;
end procedure;

procedure AssignOrg(e,data,~edges)
  edges[1][e[1]][e[2]][1] := data;
end procedure;
  
procedure Connect(a,b,~e,~edges)
  MakeEdge(~e,~edges);
  Dest(~aDest,a,~edges);
  AssignOrg(e,aDest,~edges);
  Org(~bOrg,b,~edges);
  AssignDest(e,bOrg,~edges);
  Lnext(~aLnext,a,~edges);
  Splice(e,aLnext,~edges);
  Splice(Sym(e),b,~edges);
end procedure;

procedure DeleteEdge(e,~edges)
  Oprev(~eOprev,e,~edges);
  Splice(e,eOprev,~edges);
  Oprev(~d,Sym(e),~edges);
  Splice(Sym(e),d,~edges);
  Append(~edges[2],e[1]);
end procedure;

procedure CCW(~ans,a,b,c,~sites)
  mat := Matrix(3,3,
    [sites[a][1],sites[a][2],1,
     sites[b][1],sites[b][2],1,
     sites[c][1],sites[c][2],1]);
  R := Parent(sites[1][1]);
  assert Type(R) eq FldRe;
  pres := Precision(R);
  ans := Determinant(mat) gt 10^(-pres+4);
end procedure;

procedure RightOf(~ans,a,e,~edges,~sites)
  Org(~eO,e,~edges);
  Dest(~eD,e,~edges);
  CCW(~ans,a,eD,eO,~sites);
end procedure;

procedure Valid(~ans,e,basel,~edges,~sites)
  Dest(~eD,e,~edges);
  RightOf(~ans,eD,basel,~edges,~sites);
end procedure;

procedure LeftOf(~ans,a,e,~edges,~sites)
  Org(~eO,e,~edges);
  Dest(~eD,e,~edges);
  CCW(~ans,a,eO,eD,~sites);
end procedure;

procedure InCircle(~ans,a,b,c,d,~sites);
  mat := Matrix(4,4,
    [sites[a][1],sites[a][2],sites[a][1]^2+sites[a][2]^2,1,
     sites[b][1],sites[b][2],sites[b][1]^2+sites[b][2]^2,1,
     sites[c][1],sites[c][2],sites[c][1]^2+sites[c][2]^2,1,
     sites[d][1],sites[d][2],sites[d][1]^2+sites[d][2]^2,1]);
  R := Parent(sites[1][1]);
  assert Type(R) eq FldRe;
  pres := Precision(R);
  ans := Determinant(mat) gt 10^(-pres+4);
end procedure;

function CompareSites(a,b);
  if a[1] gt b[1] then
    return 1;
  elif a[1] lt b[1] then
    return -1;
  elif a[2] gt b[2] then
    return 1;
  elif a[2] lt b[2] then
    return -1;
  else
    return 0;
  end if;
end function;

// sites are a list of coordinates
// sitelst is a set of indices to points in sites
procedure Delaunay0(sitelst,~ledge,~redge,~edges,~sites);
  if #sitelst eq 2 then
    MakeEdge(~a,~edges);
    AssignOrg(a,sitelst[1],~edges);
    AssignDest(a,sitelst[2],~edges);
    ledge := a;
    redge := Sym(a);
  elif #sitelst eq 3 then
    MakeEdge(~a,~edges);
    MakeEdge(~b,~edges);
    Splice(Sym(a),b,~edges);
    AssignOrg(a,sitelst[1],~edges);
    AssignDest(a,sitelst[2],~edges);
    AssignOrg(b,sitelst[2],~edges);
    AssignDest(b,sitelst[3],~edges);
    CCW(~ccw,sitelst[1],sitelst[2],sitelst[3],~sites);
    if ccw then
      Connect(b,a,~c,~edges);
      ledge := a;
      redge := Sym(b);
    else
      CCW(~ccw,sitelst[1],sitelst[3],sitelst[2],~sites);
      if ccw then
        Connect(b,a,~c,~edges);
        ledge := Sym(c);
        redge := c;
      else
        ledge := a;
        redge := Sym(b);
      end if;
    end if;
  else      // #sitelst > 3
    dum := #sitelst div 2;
    Delaunay0([sitelst[i] : i in [1..dum]],~ldo,~ldi,~edges,~sites);
    Delaunay0([sitelst[i] : i in [dum+1..#sitelst]],~rdi,~rdo,~edges,~sites);
    while true do
      Org(~Ordi,rdi,~edges);
      LeftOf(~LO,Ordi,ldi,~edges,~sites);
      if LO then
        Lnext(~ldi,ldi,~edges);
      else
        Org(~Oldi,ldi,~edges);
        RightOf(~RO,Oldi,rdi,~edges,~sites);
        if RO then
          Rprev(~rdi,rdi,~edges);
        else
          break;
        end if;
      end if;
    end while;
    Connect(Sym(rdi),ldi,~basel,~edges);
    Org(~O1,ldi,~edges);
    Org(~O2,ldo,~edges);
    if O1 eq O2 then
      ldo := Sym(basel);
    end if;
    Org(~O1,rdi,~edges);
    Org(~O2,rdo,~edges);
    if O1 eq O2 then
      rdo := basel;
    end if;
    while true do
      Dest(~Dbl,basel,~edges);
      Org( ~Obl,basel,~edges);
      Onext(~lcand,Sym(basel),~edges);
      Valid(~valid,lcand,basel,~edges,~sites);
      if valid then
        while true do
          Dest(~Dlc,lcand,~edges);
          Onext(~Olc,lcand,~edges);
          Dest(~DOlc,Olc,~edges);
          InCircle(~IC,Dbl,Obl,Dlc,DOlc,~sites);
          if not IC then
            break;
          end if;
          Onext(~t,lcand,~edges);
          DeleteEdge(lcand,~edges);
          lcand := t;
        end while;
      end if;
      Oprev(~rcand,basel,~edges);
      Valid(~valid,rcand,basel,~edges,~sites);
      if valid then
        while true do
          Dest(~Drc,rcand,~edges);
          Oprev(~Orc,rcand,~edges);
          Dest(~DOrc,Orc,~edges);
          InCircle(~IC,Dbl,Obl,Drc,DOrc,~sites);
          if not IC then
            break;
          end if;
          Oprev(~t,rcand,~edges);
          DeleteEdge(rcand,~edges);
          rcand := t;
        end while;
      end if;
      Valid(~lvalid,lcand,basel,~edges,~sites);
      Valid(~rvalid,rcand,basel,~edges,~sites);
      if (not lvalid) and (not rvalid) then
        break;
      end if;
      Dest(~Dlc,lcand,~edges);
      Org( ~Olc,lcand,~edges);
      Dest(~Drc,rcand,~edges);
      Org( ~Orc,rcand,~edges);
      InCircle(~IC,Dlc,Olc,Orc,Drc,~sites);
      if (not lvalid) or (rvalid and IC) then
        Connect(rcand,Sym(basel),~basel,~edges);
      else
        Connect(Sym(basel),Sym(lcand),~basel,~edges);
      end if;
    end while;
    ledge := ldo;
    redge := rdo;
  end if;
end procedure;

procedure Delaunay1(~sites, ~sitelst, ~edges);
  _,p := Sort(sites,CompareSites);
  sitelst := ElementToSequence(p);
  edges := [*[],[]*];
  Delaunay0(sitelst,~ledge,~redge,~edges,~sites);
end procedure;

// This just translates the quad-edge data structure into the simpler output 
// format.
procedure Delaunay2(~sites, ~sitelst, ~edges, ~siteedges)
  siteedges := [[] : i in sites];
  for i in [i : i in [1..#edges[1]] | i notin edges[2]] do
    for j in [1,3] do
      edge := <i,j>;
      e := edge;
      Org( ~org,<i,j>,~edges);
      if siteedges[org] eq [] then
        lst := [];
        repeat
          Onext(~e,e,~edges);
          Dest(~dest,e,~edges);
          Append(~lst,dest);
        until e eq edge;
        siteedges[org] := lst;
      end if;
    end for;    
  end for;
end procedure;

intrinsic Delaunay(sites::SeqEnum[Tup]) -> SeqEnum
{Compute the Delaunay triangulation of sites}
  require #sites[1] eq 2: "Argument 1 must be a list of pairs of real numbers";
  require Category(sites[1][1]) in [FldReElt]: "Argument 1 must be a list of tuples of real numbers";
  require Category(sites[1][2]) in [FldReElt]: "Argument 1 must be a list of tuples of real numbers";
  // scale things so that sites fill out [0,1]x[0,1]. This is so that scaling 
  // doesn't effect our zero checks...
  lst := [p[1] : p in sites];
  maxx := Maximum(lst);
  minx := Minimum(lst);
  lst := [p[2] : p in sites];
  maxy := Maximum(lst);
  miny := Minimum(lst);
  len := 0.6*Maximum(maxx-minx,maxy-miny);
  cx := (maxx+minx)/2;
  cy := (maxy+miny)/2;
  sites := [<(xy[1]-(cx-len))/(2*len),(xy[2]-(cy-len))/(2*len)> : xy in sites];
  Delaunay1(~sites, ~sitelst, ~edges);
  Delaunay2(~sites, ~sitelst, ~edges, ~siteedges);
  return siteedges;
end intrinsic;

procedure VoronoiPoint(duale,~edges,~sites,~dualsites)
  if edges[1][duale[1]][duale[2]][1] eq 0 then
    e := Rot(duale,-1);
    Org(~a,e,~edges);
    Dest(~b,e,~edges);
    Oprev(~ep,e,~edges);
    Dest(~c,ep,~edges);
    LeftOf(~LO,b,ep,~edges,~sites);
    if LO then
      Ax := sites[a][1];
      Ay := sites[a][2];
      Bx := sites[b][1];
      By := sites[b][2];
      Cx := sites[c][1];
      Cy := sites[c][2];
      Dx := (Ax+Bx)/2;
      Dy := (Ay+By)/2;
      Ex := (Ax+Cx)/2;
      Ey := (Ay+Cy)/2;
      if By eq Ay then
        x := Dx;
        m2 := (Cx-Ax)/(Cy-Ay); // Cy ne Ay
        y := (Ex-x)*m2+Ey;
      else
        m1 := (Bx-Ax)/(By-Ay); // reciprical of slope
        if Cy eq Ay then
          x := Ex;
          y := (Dx-x)*m1+Dy;
        else
          m2 := (Cx-Ax)/(Cy-Ay);
          x := (Ey-Dy+m2*Ex-m1*Dx)/(m2-m1);
          y := (Dx-x)*m1+Dy;
        end if;
      end if;
      Append(~dualsites,<x,y,0>);
      ind := #dualsites;
      de := duale;
      repeat
        Onext(~de,de,~edges);
        edges[1][de[1]][de[2]][1] := ind;
      until de eq duale;
    else // this is an edge from infinity, save it's slope and direction
      R := Parent(sites[1][1]);
      matlst := [sites[a][1],sites[a][2],1,sites[b][1],sites[b][2],1,0,0,1];
      Ax := sites[a][1];
      Ay := sites[a][2];
      Bx := sites[b][1];
      By := sites[b][2];
      Dx := (Ax+Bx)/2;
      Dy := (Ay+By)/2;
      if By ne Ay then // finite slope
        mm := -(Bx-Ax)/(By-Ay);
        matlst[7] := Dx+1;
        matlst[8] := Dy+mm;
        mat := Matrix(3,3,matlst);
        if -Determinant(mat) gt 0 then // large x goes to infinity
          Append(~dualsites,<R!1,mm,1>);
        else // large negative x goes to infinity
          Append(~dualsites,<R!-1,-mm,1>);
        end if;
      else
        matlst[7] := Dx;
        matlst[8] := Dy+1;
        mat := Matrix(3,3,matlst);
        if -Determinant(mat) gt 0 then // big positive y goes to infinity
          Append(~dualsites,<R!0,R!1,1>);
        else // large negative y goes to infinity
          Append(~dualsites,<R!0,R!-1,1>);
        end if;
      end if;
      ind := #dualsites;
      edges[1][duale[1]][duale[2]][1] := ind;
    end if;
  end if;
end procedure;

procedure Voronoi1(~sites, ~edges, ~sitelst, ~dualsites);
  _,p := Sort(sites,CompareSites);
  sitelst := ElementToSequence(p);
  edges := [*[],[]*];
  Delaunay0(sitelst,~ledge,~redge,~edges,~sites);
  dualsites := [];
  for i in [i : i in [1..#edges[1]] | i notin edges[2]] do
    VoronoiPoint(<i,2>,~edges,~sites,~dualsites);
    VoronoiPoint(<i,4>,~edges,~sites,~dualsites);
  end for;
end procedure;

intrinsic Voronoi(sites::SeqEnum[Tup]) -> SeqEnum, SeqEnum, SeqEnum
{Compute the Voronoi cells of the sites}
  require #sites[1] eq 2: "Argument 1 must be a list of pairs of real numbers";
  require Category(sites[1][1]) in [FldReElt]: "Argument 1 must be a list of tuples of real numbers";
  require Category(sites[1][2]) in [FldReElt]: "Argument 1 must be a list of tuples of real numbers";
  lst := [p[1] : p in sites];
  maxx := Maximum(lst);
  minx := Minimum(lst);
  lst := [p[2] : p in sites];
  maxy := Maximum(lst);
  miny := Minimum(lst);
  len := 6/10*Maximum(maxx-minx,maxy-miny);
  cx := (maxx+minx)/2;
  cy := (maxy+miny)/2;
  sites := [<(xy[1]-(cx-len))/(2*len),(xy[2]-(cy-len))/(2*len)> : xy in sites];

  Voronoi1(~sites, ~edges, ~sitelst, ~dualsites);
  Delaunay2(~sites, ~sitelst, ~edges, ~siteedges);
  // now translate quad-edge data into the simplified description of cells
  cells := [[] : i in sites];
  for i in [i : i in [1..#edges[1]] | i notin edges[2]] do
    for j in [1,3] do
      edge := <i,j>;
      e := edge;
      Org( ~sitenum,edge,~edges);
      if cells[sitenum] eq [] then
        lst := [];
        repeat
          Onext(~e,e,~edges);
          de := Rot(e,1);
          Dest(~dest,de,~edges);
          Append(~lst,dest);
        until e eq edge or dualsites[dest][3] ne 0;
        if dualsites[dest][3] ne 0 then
          Onext(~e,edge,~edges);
          repeat
            de := Rot(e,1);
            Org(~org,de,~edges);
            Insert(~lst,1,org);
            Oprev(~e,e,~edges);
          until dualsites[org][3] ne 0;
        end if;
        cells[sitenum] := lst;
      end if;
    end for;    
  end for;
  // unscale
  dualsites := [xyb[3] eq 0 select <xyb[1]*2*len+cx-len,xyb[2]*2*len+cy-len,0> else xyb : xyb in dualsites];
  return siteedges, dualsites, cells;
end intrinsic;


