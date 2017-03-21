freeze;

////////////////////////////////////////////////////////////////////
//                                                                //  
//        Farey Symbols                                           // 
//        for congruence subgroups                                //
//  by Helena A. Verrill                                          //
//                                                                // 
////////////////////////////////////////////////////////////////////

/**********************   CHANGES LOG   ****************************

// hav: update 28 August 2002 - correct error that list of
// labels in Farey symbol was output as sequence of rationals
// instead of sequence of integers.

// hav: update 14 October 2002 - corrected to deal with groups
// involving a Dirichlet character.

   SRD, Jan 2009 -- avoid repeated calls to PSL2(Integers()),
   this was dominating runtime in Generators of X_15, for example.

*******************************************************************/
import "farey_gamma0.m":  FareySequenceForGamma0N,
			  FareySequenceForGammaUpper0N;
import "farey_gamma1.m":  FareySequenceForGamma1N,
                          FareySequenceForGammaUpper1N;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    Attribute declarations                      //
//                                                                // 
////////////////////////////////////////////////////////////////////

declare type SymFry;

declare attributes SymFry:
   labels,  // sequence of integers, which identify edges
            // between cusps, or are integers -2 or -3
            // for self paired edges. 
   cusps,   // sequence of cusps, starting and ending with infinity
   generators,  // sequence of matrices generating corresponding
                 // group, assuming computed
   cosets,    // coset reps for group.
//   gen_edges,   // each generator corresponds to a pair of
//                // edges; this gives the pair for each generator
   otherEdges,   // sequence of `other edges', used for drawing
   widths,       // width sequence of cusp list.
   group;   // congruence subgroup, if computed


/////////////////////////////////////////
//                                     // 
//    Creation function                // 
//                                     //
/////////////////////////////////////////

forward FindWidths;

function init_farey_seq(farey_seq,farey_labels,gens) 
    /* The basic internal creation function. */
    FS := HackobjCreateRaw(SymFry); 
    FS`labels := farey_labels;
    FS`cusps := farey_seq;
    FS`generators := gens;
    return FS;
end function; 

// have to take edges e1, e2 to be sequences of
// two integers
function IsFareyPair(e1,e2)
    error if not Type(e1) eq SeqEnum and
    Type(e2) eq SeqEnum and
    #e1 eq 2 and #e2 eq 2 and
    Universe(e1) eq Integers() and
    Universe(e2) eq Integers(),
    "this function's input should be two pairs of integers";
    return (e1[2]*e2[1] - e1[1]*e2[2]) eq 1;
end  function;

// this function checks an edge is in the format of a
// sequence of length 6
function IsFareyEdge(e)
    return (Type(e) eq SeqEnum) and #e eq 6 and
    Universe(e) eq Integers() and
    IsFareyPair([e[1],e[2]],[e[3],e[4]]);    
end function;

function Mat(e : PSL:=PSL2(Integers()) )
    // this gives the matrix corrsponding to an edge
    a1, a2, b1, b2, dum1, dum2:= Explode(e);
    return PSL![b1,a1,b2,a2];    
end function;


function EdgeJoinMatrix(group,M1,M1a,M2)
    // e1, e2 are integer sequences length 6, 
    // as used in function below.
    // should verify that e1, e2 are edges in a Farey sequence.
    // especially, we _always_ need end points of edges to be in 
    // increasing order.
    // returns a type which is 0 or else -2 or -3 for
    // self linked edges

    // TO DO:
    // this function will be modified, so it's fed the matrices
    // rather than the edges.
    // also, we will have premultiplied the first matrix,
    // corresponding to e1, by [0,-1,1,0]
//    error if not IsFareyEdge(e1) and IsFareyEdge(e2),
//	"e1 and e2 should denote edges in a Farey Sequence";
  	
    type := 0;
    
    matrix := M2*M1a;
    
    if M1 eq M2 then
	if not matrix in group then
	    PSL := PSL2(Integers());
	    M := PSL![1,0,1,1]; 
	    matrix := M2*M*M1a;
	    type := -3;
	else
	    type := -2;
	end if;
    end if;
    
    return matrix, type;
end function;

// some functions on Farey edges defined as sequences of
// length 6

// this procedure sets the label flags to denote that edges
// e and f are joined.
// i will be the Index of e in some list, and
// j this index of f in the same list.
procedure SetLink(~e,~f,i,j,label)    
    e[5]:=j;
    f[5]:=i;
    e[6]:=label;
    f[6]:=label;
end procedure;

function NotLinked(e)
    return e[6] eq 0 or e[6] eq -4;
end function;


function NotBoundary(e)
    return not (e[6] eq -4);
end function;

function AllEdgesLinked(L);
    // this function is to check whether there's anything
    // left to do in the
    ends:=[e[6] : e in L];
    return not (0 in ends);    
end function;

function BoundariesGlued(L)
    ends:=[e[6] : e in L];
    return not (-4 in ends);    
end function;
    

procedure UnGlueFirstBoundary(~L);
    ends := [e[6] : e in L];
    i := Index(ends,-4);
    if i ne 0 then
	L[i][6] := 0;
    end if;
end procedure;


procedure Update(~L,i,j,e,f)
    L[j]:=f;
    L[i]:=e;
end procedure;

// the following function tests whether the edge
// e links to something in the list of edges L,
// under the action of some matrix in group
// if it does, then it returns true, the index
// of the edge in L that e is linked to
// and the matrix joining the edges
// the type is 0, unless the edge links to itself,
// in which case it's given by -order of the linking matrix
function CanLink(group,L,e : PSL:=PSL2(Integers()) )
//    mat is the matrix corresponding to e;
    linksto := false;
    linkfound := false;
    j:= 0;
    matrix := group`MatrixGroup!1;
    M := PSL![0,-1,1,0];
    mat := Mat(e : PSL:=PSL);
    mate := M*(mat)^(-1);
    
    while not linkfound and j lt #L do
	j +:= 1;
	f := L[j];
	matf := Mat(f : PSL:=PSL);
	if NotLinked(f) then
	    matrix, type := EdgeJoinMatrix(group,mat,mate,matf);
	    linkfound :=  matrix in group;
	end if;
    end while;
    if not linkfound then matrix:=PSL!1; end if;
    return linkfound, j, group!matrix, type;
end function;


// the following makes an edge as a sequence of 6
// integers, given two end points which must be
// cusps, and a label to say whether the edge must
// be a boundary or not
function MakeEdge(X,boundary)
    a,b := Explode(Eltseq(X[1]));
    c,d := Explode(Eltseq(X[2]));
    error if a le 0 and b le 0 and c le 0 and d le 0,
	"Cusps need to be quotients of positive integers";
    // need a staring -infinity
    if b eq 0 then a := -1; end if;
    error if not IsFareyPair([a,b],[c,d]), "pair of edges
	must be a Farey pair";
    bound := 0;	
    if boundary then bound := -4; end if;
    return [a,b,c,d,0,bound];
end function;


// the following sets the type of the ith edge in the
// list L to -5, to indicate that it's an internal edge
procedure internal(~L,~e,i)
    e[6] := -5;
    L[i] := e;
end procedure;


// the following will return the two egdes obtained when we
// extend the farey sequence along a particular edge
function SplitEdge(e)
    error if not (Type(e) eq SeqEnum and Universe(e) eq Integers()),
	"an edge should be given by a sequence of 4 integers";
    u1:=e[1]+e[3];
    u2:=e[2]+e[4];    
    newedge1:=MakeEdge([[e[1],e[2]],[u1,u2]], false);
    newedge2:=MakeEdge([[u1,u2],[e[3],e[4]]], false);
    return newedge1, newedge2;
end function;



forward FareySequenceForPSL;
forward EdgeListToFareySymbol;
forward EdgeListToOtherEdges;
forward UpdateAttributes;

// each fundamental domain for Gamma_0(2) corresponds to some
// choice of 3 coset representatives; this gives them.

function CosetImages(matrix)
    PSL := PSL2(Integers());
    r := PSL![0,1,-1,1];
    return [matrix,matrix*r,matrix*r^2];
end function;

// need another coset rep map for -3 edges!!!!


intrinsic FareySymbol(group::GrpPSL2,restrictions::SeqEnum) -> SymFry
    {Computes the Farey Symbol of a congruence subgroup in PSL_2(Z).}

    Z := Integers();
    PSL := PSL2(Z);

    require group`BaseRing eq Z:
      "currently only implemented for subgroups of PSL_2(Z)";

    // case if already computed:
    if assigned group`FS_labels then
       FS := init_farey_seq(group`FS_cusps,
       group`FS_labels,group`FS_generators);
       FS`group := group;
//       FS`gen_edges  := group`FS_gen_edges;
       FS`cosets := group`FS_cosets;
       if assigned group`FS_otherEdges then
	  FS`otherEdges := group`FS_otherEdges;
       end if;
       if assigned group`FS_widths then
	  FS`widths := group`FS_widths;
       end if;
       return FS;
    end if;
       
    // special cases:
    if IsGamma0(group) then
       return FareySequenceForGamma0N(group);
    end if;

    if IsGammaUpper0(group) then
       return FareySequenceForGammaUpper0N(group);
    end if;
    
    if IsGamma1(group) then
       return FareySequenceForGamma1N(group);
    end if;
    
    if IsGammaUpper1(group) then
       return FareySequenceForGammaUpper1N(group);
    end if;

    N,M,P:= Explode(CongruenceIndices(group)[1]);
    if P eq 1 and M eq N and (not assigned group`subgroup_list) then
       return FareySequenceForGamma1N(group);
    elif N eq 1 and M eq P and (not assigned group`subgroup_list) then
       return FareySequenceForGammaUpper1N(group);
    end if;
       
    // assume for now the index is at least 2,
    // need to change this, as currently won't work in that case
    // (this case does not yet come up though)
    
    boundary := true;
    edge1 := MakeEdge([Cusps()|Infinity(),0],boundary); // -infinity to 0
    edge2 := MakeEdge([Cusps()|0,1],     not boundary);	// 0 to 1        
    edge3 := MakeEdge([Cusps()|1,Infinity()], boundary);// 1 to +infinity
    L := [edge1,edge2,edge3];
    
    generators := [];
    gen_edges := [];
    cosets := [];
    // check if the ends link to each other:
    
    edgepair := 1;
    T := PSL![1,1,0,1];

    if T in group then
	SetLink(~L[1],~L[3],1,3,1);
	edgepair:=2;
	Append(~generators,group!T);
	Append(~gen_edges,[1,3]);
    end if;

    // following assumes index is not 2:
    cosets := CosetImages(PSL!1);
        
    finished := false;
    i := 2;			

    while not finished do
	e := L[i];
	mat := Mat(e : PSL:=PSL);
	if NotLinked(e) and NotBoundary(e) then  
	    linksto,j,matrix,type := CanLink(group,L,e : PSL:=PSL);
	    if linksto then
		f := L[j];
		if type eq 0 then
		    SetLink(~e,~f,i,j,edgepair);
		    edgepair +:=1;
		else
		    SetLink(~e,~f,i,j,type);
		end if;
		Update(~L,i,j,e,f);
		Append(~generators,matrix);		
		Append(~gen_edges,[i,j]);
		if type eq -3 then
		    Append(~cosets,mat);
		end if;
	    else		
		newedge1, newedge2 := SplitEdge(e);
		internal(~L,~e,i);
		Append(~L,newedge1);
		Append(~L,newedge2);
		newcosets := CosetImages(mat);
		// why doesn't cat work here?????
//		cosets := cosets cat newcosets;
		Append(~cosets,newcosets[1]);
		Append(~cosets,newcosets[2]);
		Append(~cosets,newcosets[3]);
	    end if;
	end if;
	if AllEdgesLinked(L) then
	    if BoundariesGlued(L) then
		finished := true;
	    else
		UnGlueFirstBoundary(~L);
		i := 1;
	    end if;
	end if;
	i +:=1;
    end while;
    
    fareysymbol:= EdgeListToFareySymbol(L);
    otheredges := EdgeListToOtherEdges(L);

    farey_seq:=
    [Cusps()!Infinity()]
    cat [Cusps()!z : z in fareysymbol[1]]
    cat [Cusps()!Infinity()];
    fareylabels := [Integers()| f : f in fareysymbol[2]];
    FS := init_farey_seq(farey_seq,fareylabels,generators);
    FS`group := group;
    FS`cosets := cosets;
    FS`otherEdges := otheredges;
    UpdateAttributes(group,FS);
    return FS;
end intrinsic;


intrinsic FareySymbol(group::GrpPSL2) -> SymFry
   {Computes the Farey Symbol of a congruence subgroup in
    PSL_2(Z).}
    // if a farey sequence is already found, don't recompute;
    // however, we would like to add a function to recompute
    // if wished.

    if assigned group`FS_labels then
       FS := init_farey_seq(group`FS_cusps,
       group`FS_labels,group`FS_generators);
       FS`group := group;
//       FS`gen_edges  := group`FS_gen_edges;
       FS`cosets := group`FS_cosets;
       if assigned group`FS_otherEdges then
	  FS`otherEdges := group`FS_otherEdges;
       end if;
       if assigned group`FS_widths then
	  FS`widths := group`FS_widths;
       end if;
       return FS;
    else
	return FareySymbol(group,[]);
    end if;    
end intrinsic;
    
// the following produces a Farey symbol from the list of
// edges indictively constructed while finding the group,

function EdgeListToFareySymbol(L)

    L1:=[e : e in L | e[6] ne -5 and e[2] ne 0];

    // WARNING, for the following to work, we assume
    // that all the end
    // points of edges are positive numbers!
    
    endpoint:=func<x, y | x[1]*y[2] - y[1]*x[2]>;
    L2:=Sort(L1,endpoint);
    cusps:=[x[1]/x[2] : x in L2];
    end1:=[e : e in L | e[2] eq 0][1];
    end2:=[e : e in L | e[4] eq 0][1];
    
    matchings:=[end1[6]];
    for e in L2 do 
	Append(~matchings,e[6]);
    end for;
    
    return [cusps,matchings];
end function;


// the following constructs the "other" edges than those on
// the boundary of the domain - so this is a complement to the
// function EdgeListToFareySymbol(L)

// WARNING, for the following to work, we assume that all the end
// points of edges are positive numbers!

function EdgeListToOtherEdges(L)
    L1:=[[Cusps()|[e[1],e[2]],[e[3],e[4]]] : e in L | e[6] eq -5];
    return L1;
end function;


function verifyGeneralisedFarey(v)
    error if not Parent(v) eq SeqEnum or
	not Universe(v) eq Rationals(),
	"must provide a sequence of rationals";
    
    length:=#v;
    if length lt 1 then return false; 
    end if;
    
    if not 0 in v then return false; 
    end if;
    
    if Denominator(v[1]) ne 1 then return false; 
    end if;
    
    if Denominator(v[length]) ne 1 then return false; 
    end if;
    
    i:=1;
    foundError:=false;
    while i lt length and not foundError do
	a1:=Numerator(v[i]);
	b1:=Denominator(v[i]);
	a2:=Numerator(v[i+1]);
	b2:=Denominator(v[i+1]);
	if a2*b1-a1*b2 ne 1 then foundError:=true; end if;
	i:=i+1;
    end while;
    
    return not foundError;
end function;


//////////////////////////////////
//
//
//    Update Attributes of the group after computation of
//    Farey symbol
//
///////////////////////////////////////

procedure UpdateAttributes(group,FS)
    group`FS_labels     := FS`labels     ;
    group`FS_cusps      := FS`cusps      ;
    group`FS_generators := FS`generators ;
//    group`FS_gen_edges  := FS`gen_edges  ;
    group`FS_cosets     := FS`cosets     ;
    if assigned FS`otherEdges then
       group`FS_otherEdges := FS`otherEdges ;
    end if;
    if assigned FS`widths then
       group`FS_widths   := FS`widths;
    end if;
 end procedure;
    
//////////////////////////////////
//
//   check that a Farey Symbol consists of a gFS, 
//   and a list of symbols.. -2 means point order 2
//                           -3 means point order 3
//   apart from this, integers come in pairs.
//
//   the infinitys should be left off the list of rationals.
//
//////////////////////////////////

function verifyFareySymbol(vw)
    error if not Parent(vw) eq SeqEnum or
	#vw ne 2, "must give 2 sequences of rationals";	
    v:=vw[1];
    w:=vw[2];
    error if not Parent(v) eq SeqEnum or
	not Universe(v) eq Rationals(),
	"must give 2 sequences of rationals";	

    
    if #v + 1 ne #w then return false;
    end if;
    
    sv:=Sort(v);
    if sv[1] lt -3 then return false; end if; 
    if -1 in sv[1] then return false; end if; 
    if 0 in sv[1] then return false; end if; 
    
    subv:=[i : i in sv | i gt 0];
    if 2*#Set(subv) ne #subv then return false; end if;
    
    return verifyGeneralisedFarey(v);
end function;


///////////////////////////////////
//    Widths                     //
//                               //
///////////////////////////////////

function FindWidths(cusps,labels,extra);
    // the widths are for the cusps starting with
    // infinity, but not counting the width of the
    // last infinity a second time.
    // This function returns 2 times the widths, so
    // as to return and integer sequence.
    widths := [2 : i in [1..#cusps]];
    widths[1] := 0;
    for i := 1 to #labels do
	a := labels[i];
	if a eq -3 then
	    widths[i] -:=1;
	    widths[i+1] -:=1;
	end if;
    end for;
    // since there is as yet no equality testing for
    // cusps, create "cuspsE"
    cuspsE := [Eltseq(c) : c in cusps];
    for a in extra do
	widths[Index(cuspsE,Eltseq(a[1]))] +:=2;
	widths[Index(cuspsE,Eltseq(a[2]))] +:=2;
    end for;
    widths[1] +:=widths[#widths];
    widths[#widths] := widths[1];
    return widths;
end function;


/////////////////////////////////////////
//                                     // 
//    Printing function                // 
//                                     //
/////////////////////////////////////////

function spaces(N)
    // return a string of N spaces
    return &cat[" " : i in [1..N]];
end function;


intrinsic HackobjPrintSymFry(FS::SymFry, level::MonStgElt)
    {}

    cuspString := "[ oo, " cat
    &cat[Sprintf("%o, ",c) : c in FS`cusps | c ne Cusps()!Infinity()]
    cat "oo ]";
    printf "%o\n%o", FS`labels,cuspString;
    
    // for another level, perhaps:
    if false then
    cuspsString := "[ ";
    labelString := "[  ";
    cusps := FS`cusps;
    labels := FS`labels;
    for i := 1 to #cusps-1 do
	c := Sprintf("%o",cusps[i]);
	cuspsString := cuspsString cat c cat ", ";
	labelString := labelString cat spaces(#c);
	d := Sprintf("%o",labels[i]);
	labelString := labelString cat d;
	if i ne #cusps -1 then
	    labelString := labelString  cat ", ";
	end if;
	cuspsString := cuspsString cat spaces(#d);	
    end for;
    labelString := labelString cat "    ]";
    cuspsString := cuspsString cat "oo ]";

    printf "%o\n%o", labelString,cuspsString;
    end if;
end intrinsic;


/////////////////////////////////////////
//                                     // 
//    Access functions                 // 
//                                     //
/////////////////////////////////////////


intrinsic Cusps(FS::SymFry) -> SeqEnum
    {Returns the list of cusps of a Farey Symbol}
    return FS`cusps;
end intrinsic;

intrinsic Labels(FS::SymFry) -> SeqEnum
    {Returns the list of edge labels of a Farey Sequence}
    return FS`labels;
end intrinsic;


intrinsic Generators(FS::SymFry) -> SeqEnum
    {Returns the generators of the congruence subgroup
    corresponding to the Farey Symbol}
     if Type(FS`generators[1]) ne GrpPSL2Elt then
	FS`generators := [FS`group | x : x in FS`generators];
     end if;
    return FS`generators;
end intrinsic;


intrinsic Group(FS::SymFry) -> GrpPSL2
    {Returns the congruence subgroup corresponding to
    the Farey Symbol FS}
    return FS`group;
end intrinsic;



function MakeOtherEdges(Cusps,Labels);
   otheredges := [];
   for i in [2..(#Cusps-1)] do
      if i eq 2 then fudge:=1;
      else fudge:=0;
      end if;
      if Labels[i] eq -3 then
	 Append (~otheredges,[Cusps[i],Cusps[i+1]]);
      end if;
      ei := Eltseq(Cusps[i]);
      for j := i + 2 to #Cusps - fudge do
	 ej := Eltseq(Cusps[j]);
	 if ej[1]*ei[2] - ej[2]*ei[1] eq 1 then
	    Append(~otheredges,[Cusps[i],Cusps[j]]);
	 end if;
      end for;
   end for;
   return otheredges;
end function;



intrinsic Widths(FS::SymFry) -> SeqEnum
   {Returns the widths of the cusp list of the Farey Symbol}
   if assigned FS`widths then
      return FS`widths;
   else
      if not assigned FS`otherEdges then
	 FS`otherEdges := MakeOtherEdges(FS`cusps,FS`labels);
	 FS`group`FS_otherEdges := FS`otherEdges;
      end if;
      FS`widths := FindWidths(FS`cusps,FS`labels,FS`otherEdges);
      return FS`widths;
   end if;
end intrinsic;

intrinsic CosetRepresentatives(FS::SymFry) -> SeqEnum
   {Returns the coset representatives for the congruence subgroup
   of the Farey Symbol in PSL_2(z)}
   if Type(FS`cosets[1]) ne GrpPSL2Elt then
      P := PSL2(Integers());
      FS`cosets := [P | x : x in FS`cosets];
   end if;
   return FS`cosets;
end intrinsic;


intrinsic InternalEdges(FS::SymFry) -> SeqEnum
   {Returns a sequence of pairs of cusps which are cusps of the Farey
   Symbol FS, and which are  not adjacent in FS but which are images of
   0 and infinity under some matrix in PSL_2(Z).}
   if assigned FS`otherEdges then
      return FS`otherEdges;
   end if;
   FS`otherEdges := MakeOtherEdges(FS`cusps,FS`labels);
   return FS`otherEdges;
end intrinsic;

intrinsic FundamentalDomain(FS::SymFry) -> SeqEnum
    {returns a sequence of points in the upperhalf plane union
    cusps, such that the geodesics between these points form the
    boundary of a fundamental domain for the group corresponding
       to the Farey symbol FS.}
    cusps := FS`cusps;
    labels := FS`labels;
    polygon :=[];
    H := UpperHalfPlaneWithCusps();
    P := PSL2(Integers());
    for i:=1 to #cusps do
	Append(~polygon,H!cusps[i]);
	if i le #labels and labels[i] eq -3 then
	    x := Eltseq(cusps[i]);
	    y := Eltseq(cusps[i+1]);
	    M := P![y[1],x[1],y[2],x[2]];
	    Append(~polygon,M*H.2);
	end if;
    end for;
    return polygon;
end intrinsic;


/////////////////////////////////////////
//                                     // 
//    Arithmetic                       // 
//                                     //
/////////////////////////////////////////

intrinsic Index(FS::SymFry) -> RngIntElt
    {returns the index in PSL2(Z)
    of the congruence subgroup corresponding to the
    Farey Symbol FS}
    labels := FS`labels;
    return 3*#labels - 6 + #[i : i in labels | i eq -3];
end intrinsic;














