//sharbly.m  4/27/2009

freeze;

import "defs.m":
    ZeroSharblyRec;
import "defs.m":
    CellRec;
import "hecke.m":Mab;

import "compute.m" : hermitian_to_fat, q, minimal_vectors;

import "srd_reduce.m" : srd_reduce;


MaximalOrder := Integers; // faster calling sequence

Q := RationalField();


function star(M)
    c:=NumberOfRows(M);
    return Matrix(c,[Trace(e)-e : e in Eltseq(Transpose(M))]);
end function;


function is_isomorphic(A,B)
    RA,TA:=LLLGram(A[1] : Delta:=0.999); IA:=TA*A[2]*Transpose(TA);
    RB,TB:=LLLGram(B[1] : Delta:=0.999); IB:=TB*B[2]*Transpose(TB);
    tf,g0 := IsIsomorphic([RA,IA],[RB,IB]);
    if tf then
	g := TB^-1*g0*TA;
    else
	g := Parent(RA)!0;
    end if;
    return tf,g;
end function;


function IsGLConj(F,OF,A,B)
    // return Boolean and g such that gAg^* = B, if g exists.
    // Otherwise g = 0.
    RA,IA := Explode(hermitian_to_fat(A));
    RB,IB := Explode(hermitian_to_fat(B));
    rA:=Lcm([Denominator(x) : x in Eltseq(RA)]);
    RA:=ChangeRing(RA*rA,Integers()); 
    iA:=Lcm([Denominator(x) : x in Eltseq(IA)]);
    IA:=ChangeRing(IA*iA,Integers());
    rB:=Lcm([Denominator(x) : x in Eltseq(RB)]);
    RB:=ChangeRing(RB*rB,Integers()); 
    iB:=Lcm([Denominator(x) : x in Eltseq(IB)]);
    IB:=ChangeRing(IB*iB,Integers());
    tf,g0 :=  is_isomorphic([RA,IA],[RB,IB]);
    w := F!(OF.2);
    cw := F`Conjugate(w);
    g := ZeroMatrix(F,2,2);
    if tf then
	for i,j in [1..2] do
	    g[i][j]:=g0[i][j]+g0[i][j + 2]*cw;
	end for;
	BB :=  g*A*star(g);
	assert BB eq B;
    end if;
    return tf,g;
end function;


function is_strongly_reduced_proc(M,s)
    //degenerate sharblies are returned as strongly reduced but GL_type = 0
    shar:=s;
    if not assigned shar`is_strongly_reduced then
	if Determinant(Matrix(shar`O2_vertices)) eq 0 then
	    shar`is_strongly_reduced:=true;
	    shar`GL_type:=0;
	else
            F:=M`Field;
            OF:=Integers(F);
	    onepolys:=M`ModFrmData`one_poly;
	    tf:=exists(type){i:i in [1..#onepolys]|
		IsGLConj(F,OF,onepolys[i]`bary,shar`bary)};
	    if tf then
		shar`is_strongly_reduced:=true;
		shar`GL_type:=type;
	    else
		shar`is_strongly_reduced:=false;
	    end if;
	end if;
    end if;
    return shar;
end function;

forward barycenter;
forward vertices_containing;

function is_voronoi_reduced_proc(M,s)
    //degenerate sharblies are returned as voronoi reduced but GL_type = 0
    //This checks whether a sharbly is Voronoi reduced by checking
    //whether the barycenter is in the cone defining the edge.
    //if true, then attaches
    //if not assigned shar`is_voronoi_reduced then computes
    shar:=s;
    D:=Determinant(Matrix(shar`O2_vertices)) ;
    L:=M`ModFrmData`dets;
    if D eq 0 then
	shar`is_voronoi_reduced:=true;
	shar`GL_type:=0;
    elif D in L then  
	b:=barycenter(shar);
	//the vertices of the top cone containing as cell record;
	T:=vertices_containing(M,b);
	
	vprintf Bianchi,4 :"The cell containing the barycenter %o is %o.\n",b,T;
	v:=shar`vertices;
	tf:=v[1] in T`cone_vertices and v[2] in T`cone_vertices;
	shar`is_voronoi_reduced:=tf;
	if tf then 
	    shar`containing_cell:=T;
	end if;
    else
	//It should only get here if the above case did not apply.
	shar`is_voronoi_reduced:=false;
    end if;
    return shar;
end function;

   
function MakeSharbly(M,ov,c:v:=[ToBianchiCone(BaseField(M),a):a in ov],is_voronoi_reduced:=0,strong_reduce:=true)
    //creates 0-sharbly record.
    qM := [q(v) : v in ov];
    bary := &+qM;
    shar:=rec<ZeroSharblyRec|vertices:=v,O2_vertices:=ov,coefficient:=c,is_voronoi_reduced:=is_voronoi_reduced, bary := bary>;
    if shar`is_voronoi_reduced cmpeq 0 then 
	shar:=is_voronoi_reduced_proc(M,shar);
    end if;
if strong_reduce then
    if  shar`is_voronoi_reduced then 
	shar:=is_strongly_reduced_proc(M,shar);
    else
	shar`is_strongly_reduced:=false;
    end if;
end if;
    return shar;
end function;

function barycenter(s)
    return &+[Vector(a): a in s`vertices];
end function;

function badness(v,cand)
    //given vertices v and candidate reducing point cand, computes how bad
    //the choice of reducing point is.  Currently uses norm determinant,
    //but better one should be available.
    L:=[Norm(Determinant(Matrix([a,cand]))):a in v];
    vprintf Bianchi,2:"Badness is %o.\n",L;
    return Maximum(L);
    
end function;

function choose_smart(M,s,T,shar_in_T)
    //when one or both ov the sharbly vertices are in the cone containing the
    //barycenter, we should choose the reducing point carefully.
    //cand is a list of indices of T`cone_vertices that are not vertices of s
    vprintf Bianchi,2:"Trying to choose wisely %o.\n", shar_in_T;
    if shar_in_T[1] eq 0 then
	//first vertex of s is out of T.
	no_good:=shar_in_T[2];
	tf:=exists(bestone)
	    {j:j in [1..#T`O2_vertices]|
	not j eq no_good and
	MakeSharbly(M,[s`O2_vertices[1],T`O2_vertices[j]],
	    s`coefficient:v:=[s`vertices[1],T`cone_vertices[j]],strong_reduce:=false)`is_voronoi_reduced};
    else
	assert shar_in_T[2] eq 0;
	//second vertex of s is out of T
	no_good:=shar_in_T[1];
	tf:=exists(bestone)
	    {j:j in [1..#T`O2_vertices]|
	not j eq no_good and
	MakeSharbly(M,[T`O2_vertices[j],s`O2_vertices[2]],
	    s`coefficient:v:=[T`cone_vertices[j],s`vertices[2]],strong_reduce:=false)`is_voronoi_reduced};
    end if;
    if tf then
	vprintf Bianchi,2:"You chose wisely %o.\n",bestone;
	return bestone;
    else
	ind := [ i :  i in [1..#T`O2_vertices]|not i in shar_in_T]; 
	B:=[ badness(s`O2_vertices,T`O2_vertices[i]): i in [1..#T`O2_vertices]|not i in shar_in_T ];  
	vprintf Bianchi,2: "badness of candidates = %o.\n",B;
	_,bestind:=Minimum(B);
	return ind[bestind];
    end if;
end function;

function reducing_point(M,s,T)
    //Given 0-sharbly s and cell containing vertex T, returns a choice of
    //reducing point and O2 version.

    shar_in_T:=[Position(T`cone_vertices,a):a in s`vertices];
    if shar_in_T ne [0,0] then 
	bestone:=choose_smart(M,s,T,shar_in_T);
    else
	B:=[badness(s`O2_vertices,a): a in T`O2_vertices];
	_,bestone:=Minimum(B);
    end if;
    
    rp :=T`cone_vertices[bestone];
    orp:=T`O2_vertices[bestone];
    vprintf Bianchi,4: "Choosing reducing point  for %o.\n",<s`vertices,s`O2_vertices>;
    vprintf Bianchi,4: "  Chose reducing point %o.\n",<rp,orp>;
    return rp, orp;
end function;

/*************************************************************************

function flip(F,nx)
    //assumes nx is normalized so that bottom right is 1.
    O:=MaximalOrder(F);
    assert nx[4] eq 1;
    vprint Bianchi, 4:"Flip";
    B:=BasisMatrix(O);
    b:=Vector(Eltseq(F!(-F`Conjugate(nx[2]*O.1+nx[3]*O.2)/nx[1])))*B^(-1);
    return [1/nx[1],b[1] ,b[2] ,1],Matrix(O,2,[0,-1,1,0]);
end function;

function close(F,beta)
    //returns integer n that is close to beta
    O:=MaximalOrder(F);
    B:=BasisMatrix(O);
    v:=Vector(Eltseq(F!beta) )*B^(-1);
    n:=O![Round(v[1]),Round(v[2])];
    return n;
end function;

function translate(F,nx)
    //assumes x is normalized so that bottom right is 1.
    vprint Bianchi, 4:"Translate.";
    assert nx[4] eq 1;
    O:=MaximalOrder(F);
    B:=Basis(O);
    beta:=B[1]*nx[2]+B[2]*nx[3];
    n:=-close(F,beta);
    a:=RationalField()!(nx[1]+F`Conjugate(beta)*n+beta*F`Conjugate(n)+n*F`Conjugate(n));
    N:=Matrix(O,2,[1,n,0,1]);
    vprintf Bianchi, 4:"Translate using %o.", N;
    return [a,nx[2]+n[1],nx[3]+n[2],1],N;
end function;
    
function centered(F,nx)
    //need to think about this;
    //assumes nx is normalized so that bottom right is 1.
    if Abs(nx[1]) lt 1 then 	
	return false;
    elif Abs(nx[2]) gt 1 or Abs(nx[3]) gt 1 then
	return false;
    end if;
    
    return true;//if it gets here it passed both tests
end function;

function choose_crude(F,nx)
    // assumes nx is normalized so that bottom right is 1 and nx is not
    //centered and choice must be made  i.e function centered has been called.
    if Abs(nx[1]) lt 1 then 	
	new_x,gamma:=flip(F,nx);
    else
	new_x,gamma:=translate(F,nx);
    end if;
    return new_x,gamma;    
end function;

function crude_move(F,x);
    O:=MaximalOrder(F);
    mover:=Matrix(MaximalOrder(F),2,[1,0,0,1]);
    nx:=[x[1]/x[4],x[2]/x[4],x[3]/x[4],1];
//    while false do
    while not centered(F,nx) do
	nx,gamma:=choose_crude(F,nx);
	mover:=gamma*mover;
    end while;
    vprintf Bianchi, 3:"Centered point %o using unipotent translation and flip to %o using mover = %o.\n",x,nx,mover; 
    return nx,mover;
end function;

*************************************************************************/

declare attributes ModFrmBianchi : vertices_containing_cache;
    
function vertices_containing(M,xx)
    //Given a vector x in the cone, and the three-cells, returns the cell
    //representing the top cone containing x
    //Uses Gunnells

    F    := BaseField(M);
    O    := MaximalOrder(F);
    FOF  := FieldOfFractions(O);
    conj := F`Conjugate;

    function act_on_cone(g, h)
        gstar := Transpose(Matrix(2, [F| conj(x) : x in Eltseq(g)]));
        beta := h[2]*O.1 + h[3]*O.2;
        mat := Matrix(2, [F| h[1], beta, conj(beta), h[4]]);
        gh := g * mat * gstar;
        b := Eltseq(FOF! gh[1,2]);
        return [Q| gh[1,1], b[1], b[2], gh[2,2]];
    end function;

    /*
    //First do crude [[1,n],[0,1]] and [[0,-1],[1,0]] to get centered
    // printf "CRUDE: %o\t ", xx;
    new_x,mover:=crude_move(F,xx);
    // print [d*x : x in new_x] where d := LCM([Denominator(x) : x in new_x]); 
    */

    // This replaces the crude move
    // November 2013, SRD

    prec := 100 + Ilog(10, &*[1+Norm(O!(a*Denominator(a))) : a in Eltseq(xx)]); // TO DO
    RR := RealField(prec);
    assert O.1 eq 1;
    w := Conjugate(O.2, 1 : Precision:=prec);
    BL := Matrix(2, [RR| 1, 0, Re(w), Im(w)]);

    // printf "SRD: %o\t ", xx;
    beta := xx[2]*O.1 + xx[3]*O.2;
    h    := Matrix(2, [F| xx[1], beta, conj(beta), xx[4]]);
    hr, mover := srd_reduce(h, O, BL);
    b := Eltseq(O! hr[1,2]);
    new_x := [Q| hr[1,1], b[1], b[2], hr[2,2]];
    // print new_x;
    // assert new_x eq act_on_cone(mover, xx);

    // The same nearly-reduced vectors occur repeatedly here
    // (should be a fixed set, not too big, depending only on F)
    // so store the results of the next bit
    // SRD, Dec 2013

    bool, cache := HasAttribute(M, "vertices_containing_cache");
    if not bool then
        M`vertices_containing_cache := AssociativeArray(); 
    else
        bool, tup := IsDefined(cache, new_x);
    end if;

    if bool then
//printf ".";
        mover1, newcone_index := Explode(tup);
    else
        new_x0 := new_x;
        mover1 := Parent(mover) ! 1;

        three := M`ModFrmData`three_poly;
        C     := M`ModFrmData`cone_space;
        newcone_index := 1;
        while true do
            std_cone := three[newcone_index];
            yF := std_cone`form;
            new_x_C := C! new_x;
            mu := (new_x_C, C! yF);
            neighbor_ip := [(new_x_C, C! n`form) : n in std_cone`neighbors];
            // vprintf Bianchi, 3: "  mu=%o.\n",mu;
            // vprintf Bianchi, 3: "neighbor_ip=%o.\n",neighbor_ip;
            newmu, neighbor_index := Minimum(neighbor_ip);
            if mu le newmu then
                break;
            end if;
            newcone_index := std_cone`neighbors_mover[neighbor_index][1];
            gamma         := std_cone`neighbors_mover[neighbor_index][2];
            mover1 := gamma * mover1;
	    new_x  := act_on_cone(gamma, new_x);
        end while;

        M`vertices_containing_cache[new_x0] := < mover1, newcone_index >;
//printf "[%o]", #Keys(M`vertices_containing_cache);
    end if;

    mover := mover1 * mover;

    // Final step depends on original xx
    three:=M`ModFrmData`three_poly;
    stdvecs:=[Vector(O,a) : a in three[newcone_index]`O2_vertices];
    g:=Matrix(O,mover^(-1));
    tg := Transpose(g);
    Tov := [v*tg : v in stdvecs];
    Tv:=[ToBianchiCone(F,v):v in Tov];
    //needs to be a cell.  Only needs to have the data of O2 vectors and
    //cone vectors.
    T:=rec<CellRec|
	O2_vertices:=Tov,
	cone_vertices:=Tv,
	GLtype:=newcone_index,
	mover:=g>;
    return T;
end function;
    
function split_sharbly(M,s,rp,orp)
    //Given sharbly s, and reducing point rp, orp, makes 2 0-sharblies
    //whose sum is homologous to s.
    c:=s`coefficient;
    v:=s`vertices;
    ov:=s`O2_vertices;
    v1:=[v[1],rp];
    ov1:=[ov[1],orp];
    v2:=[rp,v[2]];
    ov2:=[orp,ov[2]];
    return [MakeSharbly(M,ov1,c:v:=v1),MakeSharbly(M,ov2,c:v:=v2)];
end function;


forward strong_reduce; 

function ReduceSharbly(M,s)
    //1-step of the reduction algorithm acting on a single 0-sharbly,
    //takes as input the three_poly and a 0-sharbly s
    vprintf Bianchi,2: "Reducing badness %o.\n", 
                       Norm(Determinant(Matrix(s`O2_vertices)));
    b:=barycenter(s);
    //the vertices of the top cone containing as cell record;
    T:=vertices_containing(M,b);

    // fix from Dan 10/12/13
    if not s`vertices subset T`cone_vertices then
      rp,orp:=reducing_point(M,s,T);
      L:=split_sharbly(M,s,rp,orp);
      vprintf Bianchi,1: "Replace with badness %o.\n",
        [Norm(Determinant(Matrix(a`O2_vertices))): a in L];
    else
      s`containing_cell := T;
      L := strong_reduce(M,s);
    end if;

    return L;
end function;


function get_path_indices(G,s,e)
    //given polytope and start and ending vertices, returns the indices
    //of a path joining s and e
    V:=Vertices(G);
    sG:=V[s];
    eG:=V[e];
    geo:=Geodesic(sG,eG);
    geoZ:=[Index(a):a in geo];
    path:=[[geoZ[i],geoZ[i+1]]: i in [1..#geoZ-1]];
    return path;
end function;


function get_path(M,P,s)
    //Given a cell record and a 0-sharbly s contained in that cell,
    //returns a list of pairs <v,ov> on vectors defining the path from
    //the start of s to the end of s.
    vert:=P`cone_vertices;
    overt:=P`O2_vertices;
    //need to take into account that the polytope P
    //is a translate of the standard one.  The ordering of the
    //vertices matters.
    s_v:=s`vertices[1];
    e_v:=s`vertices[2];
    start_index:=Position(vert,s_v);
    end_index:=Position(vert,e_v);
    GLtype:=P`GLtype;
    stdpolygraph:=M`ModFrmData`three_poly[GLtype]`graph;
    I:=get_path_indices(stdpolygraph,start_index,end_index);
    //print <start_index,end_index,I>;
    return [<[vert[L[1]],vert[L[2]]],[overt[L[1]],overt[L[2]]]>:L in I];
end function;

function strong_reduce(M,s)
    //Assumes s is Voronoi reduced.  Returns a sum of strongly reduced
    //0-sharblies homologous to s by finding a path in the polytope.
    c:=s`coefficient;
    //assert s`is_voronoi_reduced;
    P:=s`containing_cell;
    L:=[];
    path:=get_path(M,P,s);//returns a list of pairs of pairs <v,ov>, where
    //v is the cone vertices defining the edge and ov are the o2 vertices>
    for p in path do
	v:=p[1];
	ov:=p[2];
	//s:=MakeSharbly(M,ov,c:v:=v,is_voronoi_reduced:=true);
	s:=MakeSharbly(M,ov,c:v:=v);
	Append(~L,s);
    end for;
    return L;
end function;

function FullReduce(M,s)
    //Calls ReduceSharbly until everything is Voronoi reduced.  Then calls
    //strong_reduce.
    ToDo:=[s];
    reduced:=[];
    while #ToDo ne 0 do
	vprintf Bianchi,2:"%o left to reduce.\n",#ToDo;
	vprintf Bianchi,2:"%o reduced ones found so far.\n",#reduced;
	a:=ToDo[1];
	if a`is_voronoi_reduced then
	    Remove(~ToDo,1);
	    Append(~reduced,a);
	else
	    Remove(~ToDo,1);
	    L:=ReduceSharbly(M,a);
	    
	    ToDo:=L cat ToDo;
	end if;
    end while;
    
    /*
    reducedgl:=[a:a in reduced| assigned a`GL_type];
    //delete degenerate 0-sharblies
    reducedgl:=[a:a in reducedgl|a`GL_type ne 0];
    reducednot:=[a:a in reduced|not assigned a`GL_type];
    strongreduced:=&cat[strong_reduce(M,a):a in reducedgl cat reducednot];
    */
    // SRD
    strongreduced := &cat [strong_reduce(M,a) : a in reduced |
                           not (assigned a`GL_type and a`GL_type eq 0)];
    return strongreduced;
end function;

function unimodularize(M,v)
    //return v; // don't need to do below.
    //  I think we need this to implement Cremona cusp boundary
    // technique.
	
    //O:=CoefficientRing(v);
    O:=Integers(BaseField(M));
    G,f:=ClassGroup(O);
    I:=ideal<O|v[1],v[2]>;
    GI:=I@@f;
    tf:=exists(stdrep){r :r in M`ModFrmData`ideal_reps|r@@f eq GI};
    _,d:=IsPrincipal(I/stdrep);
    return Vector([O|v[1]/d, v[2]/d]);    
end function;

 
function act_on_sharbly(M,g,s:mult:=1)
    //Compute the action of matrix g on sharbly s
    //mult scales coefficient
    ov:=s`O2_vertices;
    OF := Integers(M`Field);
    c:=s`coefficient * mult;
    newov:=[ Vector(OF,v)*Transpose(g):v in ov];
    // Do we really? Need to normalize these vectors
    //newov:=[unimodularize(M,v):v in newov];
    return MakeSharbly(M,newov, c);
end function;

procedure SetSharblies(M)
    //Sets standard 0-sharblies in the same order as one_poly with coefficient 1
    O:=MaximalOrder(BaseField(M));
    L:=[];
    ideals:=[];
    for i := 1 to #M`ModFrmData`one_poly do
        poly := M`ModFrmData`one_poly[i];
	ov:=poly`O2_vertices;
	if i in M`ModFrmData`zero_reversers then
	    ov:=Reverse(poly`O2_vertices);
	end if;

	for v in ov do
	    Include(~ideals,ideal<O|v[1],v[2]>);
	end for;
	
	vec:=poly`cone_vertices;
	c:=1;
	shar:=MakeSharbly(M,ov,c:v:=vec,is_voronoi_reduced:=true);
	Append(~L,shar);
    end for;
    M`ModFrmData`standard_sharblies:=L;
    //M`ModFrmData`ideal_reps:=ideals;
end procedure;
