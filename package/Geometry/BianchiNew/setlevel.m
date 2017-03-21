//setlevel.m

freeze;

import "defs.m":
    LevelRec,
    OrbitRec,
    HomologyRec;

import "../ModFrmHil/proj1.m": 
    ProjectiveLineOrbits;

function gamma_list(LO,proj,level)
    //Computes gamma_list;
    O:=Parent(proj[1,1]);
    gammalist:=[ ];
    //these take [0:1] to a0.  Given as a list, one for each Gamma0 type;
    for Gamma0type in [1..Maximum(LO)] do
	ind:=Position(LO, Gamma0type); //Is this guaranteed to be the first
	//occurence of Gamma0type in LO?
	//ind:=Minimum([i:i in [1..#LO]|LO[i] eq Gamma0type]);
	olda:=proj[ind];
	a:=olda;
	id := ideal<O|a[1],a[2]>;
	while id ne 1*O do
	    n := Random(Basis(level));
	    a:=[a[1]+n,a[2]];
	    id := ideal<O|a[1],a[2]>;
	end while;
	if a[1] eq 0 then
	    gamma:=Matrix([[O|1,0],[O|0,1]]);
	elif a[1] eq 1 then
	    gamma:=Matrix([[O|0,-1],[O|1,a[2]]]);
	else
	    I:=ideal<O|a[1]>;
	    J:=ideal<O|a[2]>;
	    tf,i,j:=Idempotents(I,J);
	    assert tf;
	    s:=O!(i/a[1]);
	    t:=O!(j/a[2]);
	    gamma:=Matrix([[O|t,-s],[O|a[1],a[2]]]);
	end if;
	gammalist[Gamma0type]:=gamma;
    end for;
    return gammalist;
end function;
    
function orbit_number_list(OT,F,cell,proj,proj_map)
    onumber:=[];
    OF := Integers(F);
    stabplus := [Matrix(OF,A) : A in cell`stabilizer_plus];
    for otype in [1..Maximum(OT)] do
	ind:=[i:i in [1..#proj]|OT[i] eq otype];
	a0:=proj[ind[1]];
	for i in ind do
	    b:=proj[i];
	    tf:=exists(g){g: g in stabplus | rep eq a0 
		             where _,rep:=proj_map(b*g,false,false)};
	    if tf then
		onumber[i]:=1;
	    else onumber[i]:=-1;
	    end if;
	end for;
	assert onumber[ind[1]] eq 1;
    end for;
    return onumber;
end function;

function non_orientable_orbits(OT,F,cell,proj,proj_map)
    no:=[];
    OF := Integers(F);
    stabplus := [Matrix(OF,A) : A in cell`stabilizer_plus];
    stab := [Matrix(OF,A) : A in cell`stabilizer];
    for otype in [1..Maximum(OT)] do
	ind:=[i:i in [1..#proj]|OT[i] eq otype];
	b:=proj[ind[1]];
	S:=[g:g in stab | g notin stabplus ];
	tf:=exists(g){g: g in S| rep eq b
		         where _,rep:=proj_map(b*g,false,false)};
	if tf then Append(~no,otype); end if;
    end for;
    return no;
end function;

function brm(M,g)
    O:=Integers(BaseField(M));
    proj:=M`LevelData`projective_space;
    proj_map:=M`LevelData`projective_space_map;
    v:=[O | g[2,1],g[2,2]];
    _,nv:=proj_map(v,false,false);
    ans:=Position(proj,nv);
    return ans;
end function;

function GetOrbits(M,polydim)
    vprintf Bianchi,2:"Computing %o-dimensional cell orbits.\n",polydim;
    F:=BaseField(M);
    OF := Integers(F);
    levelrec:=M`LevelData;
    total:=[];
    level:=Level(M);
    if polydim eq 3 then
	std:=M`ModFrmData`three_poly;
    elif
	polydim eq 2 then
	std:=M`ModFrmData`two_poly;
    elif
	polydim eq 1 then
	std:=M`ModFrmData`one_poly;
    end if;
    proj:=levelrec`projective_space;
    proj_map:=levelrec`projective_space_map;
    rF:=levelrec`rF;
    base:=0;
    for cell in std do
	Stab:=[Matrix(OF,A) : A in cell`stabilizer];
	orbitrec:=rec<OrbitRec|>;
	orbitrec`orbit_type:=ProjectiveLineOrbits(Stab,proj,proj_map);
	orbitrec`total_number:=Maximum(orbitrec`orbit_type);
	orbitrec`gamma_list:=gamma_list(orbitrec`orbit_type,proj,level);
	assert &and[brm(M,g[i]) eq Position(orbitrec`orbit_type,i)
	    where g:=orbitrec`gamma_list:i in [1.. #orbitrec`gamma_list]];
	orbitrec`orbit_number_list:=
	    orbit_number_list(orbitrec`orbit_type,F,cell,proj,proj_map);
	orbitrec`non_orientable_orbits:=
	    non_orientable_orbits(orbitrec`orbit_type,F,cell,proj,proj_map);
	orbitrec`entry:=[base+i:i in [1..orbitrec`total_number]];
	Append(~total,orbitrec);
	base:=base+orbitrec`total_number;
    end for;
    vprintf Bianchi,2:"  Found %o Gamma0-orbits of cells.\n",
	&+[a`total_number:a in total];
    return total;
end function;

procedure SetLevel(M)
    //Given F and level, attaches ModFrmData M`LevelDataord.
    //Assumes F has been set up and cells have been computed.}
    level:=Level(M);
    if not assigned M`LevelData`projective_space then 
	F:=BaseField(M);
	O:=Integers(F);
	rF:=quo<O|level>;
	M`LevelData`rF:=rF;
	M`LevelData`good_a:=AssociativeArray();
	M`LevelData`projective_space, M`LevelData`projective_space_map:=
            ProjectiveLine(rF:Type:="Vector");
    end if;
    
    if not assigned M`LevelData`two_orbits then 
	M`LevelData`two_orbits:=GetOrbits(M,2);
	M`LevelData`one_orbits:=GetOrbits(M,1);
	M`LevelData`total_number_of_one_orbits:=
	    &+[a`total_number:a in M`LevelData`one_orbits];
	M`LevelData`total_number_of_two_orbits:=
	    &+[a`total_number:a in M`LevelData`two_orbits];
	M`LevelData`homology:=rec<HomologyRec|>;
    end if;
end procedure;

