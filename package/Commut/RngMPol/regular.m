freeze;

/****************************************************************************
Intrinsics to compute REGULAR SEQUENCES in ideals of polynomial rings.
  Follow the algorithm of Eisenbud & Sturmfels from "Finding sparse systems
  systems of parameters" (Journal of Pure & Applied Algebra 94, 1994,143-157)
****************************************************************************/

procedure MyReduce(~mons)
// finds a minimal set of mons that generate the same monomial ideal
    
    R := Generic(Universe(mons));
    n := Rank(R);
    exps := [Exponents(m) : m in mons];

    j := #mons;
    while j gt 0 do
	expj := exps[j];
	for i in [1..#mons] do
	    if i eq j then continue; end if;
	    expi := exps[i];
	    if &and[expi[k] le expj[k] : k in [1..n]] then
		Remove(~mons,j); Remove(~exps,j); break;
	    end if; 
	end for;
	j -:= 1;
    end while;

end procedure;

function MonomialIdealMeet(Imons)

    assert #Imons gt 0;

    mons := Imons[1];
    R := Generic(Universe(mons));
    n := Rank(R);
    MyReduce(~mons);
    for j in [2..#Imons] do
	mons1 := Imons[j];
	mons := [Monomial(R,[Max(e1[i],e2[i]) : i in [1..n]]) where
		  e1 is Exponents(m1) where e2 is Exponents(m2) :
		   m1 in mons, m2 in mons1];
	MyReduce(~mons);
    end for;
    return mons;

end function;

function MonomialIdealIsSub(mons1,mons2)

    if #mons1 eq 0 then return true; end if;
    if #mons2 eq 0 then return false; end if;

    exps2 := [Exponents(m) : m in mons2];
    n := #(exps2[1]);
    for m in mons1 do
	expm := Exponents(m);
	if &and[&or[expm[i] lt e[i] : i in [1..n]] : e in exps2] then
	    return false;
	end if;
    end for;
    return true;

end function;

function MakeIrredundant(prim_dec)

    pd1 := [p[1] : p in prim_dec];
    pd2 := [p[2] : p in prim_dec];

    i := #pd2;
    while i gt 0 do
	i_min := [j : j in [1..#pd2] | (j ne i) and
	    (Seqset(pd2[j]) subset Seqset(pd2[i]))];
	if #i_min gt 0 then
	    if MonomialIdealIsSub(MonomialIdealMeet([Basis(pd1[j]): j in i_min]),
		Basis(pd1[i])) then
		  Remove(~pd1,i); Remove(~pd2,i);
	    end if;
	end if;
	i -:= 1;
    end while;

    return [<pd1[i],pd2[i]> : i in [1..#pd1]];

end function;

function MyMonomialPrimaryDecomposition(monos)
// computes a primary decomposition of monomial ideal <monos>
  
    R := Generic(Universe(monos));
    n := Rank(R);

    // first find all vars occuring in mons
    exps := [Exponents(m) : m in monos];
    vars := [i : i in [1..n] | &or[e[i] ne 0 : e in exps]];

    // data lists
    prim_dec_pairs := [];
    list := [<monos,vars,[Integers()|]>];

    while #list gt 0 do
	mons, vars1, vars2 := Explode(list[#list]);

	if (#vars1 eq 0) or (#mons eq #vars2) then 
	    Append(~prim_dec_pairs,<ideal<R|mons>,vars2>);
	    Prune(~list); continue;
	end if;
 
	ind1 := vars1[1];
	mons1 := mons[[1..#vars2]];
	exps := [Exponents(mons[i])[ind1] : i in [#vars2+1..#mons]];
	mons2 := [mons[i+#vars2] : i in [1..#mons-#vars2] | exps[i] eq 0];
	mons3 := [mons[i+#vars2] : i in [1..#mons-#vars2] | exps[i] ne 0];
	exps := [e : e in exps | e ne 0];

	if #exps eq 0 then
	    list[#list] := <mons,Remove(vars1,1),vars2>;
	    continue;
	end if;

	r := Max(exps);
	mons4 := [Monomial(R,e[[1..ind1-1]] cat [0] cat e[[ind1+1..n]])
		    where e is Exponents(m) : m in mons3];
	if &or[TotalDegree(m) eq 0 : m in mons4] then
	    Prune(~list);
	else
	    list[#list] := <mons1 cat
		[m : m in mons2 | &and[not IsDivisibleBy(m,m1) : m1 in mons4]]
		cat mons4,Remove(vars1,1),vars2>;
	end if;
	Append(~list,<mons1 cat [(R.ind1)^r] cat mons2 cat
		[mons3[i] : i in [1..#exps] | exps[i] ne r],
		Remove(vars1,1), vars2 cat [ind1]>);
    end while;

    //sort by prime height
    Sort(~prim_dec_pairs,func<x,y|#(x[2]) - #(y[2])>);
    return prim_dec_pairs;

end function;

function get_minimal_subset(mons)
// if ideal <mons> is of height c, finds a minimal subset of mons that still
//  generate a height c ideal. Returns the indices [in the sequence mons] of
//  the chosen subset and the indices of a set of vars of size c which generate
//  a minimal prime over <mons>

    pd := MyMonomialPrimaryDecomposition(mons);
    c := #(pd[1][2]);
    ps := [p[2] : p in pd];

    // get all minimal primes
    min_ps := [ ps[i] : i in [1..#ps] | &and[not Seqset(ps[j]) subset Seqset(ps[i]):
		   j in [1..#ps] | j ne i]];

    // get all var subsets of size c-1 in min primes
    bad_cm1 := Setseq(&join[Subsets(Seqset(p),c-1) : p in min_ps]);

    // get "bad" subsets of mons that lie in <x[i] : i in b> where b
    //  is a bad_cm1 set
    exps := [Exponents(m) : m in mons];
    N := #mons; n := Rank(Generic(Universe(mons)));
    bad_mons := [{j:  j in [1..N] | &or[e[i] ne 0 : i in b] where e is exps[j]} 
	: b in bad_cm1];
 
    // find a smallest subset of mons that is of height c. This is now equiv
    //  to finding a smallest subset of {1..N} not lying in any of the
    //  bad_mons sets.
    bad_mons_cmpl := [{i : i in [1..N] | i notin b} : b in bad_mons];
    // want a smallest cardnality set that intersects each of those in bad_mons_cmpl
    //  get by integer linear programming
    M := #bad_mons_cmpl;
    opt_mat := ZeroMatrix(Integers(),M,N);
    for i in [1..M] do
	for j in bad_mons_cmpl[i] do
	    opt_mat[i,j] := 1;
	end for;
    end for;
    rel_mat := Matrix(Integers(),M,1,[1 : i in [1..M]]); // also = rhs matrix!
    obj_mat := Matrix(Integers(),1,N,[1 : i in [1..N]]);
    soln,e := MinimalZeroOneSolution(opt_mat,rel_mat,rel_mat,obj_mat);
    assert e eq 0;
    mons1 := [i : i in [1..N] | es[i] eq 1] where es is Eltseq(soln);

    // finally, divide into divisibility sets.
    vars := ps[1];
    mon_sets := [];
    for i in vars do
	seti := [];
	for j := #mons1 to 1 by -1 do
	    if Exponents(mons[mons1[j]])[i] ne 0 then
		Append(~seti,mons1[j]); Remove(~mons1,j);
	    end if;	    	    
	end for;
	Append(~mon_sets,seti);
    end for;

    return mon_sets,vars;

end function;

RandomProc := recformat<
  gens		: SeqEnum,
  l		: RngIntElt,
  u		: RngIntElt,
  lat_proc	: LatEnumProc
>;

function RandProcInit(k,B)
    rp := rec<RandomProc | gens := B, l := 1>;
    if Characteristic(k) eq 0 then
	rp`u := 10;
	rp`lat_proc := ShortVectorsProcess(StandardLattice(#B),1,10);
    end if;
    return rp;
end function;

function RandomLinearCombo(rp,k)

    if Type(k) eq FldFin then
	if rp`l gt 0 then
	    b := (rp`gens)[rp`l];
	    if rp`l lt #(rp`gens) then
		rp`l := rp`l + 1;
	    else
		rp`l := 0;
	    end if;
	    return b;
	else
	  return &+[Random(k)*b : b in rp`gens];
	end if;
    elif Characteristic(k) gt 0 then
	error "Sorry! Random linear combinations not done for this base field yet.";
    else
	vec,res := NextVector(rp`lat_proc);
	if res eq -1 then
	    rp`l := (rp`u)+1; rp`u := 2*(rp`u);
	    rp`lat_proc := ShortVectorsProcess(StandardLattice(#(rp`gens)),
		rp`l, rp`u);
	    vec := NextVector(rp`lat_proc);
	end if;
	vec := Eltseq(vec);
	return &+[vec[i]*(rp`gens)[i] : i in [1..#vec]];
    end if;

end function;

intrinsic RegularSequence(I::RngMPol : Homogeneous := true) -> SeqEnum
{ Computes a maximal regular sequence of elements inside ideal I of
  a polynomial ring over a field }

    B := EasyBasis(I);
    // do special cases
    if not IsProper(I) then
	return [R.i : i in [1..Rank(R)]] where R is Generic(I);
    elif IsZero(I) then
	return [I|];
    end if;
    // Find minimal set of elts of B to get a reg seq from linear combs.
    //  Compute by considering the monomial ideal of leading terms. 
    mons := [LeadingTerm(b) : b in B];
    mon_inds,varinds := get_minimal_subset(mons);
    B := [Generic(I)|b : b in B]; // make sure we're back in Generic(I)!
    Bsets := [[B[i] : i in mi] : mi in mon_inds];

    // homogeneity conversion
    if Homogeneous and (Max([#bs : bs in Bsets]) gt 1) and
		&and[IsHomogeneous(b) : b in B] then
      for i in [1..#Bsets] do
	if #(Bsets[i]) gt 1 then
	  var := Generic(I).(varinds[i]);
	  dmax := Max([LeadingTotalDegree(b) : b in Bsets[i]]);
	  for j in [1..#(Bsets[i])] do
	    if LeadingTotalDegree((Bsets[i])[j]) lt dmax then
		(Bsets[i])[j] *:= var^(dmax - 
			LeadingTotalDegree((Bsets[i])[j]) );
	    end if;
	  end for;
	end if;	
      end for;
    end if;

    // get the "easy" part of a reg sequence
    reg_seq := [ b[1] : b in Bsets | #b eq 1];
    // now get the rest by random linear combos
    Brem := [ b : b in Bsets | #b gt 1 ];
    if #Brem eq 0 then return reg_seq; end if;

    R := Generic(I); n := Rank(R); k := BaseRing(R);
    I1 := ideal<R|reg_seq>;
    for b in Brem do
	rp := RandProcInit(k,b);
	while true do
	  t := RandomLinearCombo(rp,k);
	  I1 := ideal<R|Basis(I1) cat [t]>;
	  if n-Dimension(I1) eq (#reg_seq)+1 then
	    Append(~reg_seq,t); break;
	  end if;	
	end while;
    end for;
    return reg_seq;
	
end intrinsic;
