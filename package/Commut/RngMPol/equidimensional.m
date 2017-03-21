freeze;

//////////////////////////////////////////////////////////////
//  Functions to perform Equidimensional decomposition on   //
//        ideals with no embedded components.               //
//         Added by Mike Harrison, 05/2004                  //
//////////////////////////////////////////////////////////////

/*  
    06/06 - mch - added faster "module version" for homogeneous
    ideals in ordinarily-weighted polynomial rings for computation
    of the equidimensional part of I.
*/

/*****Functions to compute equidimensional part of a homog. ideal***********/
/***using the projection of a module to a graded subring giving the ********/
/*********************Noether normalisation        *************************/
/*
   The functions all assume that things have been normalised so that
   a graded module M over R=k[x_1,...,x_n] has k[x_(n-d+1),..,x_n] as
   a Noether normalising subring.

   MyMinimise(M) - temporary hack. finds a minimal basis for the module
		given by the cokernel of matrix M.
   ModuleProject(I,Ry) - finds the projection of R/I and expresses it as
		a module over Ry a poly ring in d vars
   ModuleEquidimensional(I,d) - Finds the equidimensional part of I using
		the projection of R/I.
*/

//include left/right kernel

function LeftKernel(M)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the left kernel of polynomial matrix M
//  (seq s gives the coordinates of a kernel vector)
   Mmod := Module(BaseRing(M),Ncols(M));
   S := sub<Mmod|[M[i]:i in [1..Nrows(M)]]>;
   return [Eltseq(b): b in Basis(SyzygyModule(S))];
end function;

function RightKernel(M)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the right kernel of polynomial matrix M
//  (seq s gives the coordinates of a kernel vector)
    return LeftKernel(Transpose(M));
end function;

function MyMinimise(M)
/* 
   Takes a matrix M whose rows gives the relations for a module mod
   and returns a new matrix which give the relations wrt a minimal
   basis. [Temporary hack while core function is unavailable!]
*/
    while true do
	ind := Index([TotalDegree(m) : m in Eltseq(M)],0);
        if ind eq 0 then break; end if; // M has no non-zero constant terms
        nc := Ncols(M); nr := Nrows(M);
	if nc eq 1 then return Matrix(BaseRing(M),0,0,[]); end if;
        row := Floor((ind-1)/nc) + 1;
	col := ind - (row-1)*nc;
	// M[row,col] is constant - eliminate variable col and 
	// adjust M accordingly
	MultiplyRow(~M,-1/M[row,col],row);
	for i in [1..nr] do
	    if i eq row then continue; end if;
	    AddRow(~M,M[i,col],row,i);
	end for;
	// remove row row and column col
	M := VerticalJoin(RowSubmatrix(M,row-1),RowSubmatrix(M,row+1,nr-row));
	M := HorizontalJoin( ColumnSubmatrix(M,col-1),
		ColumnSubmatrix(M,col+1,nc-col) );
    end while;
    return M;	
end function;


function ModuleProject(I,Ry)
/* 
   takes module M=S/I over S=k[x_1,..x_n], finite over Ry=k[y_1,..y_d]
   if y_i is mapped to x_(n-d+i), and returns the corresponding
   module over k[y_1,..,y_d] as a reduced (ie presentational) module.

   as well as returning M, the function also returns a sequence of
   r*r matrices (where M = Ry^r/relations) giving the actions of
   x_1,..,x_(n-d) on M, so that the S-module structure can be recovered 
*/

    R0 := Generic(I);
//make sure have degrevlex! and Ry too!

    R := R0;
    n := Rank(R);
    d := Rank(Ry);
    assert (n ge d) and (d gt 0);

    if n eq d then return QuotientModule(I); end if;

    Rx := PolynomialRing(BaseRing(R),n-d,"grevlex");
    mpx := hom<R->Rx|[Rx.i:i in [1..n-d]] cat [0:i in [1..d]]>;
    G := GroebnerBasis(I);

    //1. find module generators.
    Gx := [g : f in G | g ne 0 where g is mpx(LeadingTerm(f))];
    Itmp := ideal<Rx|Gx>; MarkGroebner(Itmp);
    _,deg := HilbertPolynomial(Itmp);
    delete Itmp;
    mons := &join[Isetset(MonomialsOfDegree(Rx,i)) : i in [0..deg]];
    for g in Gx do
	mons := {m : m in mons | not IsDivisibleBy(m,g)};
    end for;
    mons := Sort(Setseq(mons));
    //mons now form a set of generators for our module

    //2. find relations
    M := RModule(Ry,#mons);
    B := Basis(M);
    Gy := [g:g in G|l lt (R.(n-d))^TotalDegree(l) where l is
			LeadingMonomial(g)];
    rels := [M| &+[LeadingCoefficient(t)*Monomial(Ry,E[2])*
		B[i] where i is Index(mons,Monomial(Rx,E[1]))
                 where E is Partition(Exponents(t),[n-d,d]) :
		   t in Terms(g)] : g in Gy];
    
    if #rels gt 0 then M := quo<M|rels>; end if;

    //3. find the sequence of #mons*#mons matrices that give the
    //   action of x_1,..x_(n-d) on M
    h := hom<Rx->R|[R.i:i in [1..n-d]]>;
    mons1 := [h(m): m in mons];
    mats := [ Matrix(Ry,[ Eltseq( &+[M| LeadingCoefficient(t)*Monomial(Ry,E[2])*
		B[i] where i is Index(mons,Monomial(Rx,E[1]))
                 where E is Partition(Exponents(t),[n-d,d]) :
		   t in Terms(NormalForm((R.j)*m,I))]) : m in mons1])
			: j in [1..n-d] ]; 

    return M,mats;

end function;

function ModuleEquidimensional(I,d,bRk)
/*
   Input: I a homogeneous ideal over polynomial ring R s.t. the last 
       d variables of R give a Noether normalisation for R/I.
   The function computes and returns the equidimensional component E(I) 
   of I by working with R/I as a module over its Noether norm. ring.
    If bRk is true, also returns the rank of R/E(I) as a module over
   the Noether norm. ring of R/I.
*/

// I assumed to have grevlex ordering!
    Ry := PolynomialRing(BaseRing(I),d,"grevlex");
    M,x_mats := ModuleProject(I,Ry);

    // R/I as an Ry module now is the module M over Ry and
    //  E(I)/I is given by ker[M -> Hom_Ry(Hom_Ry(M,Ry),Ry)].
    // The quotient of R/I by this (ie R/E(I)) is computed
    //  simply from the presentation of M.
    rels := RelationMatrix(M);
    if Nrows(rels) eq 0 then  //M is free over Ry => R/I CM and equi
	return I, Degree(M);
    end if;
	// R/I is either not CM or not equi (or both!)
    dual_rels := RightKernel(rels);
    dual_mat := Matrix(Ry,dual_rels);
    new_rels := RightKernel(dual_mat);
    // new_rels is the new set of relations (containing the original
    //  rels) which define E(I). Hence we can now make M1 = R/E[I]

    // compute rank, if reqd, from new_rels
    if bRk then
	mat := Matrix([ChangeUniverse(rel,K): rel in new_rels])
		where K is FieldOfFractions(Ry);
	rk := Degree(M)-Rank(mat);
	delete mat;
    end if; 

    //construct module over original R by adding x-relations
    R := Generic(I); n := Rank(R); r := Degree(M);
    mapy := hom<Ry->R|[R.i:i in [n-d+1..n]]>;

    mat_xs := [ScalarMatrix(r,R.i)-Matrix(R,r,r,Eltseq(x_mats[i])@mapy) :
		i in [1..n-d]];
    M1 := Matrix(R,[[f@mapy : f in r] : r in new_rels]); 
    for m in mat_xs do
	M1 := VerticalJoin(M1,m);
    end for;
    // M1 now contains all the relations for the module over R
    // - annihilator of M1 is the equidim part of I

    M1 := MyMinimise(M1); //should be available as core function. Hack for now!
    if Ncols(M1) eq 1 then
	EI := ideal<R | [m : m in Eltseq(M1) | m ne 0]>;
        if bRk then return EI,rk;
	else return EI; end if;
    else
	error "Something's gone wrong!";
    end if;

end function;


/*****************************************************************************/

function LeadPoly(f,indsc)

    topexps := Exponents(LeadingTerm(f));
    n := #topexps;
    P := Parent(f);
    res := P!0;
    ts := Terms(f);
    for t in ts do
       exps := Exponents(t);
       for j in indsc do
           if exps[j] ne topexps[j] then
              break t;
           end if;
       end for;
       exps := [ (j in indsc) select 0 else exps[j] :
                       j in [1..n] ];
       res +:= LeadingCoefficient(t)*Monomial(P,exps);
    end for;
    return res;

end function;

function HomogeneousEquidimensional(I)
    R := Generic(I); n := Rank(R);
    // make sure we have the grevlex ordering
    I1 := ChangeOrder(I,"grevlex");
    R1 := Generic(I1);
    hm := hom<R1->R | [R.i : i in [1..n]]>;

    vars,h,hinv := NoetherNormalisation(I1);
    d := #vars; // d = Dimension(I)
    if (d eq 0) or (d eq n) then return I; end if;
    I1 := ideal<R1 | [h(b) : b in Basis(I1)]>;

    I2 := ModuleEquidimensional(I1,d,false);
    if (I2 subset I1) then 
	return I;
    else
	return ideal<R|[hm(hinv(b)): b in Basis(I2)]>;
    end if;
end function;

function EquidimensionalInBits(J)

    d, inds := Dimension(J);
    n := Rank(Generic(J));
    if (d le 0) or (d eq n) then
       return J;
    end if;
    d1 := d;
    I := J;
    list := [];
    while d1 eq d do
        // do the "ReductionToZero" iteration from Gruel/Pfister
        indc := [i: i in [1..n] | i notin inds];
        I1,mp := ChangeOrder(I,"elim",indc);
        mp := Inverse(mp);
	h := &*[LeadPoly(b,indc) : 
                           b in GroebnerBasis(I1)];
        I1,s := ColonIdeal(I1,h);
        I1 := ideal<Generic(J)|[mp(b) : b in Basis(I1)]>;
        h := mp(h^s);
	Append(~list,<I1,inds>);
        delete I1;
        I := I + ideal<Generic(J)|h>;
        d1, inds := Dimension(I);
    end while;
    return list;
                              
end function;

intrinsic EquidimensionalPart(I::RngMPol) -> RngMPol
{Returns the equidimensional part of an ideal}

   // in homogeneous case use faster module version above
   if &and[wt eq 1 : wt in VariableWeights(I)] and IsHomogeneous(I) then
	return HomogeneousEquidimensional(I);
   end if;

   ideals := EquidimensionalInBits(I);
   J := ideals[1][1];
   for k in [2..#ideals] do
       J meet:= ideals[k][1];
   end for;
   return J;

end intrinsic;

/* NB. For this function it is assumed that I has no embedded
       primary components, eg I is reduced.                   */

intrinsic EquidimensionalDecomposition(I::RngMPol) -> SeqEnum
{Returns the equidimensional components of an ideal with
  no embedded prime component}
 
    if IsZero(I) then return [I]; end if;
    J := I;
    d := Dimension(J);
    if d eq -1 then return [I]; end if;
    list := [Parent(I)|];
    while d gt 0 do
       E_J := EquidimensionalPart(J);
       Append(~list,E_J);
       if E_J subset J then break; end if;
       J := ColonIdeal(J,E_J); // assumption on I used here
       d := Dimension(J);
    end while;
    if d eq 0 then Append(~list,J); end if;
    return list;
    
end intrinsic;

/* NB. For this function it is assumed that I has no embedded
       primary components, eg I is reduced.                   */
       
intrinsic FineEquidimensionalDecomposition(I::RngMPol) -> SeqEnum
{Returns a sequence of pairs of an equidimensional ideal with a set of
  maximal independent variables for every prime component such that
  the intersection of the ideals is the ideal, I (which must have
  no embedded prime component)}

    if IsZero(I) then return [<I,[1..Rank(I)]>]; end if;
    J := I;
    d := Dimension(J);
    if d eq -1 then return [<I,[IntegerRing()|]>]; end if;
    list := [];
    while d gt 0 do
       E_Js := EquidimensionalInBits(J);
       list cat:= E_Js;
       E_J := E_Js[1][1];
       for k in [2..#E_Js] do
          E_J meet:= E_Js[k][1];
       end for;
       J := ColonIdeal(J,E_J); // assumption on I used here
       d := Dimension(J);
    end while;
    if d eq 0 then Append(~list,<J,[IntegerRing()|]>); end if;
    return list;
    
end intrinsic;

// n >= 2 and Is is a sequence of n ideals.
// Function returns the (length n) sequence of ideals
// given by intersecting all but one of the Is

function ComplementaryIntersections(Is)

    n := #Is;
    if n eq 2 then return [Is[2],Is[1]]; end if;
    if n eq 3 then
        return [Is[2] meet Is[3], Is[1] meet Is[3],
                  Is[1] meet Is[2]];
    end if;
    m1 := n div 2;
    I_1 := &meet[Is[i] : i in [m1+1..n]];
    I_2 := &meet[Is[i] : i in [1..m1]];
    I_1s := ComplementaryIntersections(Is[[1..m1]]);
    I_2s := ComplementaryIntersections(Is[[m1+1..n]]);
    return [I_1 meet id : id in I_1s] cat [I_2 meet id : id in I_2s];

end function;

// I is an equidimensional ideal in generic space P s.t. we
// know that I is full or we know that
// P/I is a DIRECT PRODUCT of integral domains and inds is a
// set of d indices of variables of P (d = Dimension(I))
// which constitute a maximally independant set for EVERY
// associated prime component of I.
// Given this data, the function returns the guaranteed associated
// primes of I, but in a generally faster way than the
// RadicalDecomposition function.
function SimplePrimeDecomposition(I,inds)

   if #inds eq 0 then // I full or zero-dimensional
       return RadicalDecomposition(I);
   end if;
   if IsZero(I) then return [I]; end if;

   // first reduce to the zero-dimensional case by localising
   I0,mp := Extension(I,inds);
   P0s := RadicalDecomposition(I0);
   if #P0s eq 1 then // I must be already prime
       return [I];
   end if;      

   // now find elements which lie in all but a single P for each P in P0s.
   elts := [Generic(I0)|];
   Is := ComplementaryIntersections(P0s);
   for i in [1..#P0s] do 
       for b in Basis(Is[i]) do
           if b notin I0 then
               Append(~elts,b); break;
           end if;
       end for;
   end for;
   delete Is;
   
   // clear denominators and map the elts back into Generic(I)
   P := Generic(I);
   R := IntegerRing(BaseRing(I0));
   mp := hom< R -> P | [P.i:i in inds]>;
   indsc := [i : i in [1..Rank(P)] | i notin inds];
   elts1 := [P|];
   for i in [1..#elts] do
     elt := elts[i];
     d := LCM([Denominator(a) : a in Coefficients(elt)]);
     Append(~elts1, &+[ mp(R!(LeadingCoefficient(t)*d)) *
                        &*[P.indsc[j]^exps[j]:j in [1..#indsc]]
                        where exps is Exponents(t) :
                          t in Terms(elt) ]  );
   end for;

   // return result: the prime factors are (I : a) for a in elts
   return [ ColonIdeal(I,elt) : elt in elts1 ];

end function;
