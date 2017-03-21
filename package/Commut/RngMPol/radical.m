freeze;

////////////////////////////////////////////////////////////////////
//      Functions to compute the (equidimensional) radical        //
//  of a homogeneous ideal via more module-theoretic methods      //
//                   added mch - 06/2006                          //
////////////////////////////////////////////////////////////////////

declare verbose HomRad,1;

import "equidimensional.m": ModuleEquidimensional;

function CISubBasis(I,Bm,d)
// I is a homogeneous ideal of dim d of k[x_1,..,x_n] s.t. the
//  last d variables are a Noether norm. set for I. Returns a
//  seq B=[f_1,..,f_(n-d)] which generates a dim d subideal of I.
// Bm a minimal basis for I. First tries 5 random subsets of Bm.
//  If this fails
//   f_i will be a monic poly x^i+a_(i-1)x^(i-1)+.. where the
//    a_j only contain vars x_(i+1),x_(i+2),..,x_n
    P := Generic(I);
    n := Rank(P);

    // try random combs
    S := Subsets(Seqset([1..#Bm]),n-d);
    tried := [];
    for i in [1..Min(10,#S)] do
	repeat
	    s := Random(S);
	until s notin tried;
	Append(~tried,s);
	if Dimension(ideal<P|[Bm[i] : i in s] cat 
			[P.i : i in [n-d+1..n]]>) eq 0 then
	    return true,[Bm[i] : i in s];
	end if;
    end for;
    delete tried,S;
    return false,_; //don't use second method. Revert to default for now!

    // use monic polys
    I1 := ChangeOrder(I,"lex");
    B := GroebnerBasis(I1);
    B := [b : b in B | (#[e : e in Exponents(m) | e ne 0] eq 1)
    		where m is LeadingMonomial(b)];
    assert #B eq (n-d);
    ChangeUniverse(~B,P);
    return true,B;
end function;

function gci_radical(I,B,d)
// B is the minimal basis of a homogeneous ideal I of dimension d
//  which is known to be generically a complete intersection and for
//  which the last d variables give a Noether normalisation.
//  returns the equidimensional radical of I
    R := Generic(Universe(B));
    n := Rank(R); 
    jac := Matrix([[Derivative(b,i) : i in [1..n-d]] : b in B]);
    jac_seq := Minors(jac,n-d);
    //now compute "equidimensional radical" via colon ideal
    //vprint HomRad: "  Computing colon ideal for C.I. radical...";
    //vtime HomRad: IR := ColonIdeal(I,ideal<R|jac_seq>);
  //now compute "equidimensional radical" via colon ideals
  vprintf HomRad: "  Computing %o colon ideals for C.I. radical...\n",#jac_seq;
  vtime HomRad: IR := &meet[ColonIdeal(I,j) : j in jac_seq];
    return IR;
end function;

intrinsic EquidimensionalRadical(I::RngMPol) -> RngMPol,BoolElt
{}
    require &and[wt eq 1 : wt in VariableWeights(I)]:
	  "All variable weights must be 1.";
    require IsHomogeneous(I):
	  "Ideal must be homogeneous.";
    R := Generic(I);
    n := Rank(R);

    // make sure we have the grevlex ordering
    I1 := ChangeOrder(I,"grevlex");
    R1 := Generic(I1);
    hm := hom<R1->R | [R.i : i in [1..n]]>;
    if R1!1 in I1 then return I,true; end if;

    vprint HomRad: " Getting Noether normalisation...";
    vtime HomRad: vars,h,hinv := NoetherNormalisation(I1);
    d := #vars; // d = Dimension(I)
    if d eq n then return I,true; end if;
    if d eq 0 then return ideal<R|[R.i : i in [1..n]]>,true; end if;
    if d eq 1 then // for now, do homog dim 1 by default
	vprint HomRad:
	    " Computing equidimensional radical by default method...";
	vtime HomRad: IR := Radical(I: Direct := true);
	return IR, true;	
    end if;
    I1 := ideal<R1 | [h(b) : b in Basis(I1)]>;

    // get the "full" equidimensional part of I
    p := Characteristic(BaseRing(R));
    vprint HomRad: " Computing equidimensional part...";
    if p ne 0 then
	vtime HomRad: I2,rk := ModuleEquidimensional(I1,d,true);
    else
	vtime HomRad: I2 := ModuleEquidimensional(I1,d,false);
        rk := 0;
    end if;
    boo_equi := (I2 subset I1); // is I2 eq I1 ?
    if boo_equi then I2 := I1; end if; // if so don't recompute grobner bs!

    if (p ne 0) and (rk ge p) then // separability condition may not hold
	vprint HomRad:
	    " Computing equidimensional radical by default method...";
	vtime HomRad: IR := Radical(I2: Direct := true);
	return ideal<R|[hm(hinv(b)): b in Basis(IR)]>, boo_equi;
    end if;

    B := MinimalBasis(I2);
    if #B gt (n-d) then
    // find a complete intersection in I2 for which last d vars
    // still give a Noether norm
	vprint HomRad: " Finding C.I. subideal...";
	vtime HomRad: boo,B1 := CISubBasis(I2,B,d);
	if not boo then // didn't find good reg sequence - revert to default!
	    vprint HomRad:
	    " Computing equidimensional radical by default method...";
	    vtime HomRad: IR := Radical(I2: Direct := true);
	    return ideal<R|[hm(hinv(b)): b in Basis(IR)]>, boo_equi;
        end if;
	vprint HomRad: " Computing C.I. radical...";
	JR := gci_radical(ideal<R1|B1>,B1,d);
	vprint HomRad: " Computing colon ideal...";
	vtime HomRad: IR := ColonIdeal(JR,ideal<R1|B>);
	vprint HomRad: " Computing colon ideal...";
	vtime HomRad: IR := ColonIdeal(JR,ideal<R1|MinimalBasis(IR)>);
	return ideal<R|[hm(hinv(b)): b in Basis(IR)]>, boo_equi;
    else // I2 a complete intersection!
	vprint HomRad: " Computing C.I. radical...";
	IR := gci_radical(I2,B,d);
	return ideal<R|[hm(hinv(b)): b in Basis(IR)]>, boo_equi;
    end if;

end intrinsic;

intrinsic HomogeneousRadical(I::RngMPol) -> RngMPol
{}
    require &and[wt eq 1 : wt in VariableWeights(I)]:
	  "All variable weights must be 1.";
    require IsHomogeneous(I):
	  "Ideal must be homogeneous.";

    tyme := Cputime();
    vprint HomRad: "Computing equi-dimensional radical";
    EIR,boo_equi := EquidimensionalRadical(I);
    IR := EIR;
    while not boo_equi do
	vprint HomRad: "Computing lower dimensional component part of I...";
	vtime HomRad: I := &meet[ColonIdeal(I,b) : b in MinimalBasis(EIR)
			| b notin I];
	vprint HomRad: "Computing equi-dimensional radical";
	EIR,boo_equi := EquidimensionalRadical(I);
	IR meet:= EIR;
    end while;
    vprintf HomRad: "Total time: %o\n",Cputime(tyme);
    return IR;
end intrinsic;

