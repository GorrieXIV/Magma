freeze;
 
/////////////////////////////////////////////////////////////////////
//	Compatibility checks between baskets and weights
// GB Sept 03
/////////////////////////////////////////////////////////////////////

import "../HilbertSeries/misc.m": is_subseq;

forward minar, minr;
intrinsic CheckPoint(p::GRPtS,W::SeqEnum) -> BoolElt,SeqEnum
{True iff the sequence of weights W contains enough weights to
polarise the singularity p;  if false, the second return value
is a list of possible additional weights that are minimal}
    ok := true;
    extras := [ Integers() | ];
    Sort(~W);
    Wgiven := W;
    Wcurr := W;
    r := Index(p);
    P := [ a mod r : a in PrincipalPolarisation(p) ];	// just to be sure

    // Step 1: find r in W
    i := Index(Wcurr,r);
    if i ne 0 then
	// easy case
	Remove(~Wcurr,i);
    else
	// we need weights with exactly r as their common factor.
	Wr := [ Integers() | w : w in Wgiven | IsDivisibleBy(w,r) ];
	if GCD(Wr) eq r then
	    Remove(~Wcurr,Index(W,Wr[1]));
		// the remaining Wr can give 0 polarisations to P
	else
	    ok := false;
	    Append(~extras,r);	// THINK
	end if;
    end if;
    step1 := ok;

    // Step 2: find the polarisation P in W
    // method: remove first occurance of (a+kr) for some k for each a.
    for a in P do
	done := false;
	j := 1;
	repeat
	    if Wcurr[j] mod r eq a then
		Remove(~Wcurr,j);
		done := true;
	    end if;
	    j +:= 1;
	until done or j eq #Wcurr+1;
	if not done then
	    ok := false;
	    Append(~extras,minar(a,r,Wgiven));
	end if;
    end for;
    return ok,extras;
end intrinsic;

forward irred;
intrinsic CheckBasket(B::SeqEnum,W::SeqEnum) -> BoolElt,SeqEnum
{}
    bool,W := CheckBasket(MakeBasket(B),W);
    if bool then
	return true,W;
    else
	return false,_;
    end if;
end intrinsic;

intrinsic CheckBasket(B::GRBskt,W::SeqEnum) -> BoolElt,SeqEnum
{True iff the sequence of weights W contains enough weights to
polarise the singularities of the basket B;  if false, the second
return value is a suggestion for a larger collection of weights}
// THINK:  points only so far.
    // Strategy:  first make sure that enough points of the given
    // indexes can be realised by adding weights if necessary.
    // Then go through each point in turn, checking that its polarisation
    // can be realised.
    Wcurr := W;
    inds := [ Index(p) : p in Points(B) ];
    inds_red := Reversion(Sort(SetToSequence(SequenceToSet(inds))));

    // work through indexes in DECREASING order (since higher
    // indexes may add weights that suit lower indexes):
    // eg [ 1/2,1/2,1/4 ] on weights [1,1,1,2,3,5] would add weights
    // 2 and 4 if searching from 1/2 up, but only weight 4 from 1/4 down.
    for r in inds_red do
	nr := #[ s : s in inds | s eq r ];
	if not (nr eq 1 and r in Wcurr) then
	    // the minimum needed is a collection of weights with GCD = r.
	    rdiv := [ Integers() | s : s in Wcurr | s mod r eq 0 ];
	    if not (#rdiv ge 2 and GCD(rdiv) eq r) then
		// now we must add some new weight.
		if #rdiv ne 0 then
		    k := 0;
		    repeat
			k +:= 1;
		    until GCD(rdiv cat [k*r]) eq r and
			irred(k*r,[w:w in Wcurr|w lt w*r]);
		    Wcurr cat:= [ k*r ];
		else
		    if nr eq 1 and irred(r,[w:w in Wcurr|w lt r]) then
			Wcurr cat:= [r];
		    else
			// hardest case
			// *** THINK *** : temp
			Wcurr cat:= [r,r];
		    end if;
		end if;
	    end if;
	end if;
    end for;

    for p in Points(B) do
	_,extra := CheckPoint(p,Wcurr);
	Wcurr cat:= extra;
    end for;
    return Wcurr eq W, Wcurr;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//			Auxiliary functions
///////////////////////////////////////////////////////////////////////

forward adds_to;

/*
The polarising coordinate 1/r(a) is not realised in W.
Suggest a weight to add to W.  Note that this will mean adding a new
equation of the same weight, and that must be irreducible, so only
make suggestions that are bigger than Minimum(W) and could be the
weight of an irreducible equation in variable of weights W.
*/
function minar(a,r,W)
    // find the first value of 
    m := Minimum(W);
    while a lt m do
	a +:= r;
    end while;
    if not irred(a,[w:w in W|w lt a]) then
	a +:= r;
    end if;
    return a;
end function;

///////////////////////////////////////////////////////////////////////

function irred(a,Q)
// return true if there is an irreducible poly of weight a in the
// poly ring with weights Q.
    if #Q le 1 then
	// there can't be a nontrivial irreducible poly in 1 variable.
	return false;
    elif #Q eq 2 then
	// want to rule out x^sk = y^tk for common factor k > 1.
	bool1,S := IsDivisibleBy(a,Q[1]);
	bool2,T := IsDivisibleBy(a,Q[2]);
	if bool1 and bool2 and GCD(S,T) gt 1 then
	    return false;
	end if;
    end if;
    poss := adds_to(Q,a);
    if #poss le 1 then
	// there is only one monomial, so the poly is certainly not irred.
	return false;
    end if;
    for w in Q do
	if #[ v : v in Q | v eq w ] eq 1 then
	    // this variable must not appear in every monomial of poss.
	    if &and[ w in P : P in poss ] then
		return false;
	    end if;
	end if;
    end for;
    return true;
end function;

procedure add_q(~Q,q,n)
// include q in every elt of Q for which sum+q le n
    Qnew := [ Universe(Q) | ];
    for S in Q do
        S1 := S;
        done := false;
        repeat
            if &+S1 le n then
                Append(~Qnew,S1);
            else
                done := true;
            end if;
            Append(~S1,q);
        until done;
    end for;
    Q := Qnew;
end procedure;

function adds_to(Q,n)
// Q seq of integers, n an integer.
// combinations of elts of Q (with repeats) that sum to n
    Qout := [Parent([1,2]) |[] ];
    for q in Q do
        add_q(~Qout,q,n);
    end for;
    return [ S : S in Qout | &+S eq n ];
end function;

