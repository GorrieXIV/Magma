freeze;
 
function is_subseq(A,B)
    // true iff the seq A subset B; spare B-A also returned
    for a in A do
        i := Index(B,a);
        if i eq 0 then
            return false,_;
        end if;
        Remove(~B,i);
    end for;
    return true,B;
end function;

function remove(Q,q)
    // return true and Q with one occurrance of q removed. false if q not in Q.
    i := Index(Q,q);
    if i eq 0 then
        return false,_;
    else
        return true, [ Q[j] : j in [1..#Q] | j ne i ];
    end if;
end function;

function posneg(f)
    // Given a poly f return 2 seqs of seqs C, each seq C having [coeff,deg]
    // pairs of terms of f in it. A seq C contains adjacent terms of the
    // same sign. Those with pos coeff go in first return seq, those neg in 2nd.
    // Try it on:
    //          > R<t> := PolynomialRing(Rationals());
    //          > posneg(1 - 3*t - t^3 + 2*t^6);
    // returns
    //          [ [[1,0]], [[2,6]] ] [ [[-3,1],[-1,3]] ]
    // splitting poly as
    //          (1) + (-3*t-1*t^3) + (2*t^6).
    R := Parent(f);
    if Type(f) eq FldFunRatUElt then
        R := RingOfIntegers(R);
        bool,f := IsCoercible(R,f);
        if not bool then
            error if true,
             "f must be a polynomial in 1 variable or have trivial denominator";
        end if;
    elif Type(f) ne RngUPolElt then
        error if true,
            "f must be a polynomial in 1 variable or have trivial denominator";
    end if;
    neg := [];
    pos := [];
    prev := 1;
    d := -1;
    temp := [];
    for c in Coefficients(f) do
        d +:= 1;
        if c eq 0 then
            continue;
        end if;
        if Sign(c) eq prev then
            Append(~temp,[c,d]);
        else
            if prev eq 1 then
                Append(~pos,temp);
            else
                Append(~neg,temp);
            end if;
            prev *:= -1;
            temp := [ [c,d] ];
        end if;
    end for;
    if prev eq 1 then
        Append(~pos,temp);
    else
        Append(~neg,temp);
    end if;
    return pos,neg;
end function;

