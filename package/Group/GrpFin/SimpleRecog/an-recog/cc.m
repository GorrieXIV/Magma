/* Input: Group G isomorphic to 2.Alt(n) or 2.Sym(n)
 * Output: List of pairs, where the first entry is a conjugacy class representative,
 *         and the second entry is the centralizer.
 */
conjugacyClasses := function(G)
    b, e2p, p2e := RecogniseAlternatingOrSymmetric(G : Extension := true);

    if not b then
        error "not a central extension of an alternating or symmetric group";
    end if;

    H := Domain(p2e);

    //compute a generator of the center
    z := p2e(H!(1,2)(3,4))^2;

    if z eq One(G) or z^2 ne One(G) then
        error "G is not isomorphic to 2.Alt(n) or 2.Sym(n)";
    end if;

    cc := ConjugacyClasses(H);

    reps := [];

    for c in cc do
        C := Centralizer(H, c[3]);

        cG := p2e(c[3]);

        splits := true;
        centralizerGens := [];
        for x in Generators(C) do
            xG := p2e(x);
            if (cG, xG) ne One(G) then
                splits := false;
                Append(~centralizerGens, xG^2);
            else
                Append(~centralizerGens, xG);
            end if;
        end for;

        Append(~reps, <cG, sub< G | centralizerGens >>);
        if splits then
            Append(~reps, <z*cG, sub< G | centralizerGens >>);
        else
        end if;
    end for;

    return reps;
end function;


/* Input: 
 *  cc: Conjugacy classes computed by conjugacyClasses above
 *  CC: Conjugacy classes computed by the built in function ConjugacyClasses
 * Output:
 *  L: a list of integers such that cc[i] is conjugate to CC[L[i]] for all i.
 */
matchConjugacyClasses := function(cc, CC)
    L := [];
    for c in cc do
        for i in [1..#CC] do
            if IsConjugate(Parent(c[1]), c[1], CC[i][3]) then
                Append(~L, i);
                break;
            end if;
        end for;
    end for;

    return L;
end function;


for S in ["2A5", "2A6", "2A7", "2A8", "2A9", "2A10", "2A11", "2A12", "2A13"] do
    print "Computations for", S;
    G := MatrixGroup(S, 1);
    time cc := conjugacyClasses(G);
    time CC := ConjugacyClasses(G);

    if #cc eq #CC then
        print "number of conjucacy classes are equal";
    else
        print "number of conjucacy classes are DIFFERENT";
    end if;

    
    time L := matchConjugacyClasses(cc, CC);
    if #L eq #{l : l in L} then
        print "conjugacy classes match up";
    else
        print "conjugacy classes DONT match up";
    end if;
    print "";
end for;
