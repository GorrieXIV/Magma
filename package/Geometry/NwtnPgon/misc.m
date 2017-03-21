freeze;

intrinsic IsNewtonPolygonOf(N::NwtnPgon, f::RngElt) -> BoolElt
{True iff f is the defining polynomial of N}

    return Polynomial(N) eq f;

end intrinsic;

intrinsic IsDegenerate(F::NwtnPgonFace) -> BoolElt
{True iff the face function along F is not squarefree}

    require HasPolynomial(Parent(F)) : 
			    "The polygon was not defined using a polynomial";
    f := FaceFunction(F);
    if Type(f) eq RngMPolElt then
        gcd := f;
        for g in JacobianSequence(f) do
            gcd := GCD(gcd,g);
        end for;
        sqfree := TotalDegree(gcd) eq 0;
    elif Type(f) eq RngUPolElt then
        g := GCD(f,Derivative(f));
        sqfree := Degree(g) eq 0;
    end if;
    return not sqfree;
end intrinsic;

intrinsic IsDegenerate(N::NwtnPgon) -> BoolElt
{True iff the defining polynomial of N is degenerate on some face of N}
    require HasPolynomial(N):
        "The polygon was not defined using a polynomial";
    for F in Faces(N) do
        if IsDegenerate(F) then
            return true;
        end if;
    end for;
    return false;
end intrinsic;

intrinsic GradientVectors(N::NwtnPgon) -> SeqEnum
{The gradient vectors of each of the faces of N}

    grads := [];
    for f in Faces(N) do
	grads := grads cat [GradientVector(f)];
    end for;

    return grads;

end intrinsic;
