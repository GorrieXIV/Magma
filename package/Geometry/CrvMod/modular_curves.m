freeze;

declare verbose ModularCurve, 2;

CanLvls := {2,3,5,7,11,13,17,19,23,29,31,37,41,43,53,61,67,73,97};
AtkLvls := {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,71,83,101};

function InvolutionReconstruction(PX,strseq)
    k := 1;
    x := PX.1; j := PX.2; z := PX.3;
    poly := [ PX | ];
    degs := StringToIntegerSequence(strseq[k]);
    for n in degs do
	F := PX!0;
        for i in [0..n] do
	    k +:= 1;
            F +:= StringToInteger(strseq[k])*x^i*z^(n-i);
        end for;;
        Append(~poly, F);
    end for;
    r := Max(degs);
    r1 := Max(degs[1..#degs-1]); r2 := degs[#degs];
    num := &+[ poly[i]*j^(i-1)*z^(r1-degs[i]-i+1) : i in [1..#degs-1] ];
    den := poly[#degs];
    return [ num, den ], r1, r2;
end function;

intrinsic CanonicalInvolution(X::CrvMod) -> Map
    {The canonical involution of the modular curve X.}

    require IsProjective(X) : "Argument 1 must be projective";
    PX := CoordinateRing(X);
    x := PX.1; j := PX.2; z := PX.3;
    model_type := ModelType(X);
    N := Level(X);
    if model_type eq "Classical" then
	if N eq 1 then
	    return map< X -> X | [ -PX.2, -PX.1, PX.3 ] >;
	end if;
	return map< X -> X | [ PX.2, PX.1, PX.3 ] >;
    elif model_type eq "Atkin" then
	require N in AtkLvls : 
	    "Level of argument, for Atkin models, " *
	    "must be in the set", AtkLvls;
    elif model_type eq "Canonical" then
	require N in CanLvls :
  	    "Level of argument, for canonical models, " * 
	    "must be in the set", CanLvls;
    else 
	require false : 
            "Model type of argument must be one of " *
            "\"Atkin\", \"Canonical\", or \"Classical\".";
    end if;
    ModEq := GetLibraryRoot() * "/data/ModEq/" * model_type;
    nnn := IntegerToString(N);
    while #nnn lt 3 do nnn := "0" * nnn; end while;
    str := Read(ModEq * "/canonical_involution." * nnn * ".dat");
    jinv, r1, r2 := InvolutionReconstruction(PX,Split(str,"\n"));
    if model_type eq "Atkin" then
	z2 := z^(r1-r2-1);
	return map< X -> X | [ x*jinv[2]*z2, jinv[1], z*jinv[2]*z2 ] >;
    else
	s := GCD(N-1,12);
	z2 := z^(r1-r2+1);
	return map< X -> X | [ N^s*jinv[2]*z2, x*jinv[1], jinv[2]*z2 ] >;
    end if;
end intrinsic;

intrinsic AtkinLehnerInvolution(X::CrvMod,N::RngIntElt) -> Map
    {The Atkin-Lehner involution of the modular curve X.}

    require N eq Level(X) :
       "Argument 2 must equal the level of the curve.";
    require IsProjective(X) : "Argument 1 must be projective";
    model_type := ModelType(X);
    require model_type in {"Atkin", "Canonical", "Classical"} :
        "Model type of argument must be one of " *
        "\"Atkin\", \"Canonical\", or \"Classical\".";
    return CanonicalInvolution(X);
end intrinsic;

intrinsic BaseCurve(X::CrvMod) -> CrvMod, Map
    {The base curve X(1) of the modular curve X_0(N), followed by
    the projection to this curve.}
    model_type := ModelType(X);
    require model_type in {"Atkin", "Canonical", "Classical"} :
        "Model type of argument must be one of " *
	"\"Atkin\", \"Canonical\", or \"Classical\".";
    A := Ambient(X);
    PX := CoordinateRing(A);
    // This is wrong but database reports this...
    Y := ModularCurve(A,PX.1+PX.2,"Classical",[1,1,1]);
    // Should be:
    // Y := ModularCurve(A,PX.1-PX.2,"Classical",[1,1,1]);
    if IsAffine(A) then
	return Y, map< X -> Y | [-PX.2,PX.2] >;
	// Should be:
	// return Y, map< X -> Y | [PX.2,PX.2] >;
    else
	return Y, map< X -> Y | [-PX.2,PX.2,PX.3] >;
	// Should be:
	// return Y, map< X -> Y | [PX.2,PX.2,PX.3] >;
    end if;
end intrinsic;

intrinsic jFunction(X::CrvMod) -> FldFunFracSchElt
    {Returns the j-invariant as a function on the modular curve}
    require IsField(BaseRing(X)) :
        "Argument must be defined over a field.";
    return FunctionField(X).2;
end intrinsic;
