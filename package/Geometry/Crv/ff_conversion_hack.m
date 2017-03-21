freeze;

/*
   Functions to go from FldFunFracSch elements on a projective curve C
   to rational functions on the ambient of Cs FF affine patch in a naive
   (but fast) way. To be used by internal C-level functions.
*/

function FunctionFieldEvaluation(f,elts)

    // f an elt of alg fn fld F = k(x,alpha_1,..alpha_r).
    // elts = [e_0,e_1,..e_r], e_i in some appropriate field
    //  structure, F1.
    //  Returns phi(f) where phi is the field homomorphism
    // F -> F1, given by x |-> e_0, alpha_i |-> e_i
    
    if #elts eq 1 then
	if Type(Parent(f)) eq FldFunRat then
	    return Evaluate(f,elts[1]);
	else // Type(Parent(f)) eq FldFun - sigh!
	    return Evaluate(
		RationalFunctionField(ConstantField(Parent(f)))!f,elts[1]);
	end if;
    else // elts should be > 1!
	F1 := BaseRing(Parent(f));
	coeffs := [ FunctionFieldEvaluation(c,elts1) : c in expn ]
		where elts1 is Prune(elts) where expn is Eltseq(f);
	return Evaluate(PolynomialRing(Universe(coeffs))!coeffs,elts[#elts]);
    end if;
    
end function;

function gen_seq(F)
/* get sequence of field generators of AlFF F over the constant field */
    seq := [];
    F1 := F;
    while IsFinite(Degree(F1)) do
        seq cat:= [F!(F1.i) : i in [1..Ngens(F1)]];
	F1 := BaseField(F1);
    end while;
    Append(~seq,F!(F1.1));
    return Reverse(seq);
end function;

/* 
    ff_elts is a sequence of FldFunFracSch elements in the FF of
    curve C. Returns a sequence of rational functions on the
    ambient of the FF affine patch of C which <-> ff_elts
*/
intrinsic InternalFFPatchRatFunctions(ff_elts::SeqEnum) -> SeqEnum
{Internal function}
    F := Universe(ff_elts);
    error if not (Type(F) eq FldFunFracSch),
	"Erroneous internal call to conversion function for FldFunFracSch",
	"elements - wrong type found";
    AF,mpC := AlgorithmicFunctionField(F);

    // get coord functions <-> AlFF generators
    C := Curve(F);
    Ca := AffinePatch(C, FFPatchIndex(C));
    if Length(Ca) eq 1 then // special proj line case - sigh!
      Cseq := [R.1] where R is CoordinateRing(Ambient(Ca));
    else
      /* 08/10 - mch - AF can contain some "constant" generators if C is a line
	(why??), so fixed to coerce these directly into R */
      Fgens := gen_seq(AF);
      Cseq := [Index(seq,s): s in [mpCi(f) : f in Fgens]] where
	mpCi is Inverse(mpC) where seq is [F.i : i in [1..Length(Ca)]];
      Cseq := [(Cseq[j] eq 0) select R!(Fgens[j]) else R.(Cseq[j]) : j in [1..#Cseq]] 
		where R is CoordinateRing(Ambient(Ca));
    end if;

    // now just substitute into the alff "polys" <-> ff_elts elements
    return [FunctionFieldEvaluation(mpC(f),Cseq) : f in ff_elts];
end intrinsic;

/* 
    ff_elts is a sequence of FldFunFracSch elements in the FF of
    curve C. Returns a sequence of rational functions on the
    ambient of C which <-> ff_elts
*/
intrinsic InternalFFToFFAmb(ff_elts::SeqEnum, C::Sch) -> SeqEnum
{Internal function}
    //first get rat fns on FFpatch of Cproj
    patch_ff_elts := InternalFFPatchRatFunctions(ff_elts);

    //convert to rational function on ambient of C
    is_proj := IsProjective(C);
    Cp := (is_proj select C else ProjectiveClosure(C));
    Aa := Ambient(AffinePatch(Cp,FFPatchIndex(Cp)));
    if is_proj then
	seq := InverseDefiningPolynomials(ProjectiveClosureMap(Aa));
    else
	if Aa eq Ambient(C) then  // C IS the function field patch ...
	    return patch_ff_elts;
	end if;
	// ... otherwise, have to projectivise and affinise again.
	//  do it with one substitution in effect.
	seq1 := InverseDefiningPolynomials(ProjectiveClosureMap(Aa));
	seq2 := DefiningPolynomials(ProjectiveClosureMap(Ambient(C)));
	seq := [Evaluate(Numerator(f),seq2)/Evaluate(Denominator(f),seq2):
			f in seq1];	
    end if;
    return [Evaluate(Numerator(f),seq)/Evaluate(Denominator(f),seq):
			f in patch_ff_elts];
 
end intrinsic;
