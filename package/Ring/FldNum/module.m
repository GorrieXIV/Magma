
freeze;

intrinsic Hom(M::ModDed, N::ModDed) -> ModDed, Map
{The Hom-Module of homomorphisms between M and N};
    require BaseRing(M) eq BaseRing(N) : 
		"Orders of domain and codomain are different";
    PM := PseudoBasis(M);
    PN := PseudoBasis(N);
    S := [PN[i][1]/PM[j][1] : i in [1 .. #PN], j in [1 .. #PM]];
    H := Module(S);
    m := map<H -> PowerStructure(Map) | 
	     x :-> hom<M -> N | 
	               Matrix(FieldOfFractions(BaseRing(N)),
			      Ngens(M),Ngens(N), Eltseq(x))
			 : ModuleBasis := true>
	    >;
    return H, m;
end intrinsic;

//-------------
//
// Miscellaneous algorithms for pseudomatrices.
//
//-------------

/*intrinsic Transpose(P::PMat) -> PMat
  {Returns the transpose of the pseudomatrix.}

  M := Matrix(P);
  I := CoefficientIdeals(P);
  return PseudoMatrix(I, Transpose(M));
end intrinsic;*/

intrinsic Basis(P::PMat) -> SeqEnum
  {Returns the basis of the pseudomatrix.}
  M := Matrix(P);
  return [Eltseq(M[i]) : i in [1..Nrows(M)]];
end intrinsic;

intrinsic Module(P::PMat) -> ModDed
  {Returns the module defined by the rows of the pseudomatrix.}
  return Module([<c[i], m[i]> : i in [1..#c]])
         where c := CoefficientIdeals(P) where m := Matrix(P);
end intrinsic;

intrinsic PseudoMatrix(M::ModDed:Generators := false) -> PMat
  {Returns the pseudomatrix used as "basis" for the module.}
  if Generators then l := PseudoGenerators(M);
  else l := PseudoBasis(M); end if;
  if Dimension(M) eq 0 then O:=BaseRing(M);
  return PseudoMatrix([Parent(1*O)|], Matrix(O,0,Degree(M),[])); end if;
  return PseudoMatrix([x[1] :x in l], Matrix([x[2] : x in l]));
end intrinsic;

intrinsic '*'(M::PMat, A::RngOrdFracIdl) -> PMat {}
  C := CoefficientIdeals(M);
  return PseudoMatrix([x*A : x in C], Matrix(M));
end intrinsic;

intrinsic '*'(A::RngOrdFracIdl, M::PMat) -> PMat {}
  C := CoefficientIdeals(M);
  return PseudoMatrix([x*A : x in C], Matrix(M));
end intrinsic;

intrinsic Order(O::RngOrd, M::PMat:Check := true) -> RngOrd
  {The order where the basis is given via the transformation in M.}
  n := Degree(O);
  c := CoefficientIdeals(M);
  if #c eq 0 then c := [1*CoefficientRing(O) : i in [1..n]];
  else assert #c eq n; end if;
  m := Matrix(M); assert Nrows(m) eq n;
  M := Module([<c[i], m[i]> : i in [1..n]]);
  return Order(O, M:Check := Check);
end intrinsic;

intrinsic PseudoMatrix(M::Mtrx[RngOrd]) -> PMat
  {The pseudomatrix with trivial ideals and matrix M.}
  C := CoefficientRing(M);
  C := MaximalOrder(C);
  return PseudoMatrix([1*C : i in [1..Nrows(M)]], M);
end intrinsic;

intrinsic PseudoMatrix(M::Mtrx[FldOrd]) -> PMat
  {The pseudomatrix with trivial ideals and matrix M.}
  C := CoefficientRing(M);
  C := MaximalOrder(C);
  return PseudoMatrix([1*C : i in [1..Nrows(M)]], M);
end intrinsic;

//from Markus
intrinsic Generators(M::ModDed : Minimal:= false) -> []
    {A (minimal) sequence of generators of the module M over its base ring}
    if Minimal then
	MM:= SteinitzForm(M);
	Gens:= [];
	P:= PseudoGenerators(MM); 
	n:= #P;
	for i in [1..n] do
	    p:= P[i];
	    ok, x:= IsPrincipal(p[1]);
	    assert i eq n or ok;
	    if ok then 
		Append(~Gens, p[2] * x); 
	    else 
		Gens cat:= [ g*p[2] : g in Generators(p[1]) ]; 
	    end if;
	end for;
    else
	P:= PseudoBasis(M);
	Gens:= [ g*p[2] : g in Generators(p[1]), p in P ];
    end if;
    return Gens;
end intrinsic;

intrinsic GeneratorMatrix(Q::ModDed) -> Mtrx // MW
{The Generators of a Dedekind module as a matrix}
 G:=Generators(Q:Minimal); if #G eq 0 then G:=[BaseRing(Q)|]; end if;
 return Matrix(#G,Degree(Q),G); end intrinsic;

intrinsic GramMatrix(Q::ModDed) -> Mtrx // MW
{The Gram matrix of the Generators (not [Pseudo]Basis) of a Dedekind module}
 GM:=GeneratorMatrix(Q);
 return GM*InnerProductMatrix(Q)*Transpose(GM); end intrinsic;

// from Markus
intrinsic DirectSum(Q::[ModDed]) -> ModDed, SeqEnum[Map], SeqEnum[Map]
{The direct sum of the modules in Q, together with a sequence containing
 the embedding maps, and a sequence containing the projection maps}
    require not IsEmpty(Q): "The sequence cannot be empty";
    embed_types := {Type(EmbeddingSpace(q)) : q in Q};
    require #embed_types eq 1 or &and{ISA(x, y) or
	ISA(y, x) : x, y in embed_types}: "EmbeddingSpaces must be compatible";
    E:= [ EmbeddingSpace(q): q in Q ];
    if &or[BaseRing(e) cmpne BaseRing(E[1]) : e in E]
        or not IsField(BaseRing(E[1])) then
	E := [<a, b> where a, b :=
		ChangeRing(e, FieldOfFractions(BaseRing(e))) : e in E];
	Em := [x[2] : x in E];
	E := [x[1] : x in E];
	if &or[BaseRing(e) cmpne BaseRing(E[1]) : e in E] then
	    assert #E gt 1;
	    C := CoveringStructure(BaseRing(E[1]), BaseRing(E[2]));
	    for i in [3 .. #E] do
		C := CoveringStructure(C, BaseRing(E[i]));
	    end for;
	    E := [<a, b> where a, b := ChangeRing(e, C) : e in E];
	    Em := [Em[i]*E[i][2] : i in [1 .. #E]];
	    E := [x[1] : x in E];
	end if;
    else
	Em := [Coercion(e, e) : e in E];
    end if;
    V, I:= DirectSum(E);
    M:= Module( [ < b[1], b[2] @ Em[i] @ I[i] > :
		   b in PseudoBasis(Q[i]), i in [1..#Q]] );
    II:= [ map< Q[i] -> M | x :-> (E[i] ! Eltseq(x)) @ I[i], y:-> (V !
    Eltseq(y)) @@ I[i] > : i in [1..#I] ];
    PP:= [ g^-1: g in II ];
    return M, II, PP;
end intrinsic;

intrinsic DirectSum(M1::ModDed, M2::ModDed) -> ModDed, Map, Map, Map, Map
{The direct sum D of the modules M1 and M2, together with the embedding maps
M1 -> D, M2 -> D and the projection maps D -> M1, D -> M2}
    require BaseRing(M1) cmpeq BaseRing(M2): "Incompatible base rings";
    D, I, P:= DirectSum([M1, M2]);
    return D, I[1], I[2], P[1], P[2];
end intrinsic;

intrinsic KernelModule(M::Mtrx) -> ModDed
{Given a matrix over an absolute maximal order,
 return its kernel as a Dedekind module}
 O:=BaseRing(M); require ISA(Type(O),RngOrd): "Must be over number ring";
 require IsMaximal(O): "Must be over maximal order";
 require IsAbsoluteOrder(O): "Order must be absolute";
 A:=InternalKernelModule(M); return Module(Rows(A)); end intrinsic;
