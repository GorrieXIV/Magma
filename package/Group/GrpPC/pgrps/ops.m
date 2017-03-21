freeze;

/*
 * Function for calculating a complete list of images for all pc
 * generators from a list of images of the group generators.
 * The input is the group G, a sequence of tuples and a sequence
 * of pairs indicating the definitions of the pc generators.
 * The output is the completed list of tuples.
 */

/* Modified by D Howden Summer 2011: only check the params if assertions are set
   higher than 1.  By default it now jumps to internal equivalent.
*/

intrinsic CompleteTupleList (G::GrpPC, S::SeqEnum, D::SeqEnum) -> SeqEnum
{ Given a p-group G and a list of tuples [<G.i, W.i>] for the generators
  of G, returns a list of tuples for the pc-generators of G. The tuples
  can be used to construct a homomorphism G -> W. D indicates the
  relations which give definitions for the pc-generators. }

   if GetAssertions() gt 1 then
      if Type(S[1]) ne Tup or Type(D[1]) ne SeqEnum then
         error "Bad argument types.";
      end if;

      S1 := { s[1] : s in S };
      SG := { G.s[2] : s in D | s[1] eq 0 };
      if SG notsubset S1 then
         error "Explicit images of the group generators required.";
      end if;
   end if;

   /* Jump to internal version */
   return InternalCompleteTupleList(G, S, D);

end intrinsic;

intrinsic p_hom(P::GrpPC, Q::GrpPC, S::SeqEnum,D::SeqEnum) -> Map
{ Construct the map P->Q of p-groups, given by the list of images of
  the generators of P. D indicates the definitions of pc generators of
  P.}

local O, F;

F := FPGroup(P);
fh := hom<P -> F| [F.i : i in [1..NPCgens(P)]] : Check := false>;

if #S eq NPCgens(P) then
	if Type(S[1]) eq Tup then
		O := [S[i,2] : i in {1..#S}];
	else
		O := S;
	end if;
else
	O := CompleteTupleList(P, S, D);
end if;

h := fh*hom<F -> Q| O : Check := false>;

return h;

end intrinsic;

intrinsic InvHom(h::Map) -> Map
{ Construct the inverse homomorphism of h:GrpPC -> GrpPC. }

local G,H;

G := Domain(h);
H := Codomain(h);
if Type(G) ne GrpPC or Type(H) ne GrpPC then
	error "Cannot calculate inverse: Wrong group types for homomorphism.";
end if;
hi := hom<H -> G| [<h(G.i), G.i>: i in {1..NPCgens(G)}] : Check := false>;

return hi;
end intrinsic;

intrinsic PowHom(h::Map, n::RngIntElt) -> Map
{ Returns the map h^n, the n-th power of the homomorphism h. If the Domain
of H is of type GrpPC, n may be an integer, otherwise n must be greater
or equal to zero.}

local G;

G := Domain(h);

if G ne Codomain(h) then
	error"Domain and Codmain must coincide.";
end if;

if n eq 0 then
	if Type(G) eq GrpPC then
		return hom<G -> G | [ G.i : i in [1..NPCgens(G)]] : Check := false >;
	else
		return hom<G -> G | [ G.i : i in [1..Ngens(G)]] : Check := false >;
	end if;
end if;

if n gt 0 then
	hh := h;
	nn := n;
else
	hh := InvHom(h);
	nn := -n;
end if;

if Type(G) eq GrpPC then
	s := NPCgens(G);
else
	s := Ngens(G);
end if;

II := [];

for i := 1 to s do
	w := G.i;
	for j := 1 to nn do
		w := hh(w);
	end for;

	Append(~II, <G.i, w>);
end for;

return p_hom(G ,G, II, []);

end intrinsic;

intrinsic BuildHom(h::Map) -> Map
{ Given a Map as composition of homs, construct the composition map explicitly.}

local G, H, S;

G := Domain(h);
H := Codomain(h);

S := [];
if Type(G) eq GrpPC then
	n := NPCgens(G);
else
	n := Ngens(G);
end if;

for i := 1 to n do
	Append(~S, h(G.i));
end for;
	
if Type(G) eq GrpPC and Type(H) eq GrpPC then
	return p_hom(G,H, S, []);
else
	return hom<G->H | S : Check := false >;
end if;

end intrinsic;

