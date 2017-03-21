freeze;

// Bernd Souvignier
// June 1997

declare attributes Lat: DirichletVert, DirichletPlanes;

Z := IntegerRing();
Q := RationalField();

function OverZQ(L)
    R := BaseRing(L);
    return R cmpeq Z or R cmpeq Q;
end function;

Jump := function( F )	// get the minimal difference between the norms of
			// a lattice specified by the Gram matrix F
n := Nrows(F);
QF := MatrixRing(Q, n) ! (2*F);
for i in [1..n] do
	QF[i][i] /:= 2;
end for;
lcm := Lcm( [ Denominator(x) : x in Eltseq(QF) ] );
gcd := Gcd( [ Z!(lcm*x) : x in Eltseq(QF) ] );
return gcd/lcm;

end function;



Simplex := function( L ) // get a simplex containing the Voronoi cell
			 // the hyperplanes are defined by a reduced basis
			 // of the lattice and the negative sum over the basis
n := Dimension(L);
d := Degree(L);
V := RSpace(Q, d);
B := BasisMatrix( LLL(L) );
S := [ V!B[i] : i in [1..Nrows(B)] ];
Append(~S, - &+S);
S[n+1] := S[n+1] / Gcd( Coordinates(L!S[n+1]) );
return S, [ Norm(L!s) / 2 : s in S ];

end function;



Initialize := function( L, P, nP )	// get the vertices of the simplex

n := Dimension(L);
W := RSpace(Q, n);
d := Degree(L);
B := RMatrixSpace(Q, n, d) ! BasisMatrix(L);
Vert := {@ @};
for i in [1..n+1] do
	C := RMatrixSpace(Q, n, d) ! [ P[j] : j in [1..n+1] | j ne i ];
	A := B * Transpose(C);
	y := [ nP[j] : j in [1..n+1] | j ne i ];
	x := Solution(A, W!y);
	Include(~Vert, x*B);
end for;
return Vert;

end function;



Intersect := procedure(L, h, ~V, ~nV, ~P, ~nP, ~PconV, ~VonP, ~N, ~aV, ~aP)
		// intersect the polytope computed so far with the halfspace
		// defined by h (i.e. the points x with (x,h) <= (h,h)/2)
n := Dimension(L);
d := Degree(L);
W := RSpace(Q, d);
I := MatrixRing(Q, d) ! InnerProductMatrix(L);
hI := h*I;
nh := (hI,h) / 2;
outh := {};	// points outside the halfspace defined by h
onh := {};	// points on the hyperplane defined by h
inh := {};	// points inside the halfspace defined by h


for i in aV do
	scp := (hI, V[i]);
	if scp gt nh then
		Include(~outh, i);
	elif scp eq nh then
		Include(~onh, i);
	else
		Include(~inh, i);
	end if;
end for;

if #outh eq 0 then
// the hyperplane is not relevant
	return;
end if;

// h defines a new relevant hyperplane
Append(~P, hI);
Append(~nP, nh);
Append(~VonP, onh);
Include(~aP, #P);
for i in onh do
	Include(~PconV[i], #P);
end for;
// remove the vertices lying outside
aV := aV diff outh;

oner := 1/1;
notinh := outh join onh;
for i in outh do
	Vi := V[i];
	for j in N[i] diff notinh do
// the intersection of the hyperplane with the line through V[i] and V[j]
// is a new vertex v, which satisfies the equation (h,v) = nh/2
// and is of the form v = V[i] + c*(V[j]-V[i]) with 0 < c < 1
		c := ( nh - (hI,Vi) ) / ( hI, V[j]-Vi );
		v := (oner-c) * Vi + c * V[j];
		ind := Index(V, v);
		if ind eq 0 then
			ind := #V+1;
			Include(~V, v);
			Append(~nV, (v*I,v));
			Append(~N, {});
			Include(~aV, ind);
			Include(~onh, ind);
// find the hyperplanes in which the new vertex is contained
			Append(~PconV, {});
			for k in aP do
				if (v, P[k]) eq nP[k] then
					Include(~PconV[ind], k);
					Include(~VonP[k], ind);
				end if;
			end for;
		end if;
// the new vertex is a neighbour of V[j]
		Include(~N[ind], j);
		Include(~N[j], ind);
	end for;
end for;

// remove the outside vertices from the lists
irrP := {};	// hyperplanes that become irrelevant
for i in (aP diff {#P}) do
	VonP[i] := VonP[i] diff outh;
// check, whether P[i] is relevant, i.e. whether P[i] contains a point in inh
	if #(VonP[i] diff onh) eq 0 then
		Include(~irrP, i);
		Exclude(~aP, i);
	end if;
end for;
for i in aV do
	N[i] := N[i] diff outh;
	PconV[i] := PconV[i] diff irrP;
end for;

// find the neighbours in the new relevant hyperplane
for i in onh do
	for j in onh diff (N[i] join {i}) do
		cP := PconV[i] meet PconV[j];
		if #cP ge n-1 then
// two vertices are neighbours if they lie in a 1-dimensional space
// obtained as the intersection of relevant hyperplanes
			if Rank( RMatrixSpace(Q, #cP, d)![ P[k] : k in cP ] ) ge n-1 then
				Include(~N[i], j);
				Include(~N[j], i);
			end if;
		end if;
	end for;
end for;

vprint Voronoi: #aV, "vertices,", #aP, "planes";
rad := Maximum([ nV[j] : j in aV ]);
min := Minimum([ nV[j] : j in aV ]);
vprint Voronoi: "covering radius <=", rad, "(minimum", min, ")";

end procedure;



Dirichlet := function( L ) // internal function, the data computed by this
			   // function should be stored with the lattice

if assigned L`DirichletVert then
    return L`DirichletVert, L`DirichletPlanes;
end if;

n := Dimension(L);
d := Degree(L);
V := RSpace(Q, d);
I := MatrixRing(Q, d) ! InnerProductMatrix(L);
II := I^-1;
eps := Jump(GramMatrix(L));

// find n+1 hyperplanes forming a closed simplex containing 0
// hyperplane is given by h*I to get inner product right
Planes, normPlanes := Simplex(L);
Planes := [ h*I : h in Planes ];
// find the vertices of this simplex
Vert := Initialize(L, Planes, normPlanes);
normVert := [ (v*I,v) : v in Vert ];
// Vert[i] lies on all hyperplanes except Plane[i]
PconV := [ { j : j in [1..n+1] | j ne i } : i in [1..n+1] ];
// Plane[i] contains all vertices except Vert[i]
VonP := PconV;
// Vert[j] is a neighbour of Vert[i] for j != i
Neigh := PconV;
activeV := { 1..n+1 };
activeP := { 1..n+1 };

rad := Maximum([ normVert[i] : i in activeV ]);
vprint Voronoi: "covering radius <=", rad;

len := Minimum([ 2*nP : nP in normPlanes ]);
// start with hyperplanes defined by short vectors and their negatives
SV := ShortVectors(L, len);
H := &cat[ [v[1], -v[1]] : v in SV ];
vprint Voronoi: "start with", #H, "vectors of norm", len;

done := false;
while not done do
	for h in H do
// assume that short vectors are sorted by norm
		if Norm(h)/4 ge rad then
			done := true;
			break;
		end if;
// intersect polytope with a new hyperplane
		Intersect(L, V!h, ~Vert, ~normVert, ~Planes, ~normPlanes, ~PconV, ~VonP, ~Neigh, ~activeV, ~activeP);
		rad := Maximum([ normVert[j] : j in activeV ]);
	end for;
// hyperplanes defined by vectors of bigger length have to be considered
	len +:= eps;
	if len/4 ge rad then
		done := true;
	else
		SV := ShortVectors(L, len, len);
		if #SV gt 0 then
			H := &cat[ [v[1], -v[1]] : v in SV ];
			vprint Voronoi: "consider", #H, "vectors of norm", len;
		else
			H := [];
		end if;
	end if;
end while;
radii := Sort(Setseq({ normVert[j] : j in activeV }));
vprint Voronoi: radii;
vprint Voronoi: [ #[ j : j in activeV | normVert[j] eq r ] : r in radii ];
vprint Voronoi: "required", #Vert, "vertices and", #Planes, "planes";
// renumber relevant vertices, neighbours accordingly
act := Setseq(activeV);
l := [ 0 : i in [1..#Vert] ];
for i in [1..#act] do
	l[act[i]] := i;
end for;
for i in act do
	Neigh[i] := { l[j] : j in Neigh[i] };
end for;

L`DirichletVert := [ <Vert[j], normVert[j], Neigh[j]> : j in act ];
L`DirichletPlanes := [ Planes[j]*II : j in activeP ];

return L`DirichletVert, L`DirichletPlanes;
end function;



intrinsic VoronoiCell(L::Lat) -> [], {}, []
{The Voronoi cell of lattice L, as the vertices (a sequence of vectors),
the set of edges, and the planes (a sequence of vectors)}

require OverZQ(L): "Argument 1 must be over Z or Q";

Vert, Planes := Dirichlet(L);
Edges := &join{ { {i,j} : j in Vert[i][3] } : i in [1..#Vert] };
return [ v[1] : v in Vert ], Edges, Planes;

end intrinsic;



intrinsic VoronoiGraph(L::Lat) -> Grph
{The Voronoi graph of lattice L}

require OverZQ(L): "Argument 1 must be over Z or Q";

Vert := Dirichlet(L);
return Graph< {@ v[1] : v in Vert @} | [ v[3] : v in Vert ] >;

end intrinsic;



intrinsic Holes(L::Lat) -> []
{The holes of lattice L}

require OverZQ(L): "Argument 1 must be over Z or Q";

Vert := Dirichlet(L);
return [ v[1] : v in Vert ];

end intrinsic;



intrinsic DeepHoles(L::Lat) -> []
{The deep holes of lattice L}

require OverZQ(L): "Argument 1 must be over Z or Q";

Vert := Dirichlet(L);
rad := Maximum([ v[2] : v in Vert ]);
return [ v[1] : v in Vert | v[2] eq rad ];

end intrinsic;



intrinsic CoveringRadius(L::Lat) -> FldRatElt
{The squared covering radius of lattice L}

require OverZQ(L): "Argument 1 must be over Z or Q";

Vert := Dirichlet(L);
rad := Maximum([ v[2] : v in Vert ]);
return rad;

end intrinsic;



// The following intrinsic was provided by David Teusner (david.teusner@upb.de)
// and implements Section C of 
// Agrell, Eriksson, Vardy, Zeger, Closest point search in lattices,
// IEEE Transactions on Information Theory, 48 (2002), 2201--2214.

intrinsic VoronoiRelevantVectors(L :: Lat) -> SeqEnum
{The Voronoi-relevant hyperplanes/vectors of the lattice L}

if not assigned L`DirichletPlanes then
  DimL := Dimension(L);
  num_iterations := 2^DimL-1;

  // Preparing a list for the Voronoi relevant vectors.
  vor := [];

  // Enumerating the numbers from 1 to 2^n-1 where n is the rank of the lattice.
  // For all these numbers
  // we compute their binary representation and turn that into a vector 
  // of length n. This vector will then be used to compute a representative
  // of an equivalence class of L/2L.
  for i in [1..num_iterations] do
    // Compute the binary representation.
    j := Intseq(i,2);
    // Add some zeros to get a vector of length n
    j cat:= [0^^(DimL - #j)];

    // Get the lattice point v with linearcoefficients as in the list j
    v := Coordelt(L, j);

    // Compute a list of all closest vectors to the midpoint.
    cvp := ClosestVectors(L, v/2);

    // If there are exactly 2..
    if #cvp eq 2 then
      // ..then compute the difference of these two vectors and add it 
      Append(~vor, cvp[2] - cvp[1]);
    end if;
  end for;

  L`DirichletPlanes := vor cat [-v : v in vor];
end if;
return L`DirichletPlanes;
end intrinsic;
