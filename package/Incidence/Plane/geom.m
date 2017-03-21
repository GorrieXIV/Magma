freeze;

forward BaerSubplane, fConicOval, fHallOval;

//-----------------------------------------------------------------------------
intrinsic BaerDerivation(q2::RngIntElt) -> PlaneAff, PlanePtSet, PlaneLnSet
{An affine plane constructed by the technique of derivation w.r.t. a Baer subplane}
 
   require isp and IsEven(k) and IsPrime(p) where isp, p, k is IsPower(q2):
	"Field size must be an even power of a prime";

   // Construct an affine plane by the technique of derivation with 
   // respect to a Baer subplane
 
   Fq2< w > := FiniteField(q2);
   PPl, Pts, Lns := FiniteProjectivePlane(Fq2);
   G, GPts := CollineationGroup(PPl);
 
   // Construct a Baer subplane
 
   Subplane := SubfieldSubplane(PPl, sub< Fq2 | Degree(Fq2) div 2> );

   // The Baer segment consists of those points of the Baer subplane that lie 
   // on the line at infinity. Take the line x = 0 as the line at infinity.

   LineInf := Lns![1, 0, 0];
   //BaerSeg := Support(Subplane) meet Support(LineInf);
   BaerSeg := Points(Subplane) meet Set(LineInf);
 
   // We now find the subgroup of the collineation group that fixes the Baer
   // segment. The translates of the Baer subplane under this subgroup will
   // give us those Baer subplanes that contain the set BaerSeg.  We use the   
   // G-set GPts to specify the action of G on the point Pts.
 
   StabSeg := Stabilizer(G, GPts, BaerSeg);
 
   // Rather than computing the translates of the entire Baer subplane, we   
   // compute the translates of SubPlane - BaerSeg so that we get exactly 
   // those sets which become new affine lines.

   //BaerLines := Orbit(StabSeg, GPts, Support(Subplane) diff BaerSeg);
   BaerLines := Orbit(StabSeg, GPts, Points(Subplane) diff BaerSeg);

   // We complete the new plane by taking those lines of PG(2, q^2) which
   // intersect the line at infinity at points other than those in the Baer
   // segment. Upon removing the intersection point with LineInf, each such
   // line becomes a line of the new affine plane.

   //ALns := BaerLines join { Set(l) diff LineInf : l in Lns | 
   //                             IsDisjoint(BaerSeg, Support(l)) };
   BaerSeg_set := Set(BaerSeg);
   ALns := BaerLines join { Set(l) diff LineInf : l in Lns | 
                                IsDisjoint(BaerSeg_set, Set(l)) };
 
   return FiniteAffinePlane< SetToIndexedSet(&join(ALns)) | [Set(s): s in ALns] 
                                       : Check := false >;

end intrinsic; /*BaerDerivation*/

//-----------------------------------------------------------------------------
intrinsic OvalDerivation(q::RngIntElt: HallOval := false, Print := 0) -> PlaneAff, PlanePtSet, PlaneLnSet
{A translation plane from PG(2, q) by derivation w.r.t. an oval}

   // Construct a translation plane from PG(2, q) by derivation with
   // respect to an oval.

   require q gt 0 and IsPowerOf(q, 2) :
			"Field size must be a positive power of two";
   require not HallOval or q eq 16 :
			"Hall ovals are only available for PG(2, 16)";

   Fq< w > := FiniteField(q) ;
   PPl, Pts, Lns := FiniteProjectivePlane(Fq);
   G, GPts, GLns := CollineationGroup(PPl);

   // Construct an oval Oval
   Oval := HallOval select fHallOval(PPl) else fConicOval(PPl);

   // Choose points P and Q on the Oval and find the line PQ
   P := Rep(Oval);
   Q := Rep(Exclude(Oval, P));
   PQ := Lns ! [ P, Q ];

   // We choose a point X not on the line PQ: this will certainly be true 
   // if X is chosen to be on the oval
   X := Rep(Oval diff {P, Q});
   XP := Lns![X, P];
   XQ := Lns![X, Q];

   /* Construct:
      H1: the group of central collineations with axis PQ
      H2: the group of elations with centre P and axis PQ
      H3: the group of homologies with centre P and axis XQ
      H4: the group of central collineations with centre P and axis
          through Q */

   H1 := Stabilizer(G, GPts, Setseq(Set(PQ)));
   H2 := SylowSubgroup(Stabilizer(H1, GLns, XP), 2);
   H3 := Stabilizer(Stabilizer(G, GPts, P), GPts, Setseq(Set(XQ)) );
   H4 := sub< G | H2, H3 >;

   if Print gt 0 then
       print "\nThe group of central collineations with centre P and axis";
       print "through Q has order", Order(H4);
   end if;

   /* We construct the set ALns containing the lines of the new plane.
      They are:
        the translates of oval (excluding P and Q) under the 
        central collineations:
        the lines of PG(2, Fq) (excluding PQ) that are incident with P;
        the lines of PG(2, Fq) (excluding PQ) that are incident with Q */

   ALns := Orbit(H4, GPts, Oval diff {P, Q}) 
                         join 
           { Exclude(Set(l), Y) : l in Lns, Y in {P,Q} | l ne PQ and Y in l };
   if Print gt 0 then
       print "\nThe", #ALns, "affine lines have been constructed.";
   end if;

   APts := &join ALns;
   return FiniteAffinePlane< SetToIndexedSet(APts) | Setseq(ALns) >;

end intrinsic; /* OvalDerivation */

//-----------------------------------------------------------------------------
intrinsic BaerSubplane(PPl::PlaneProj) -> PlaneProj, PlanePtSet, PlaneLnSet
{A Baer subplane of PPl}

   // Construct a Baer subplane of PG(2, q^2). We take the one corresponding 
   // to those points of PG(2, q^2) having all their coordinates in GF(q)

   Fq2 := Field(PPl);
   return SubfieldSubplane(PPl, sub<Fq2 | Degree(Fq2) div 2>);

end intrinsic; /*BaerSubplane*/


//-----------------------------------------------------------------------------
fConicOval := function(PPl)

   // Construct the oval defined by the points of the conic y^2 = xz 
   // together with the nucleus, in PG( 2, q), where q has even characteristic. 

   P := PointSet(PPl);
   Fq := Field(PPl);
   return { P![1,a,a^2] : a in Fq } join { P![0,0,1], P![0,1,0] };

end function; /* ConicOval */


//-----------------------------------------------------------------------------
fHallOval := function(Pl)

   // Construct a Hall oval in the plane of order 16

   P := PointSet(Pl);
   Fq := Field(Pl);
   error if #Fq ne 16, "Error: Hall oval only available for the plane PG(2, 16).";

   w := PrimitiveElement(Fq);
   R := PolynomialRing(Fq); x := R.1;
   z := w^4*x^14 + w^24*x^12 + w^12*x^10 + w^18*x^8 + 
        w^10*x^6 + w^10*x^4  + w^12*x^2;
   return { P![0, 1, 0], P![0, 0, 1] }  
                       join 
          { P![1, a, Evaluate(z, a)] : a in Fq };

end function; /* HallOval */

