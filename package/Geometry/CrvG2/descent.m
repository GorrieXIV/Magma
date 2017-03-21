freeze;
// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

/*************************************
 * Hyperelliptic/descent.m           *
 *                                   *
 * Find Mordell-Weil group           *
 *                                   *
 * Michael Stoll                     *
 *                                   *
 * started 20-Feb-1999               *
 *************************************/

 /*-----------------------------------------------------------------

 CHANGES:
 
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
   (nothing to do)   

   11/3/2011: Jan Steffen Mueller
     Commented out g=2 requirement




 
  TO DO
  
    Implement MordellWeilGroup

  -----------------------------------------------------------------*/

// Some hashtable functions
//
// A hashtable is implemented as a pair <keys, vals>, where 
// + keys is an indexed set
// + vals is a sequence
// such that vals[i] is the value associated to the key keys[i].

// MakeHashtable takes a sequence of pairs <key, val> and constructs
// a hashtable out of it.
function MakeHashtable(PairSeq)
    return <{@ pair[1] : pair in PairSeq @}, [ pair[2] : pair in PairSeq ]>;
end function;

// GetHashValue takes a hashtable and a key and returns the corresponding
// value. If the key is not present in the table and Default is specified,
// returns the default value, otherwise signals an error.
AUniqueObject := "!$%/()&?*+~#";
function GetHashValue(HT, key : Default := AUniqueObject)
    pos := Position(HT[1], key);
    if pos gt 0 then
      return HT[2,pos];
    else
      error if Default eq AUniqueObject,
            "GetHashValue: Key",key,"not present in the table.";
      return Default;
    end if;
end function;

// IsInHashtable takes a hashtable and a key and returns a boolean value
// indicating whether the key is in the table or not. If the key is
// present, the corresponding value is returned as a second value.
function IsInHashtable(HT, key)
    pos := Position(HT[1], key);
    if pos gt 0 then
      return true, HT[2,pos];
    else
      return false, _;
    end if;
end function;

// ExtendHashtable takes a hashtable, a key and a value. It returns the
// updated hashtable. If the key is already present, the corresponding
// value is changed, otherwise the key-value pair is added to the table.
function ExtendHashtable(HT, key, val)
    pos := Position(HT[1], key);
    if pos gt 0 then
      HT[2,pos] := val;
    else
      Include(~HT[1], key);
      Append(~HT[2], val);
    end if;
    return HT;
end function;

function HeightWithHT(HT, P, prec)
    b, val := IsInHashtable(HT, P);
    if b then return val, HT;
    else
      // "HeightWithHT: P = %o", P;
      ht := Height(P : Precision := prec);
      // " --> Height = %o.\n", ht;
      HT := ExtendHashtable(HT, P, ht);
      return ht, HT;
    end if;
end function;

function HeightPairingWithHT(HT, P1, P2, prec)
    ht1, HT := HeightWithHT(HT, P1+P2, prec);
    ht2, HT := HeightWithHT(HT, P1, prec);
    ht3, HT := HeightWithHT(HT, P2, prec);
    return (ht1-ht2-ht3)/2, HT;
end function;

// The following intrinsic takes a sequence of points on a genus 2 Jacobian
// and finds a reduced (w.r.t. the height pairing) basis of the subgroup
// generated by the points in J(Q)/torsion.
MyPrec := func<R | Precision(R)>;

intrinsic ReducedBasis(ps::[JacHypPt] : Precision := 0) -> SeqEnum, AlgMatElt
    {Computes a reduced basis (with respect to the height pairing) of the
    subgroup in J(Q)/torsion generated by the given points on J.}
   // require Dimension(Universe(ps)) eq 2 :
   //     "Universe of argument must be the Jacobian of a genus 2 curve.";
    C := Curve(Universe(ps));
    if Dimension(Universe(ps)) eq 2  then
      K := KummerSurface(Universe(ps)); // this causes K to be stored internally, avoiding
                                      // repeated creation in every call to Height...
    end if;
    if not IsSimplifiedModel(C) then
	C1, m := SimplifiedModel(C);
	ps := [ Evaluate(m,Q) : Q in ps ];
    else
	m := IdentityMap(C);
    end if;
	vprintf JacHypHeight: "ReducedBasis: %o points, prec = %o.\n", #ps, Precision;
    // First compute heights...
prec := Precision eq 0 select MyPrec(RealField()) else Precision;
    vprintf JacHypHeight: " Computing heights...\n";
    ps := Setseq(Seqset(ps));
    psh := [<pt, Height(pt : Precision := prec)> : pt in ps];
    // ...and put them into a hashtable.
    HT := MakeHashtable(psh);
    // Some initialisations
    vprintf JacHypHeight: " Initialising...\n";
    gens := [Universe(ps) | ];
    pairing := []; // [ ... [ ... pairing(gen[i],gen[j]) ... ] ... ]
    points := { pt[1] : pt in psh | pt[2] gt 0.5 or Order(pt[1]) eq 0 };
    // Now repeatedly take the point of smallest positive height,
    // adjoin it to the generators, update the pairing matrix,
    // and reduce the remaining points w.r.t. the lattice generated so far.
    mat0 := MatrixRing(RealField(), #gens)!0;
    while not IsEmpty(points) do
      // Find point of smallest height.
      cht := 0;
      for pt in points do
        ht, HT := HeightWithHT(HT, pt, prec);
        if cht eq 0 or ht lt cht then
          cht := ht; cpt := pt;
        end if;
      end for;
      // Update gens and pairing.
      vprintf JacHypHeight: "  New possible generator %o of height %o\n", cpt, cht;
      Append(~gens, cpt);
      for i := 1 to #gens - 1 do
        val, HT := HeightPairingWithHT(HT, gens[i], cpt, prec);
        Append(~pairing[i], val);
      end for;
      Append(~pairing, [ pairing[i, #gens] : i in [1..#gens-1] ] cat [cht]);
      Mat := MatrixRing(RealField(), #gens);
      mat0 := Mat!&cat pairing;
      while not IsPositiveDefinite(mat0) do
        mat0 +:= 0.1^prec*(Mat!1);
      end while;
      // Generate the appropriate lattice.
      L := LatticeWithGram(mat0);
      L1 := LLL(L); B := Basis(L1);
      gens := [ &+[Round(b[i])*gens[i] : i in [1..#gens]] : b in B ];
      new_gens := [];
      for g in gens do
        ht, HT := HeightWithHT(HT, g, prec);
        if ht gt 0.5 or Order(g) eq 0 then Append(~new_gens, g); end if;
      end for;
      gens := new_gens;
      vprintf JacHypHeight: "  Current generators:\n%o\n", gens;
      pairing := [];
      for i := 1 to #gens do
        for j := 1 to i-1 do
          val, HT := HeightPairingWithHT(HT, gens[j], gens[i], prec);
          Append(~pairing[j], val);
        end for;
        ht, HT := HeightWithHT(HT, gens[i], prec);
        Append(~pairing, [ pairing[j, i] : j in [1..i-1] ] cat [ht]);
      end for;
      Mat := MatrixRing(RealField(), #gens);
      mat0 := Mat!&cat pairing;
      V := RSpace(RealField(), #gens);
      vprintf JacHypHeight: "  Current pairing matrix:\n%o\n", mat0;
      mat := mat0^-1;
      // Project the points into the real space spanned by the lattice,
      // find a close vector and compute the difference.
      newPoints := { Universe(ps) | };
      for pt in points do
        proj := [];
        for i := 1 to #gens do
          proji, HT := HeightPairingWithHT(HT, gens[i], pt, prec);
          Append(~proj, proji);
        end for;
        w := (V!proj)*mat;
        v := [ Round(w[i]) : i in [1..#gens] ];
        npt := pt - &+[ Round(v[i])*gens[i] : i in [1..#gens] ];
        nht, HT := HeightWithHT(HT, npt, prec);
        if nht gt 0.5 or Order(npt) eq 0 then Include(~newPoints, npt); end if;
      end for;
      points := newPoints;
      vprintf JacHypHeight: "  Number of remaining points: %o.\n", #points;
    end while;
    vprintf JacHypHeight: " Generators:\n%o\n", gens;
    return [ Pullback(m,Q) : Q in gens ], mat0;
end intrinsic;

intrinsic ReducedBasis(ps::{@JacHypPt@} : Precision := 0) -> SeqEnum, AlgMatElt
    {Computes a reduced basis (with respect to the height pairing) of the
    subgroup in J(Q)/torsion generated by the given points on J. }
    //require Dimension(Universe(ps)) eq 2 :
    //    "Universe of argument must be the Jacobian of a genus 2 curve.";
    return ReducedBasis(IndexedSetToSequence(ps) : Precision := Precision);
end intrinsic;

intrinsic ReducedBasis(ps::{JacHypPt} : Precision := 0) -> SeqEnum, AlgMatElt
    {Computes a reduced basis (with respect to the height pairing) of the
    subgroup in J(Q)/torsion generated by the given points on J. }
    //require Dimension(Universe(ps)) eq 2 :
    //    "Universe of argument must be the Jacobian of a genus 2 curve.";
    return ReducedBasis(SetToSequence(ps) : Precision := Precision);
end intrinsic;