freeze;

/* This file contains some intrinsics to define conformal versions of the
 * classical groups. That is, the groups that fix the form mod scalars.
 * This will contain the "general"version of the classical group.
 * e.g. GOPlus(d,q) <= CGOPlus(d,q),
 * and the special version of determinant 1 matrices
 * e.g. SOPlus(d,q) <= CSOPlus(d,q)
 * Projective versions are also defined.
 * e.g. PGOPlus(d,q) <= PCGOPlus(d,q).
 * But many of these are the same as the "PG" version - e.g. PCGU = PGU.
 
 Commented out definitions for CGSp and CGU and then added these names
 to the bind file c.b as synonyms for CSp and CU. (DET 2011-05-13)
 
 Definitions for the matrix groups moved to Group/GrpMat/conformal.m
 (DET 2010-05-16)
 
 */

// import "classicals.m": NormSpMinusSp, NormGOMinusGO, GOMinusSO;
// import "superfield.m": MatToQ;

/*
intrinsic CGU(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal unitary group}
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  return S where S := sub< GL(d,q^2) | GU(d,q), ScalarMatrix(d,w) >
          where w := PrimitiveElement(GF(q^2));
end intrinsic;


intrinsic CSU(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal special unitary group}
  local w, mform, trans, W, Y, zpow, ypow, gen;
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if GCD(q-1,d) eq 1 then
    return G where G := SU(d,q);
  end if;
  mform := Matrix(GF(q^2),d,d, [<i,d+1-i,1>:i in [1..d]]);
  trans := CorrectForm(mform,d,q^2,"unitary");
  w := PrimitiveElement(GF(q^2));
  W := GL(d,q^2)!ScalarMatrix(GF(q^2),d,w);
  Y := DiagonalMatrix(GF(q^2),[w^(q-1)] cat [1:i in [1..d-1]]);
  Y := trans * Y * trans^-1; //Y is generator of GU/SU
  zpow := (q-1) div GCD(d,q-1);
  ypow := (-d * zpow div (q-1));
  gen := W^zpow * Y^ypow;
  if gen * mform * Transpose(MatToQ(gen,q)) eq mform then //fixes form already
    return S where S := SU(d,q);
  else
    return S where S := sub< SL(d,q^2) | SU(d,q), W^zpow * Y^ypow >;
  end if;
end intrinsic;
*/

intrinsic PCGU(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective conformal unitary group - same as PGU}
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  return G where G := PGU(d,q); //don't want second return value!
end intrinsic;

intrinsic PCSU(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective conformal unitary group - same as PSU}
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if GCD(q-1,d) eq 1 then
    return G where G := PSU(d,q);
  end if;
  return S where S := OrbitImage(G,sub<V|V.1>) where V:=VectorSpace(G)
                        where G := CSU(d,q);
end intrinsic;

/* Oh dear! This CSp exists already - I'll call it CGSp. */
/*
intrinsic CGSp(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal symplectic group}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return S where S := sub< GL(d,q) | Sp(d,q), ScalarMatrix(d,w) >
            where w := PrimitiveElement(GF(q));
  else
    return S where S := sub< GL(d,q) | Sp(d,q), NormSpMinusSp(d,q) >;
  end if;
end intrinsic;
*/

intrinsic PCGSp(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective conformal symplectic group}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return G where G := PSp(d,q);
  else
    return OrbitImage(G,sub<V|V.1>) where V:=VectorSpace(G)
                      where G := CGSp(d,q);
  end if;
end intrinsic;

/*
intrinsic CGO(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal orthogonal group in odd dimension}
  require IsOdd(d) : "Argument 1 must be odd";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if q gt 3 then
    return S where S := sub< GL(d,q) | GO(d,q), ScalarMatrix(d,w) >
            where w := PrimitiveElement(GF(q));
  else return G where G := GO(d,q);
  end if;
end intrinsic;

intrinsic CSO(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal special orthogonal group in odd dimension}
  require IsOdd(d) : "Argument 1 must be odd";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if GCD(d,q-1) gt 1 then
    return S where S := sub< SL(d,q) | SO(d,q), ScalarMatrix(d,w^p) >
            where w := PrimitiveElement(GF(q)) where p := (q-1) div GCD(d,q-1);
  else return G where G := SO(d,q);
  end if;
end intrinsic;
*/
intrinsic PCGO(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective conformal orthogonal group in odd dimension - same as PGO}
  require IsOdd(d) : "Argument 1 must be odd";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  return G where G := PGO(d,q);
end intrinsic;

intrinsic PCSO(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective special conformal orthogonal group in odd dimension - same as PSO}
  require IsOdd(d) : "Argument 1 must be odd";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  return G where G := PSO(d,q);
end intrinsic;

/*
intrinsic CGOPlus(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal orthogonal group of plus type}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return S where S := sub< GL(d,q) | GOPlus(d,q), ScalarMatrix(d,w) >
            where w := PrimitiveElement(GF(q));
  else
    return S where S := sub< GL(d,q) | GOPlus(d,q), NormGOMinusGO(d,q,1) >;
  end if;
end intrinsic;

intrinsic CSOPlus(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal special orthogonal group of plus type}
  local W, X, Y, Z, gens, hd;
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    if GCD(d,q-1) ne 1 then
      return S where S := sub< SL(d,q) | SOPlus(d,q), ScalarMatrix(d,w^p) >
            where w := PrimitiveElement(GF(q)) where p := (q-1) div GCD(d,q-1);
      else return S where S := SOPlus(d,q);
    end if;
  end if;

  Z := ScalarMatrix(GF(q),d,w) where w:=PrimitiveElement(GF(q));
  hd := d div 2;
  X := GOMinusSO(d,q,1);
  Y := NormGOMinusGO(d,q,1);
  //Normaliser in SL is generated by SO together with elements
  //X^x Y^y Z^z with x(q-1)/2 + yd/2 + zd = 0 mod q-1
  W := Matrix(Integers(),4,1,[(q-1) div 2, hd, d, q-1]);
  N := Nullspace(W);
  gens := [ X^n[1] * Y^n[2] * Z^n[3] : n in Generators(N) ];
  return sub< SL(d,q) | SOPlus(d,q), gens >;
end intrinsic;
*/

intrinsic PCGOPlus(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective conformal orthogonal group of plus type}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return G where G := PGOPlus(d,q);
  else
    return OrbitImage(G,sub<V|V.1>) where V:=VectorSpace(G)
                      where G := CGOPlus(d,q);
  end if;
end intrinsic;

intrinsic PCSOPlus(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective conformal special orthogonal group of plus type}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return G where G := PSOPlus(d,q);
  else
    return OrbitImage(G,sub<V|V.1>) where V:=VectorSpace(G)
                      where G := CSOPlus(d,q);
  end if;
end intrinsic;

/*
intrinsic CGOMinus(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal orthogonal group of minus type}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return S where S := sub< GL(d,q) | GOMinus(d,q), ScalarMatrix(d,w) >
            where w := PrimitiveElement(GF(q));
  else
    return S where S := sub< GL(d,q) | GOMinus(d,q), NormGOMinusGO(d,q,-1) >;
  end if;
end intrinsic;

intrinsic CSOMinus(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal special orthogonal group of minus type}
  local W, X, Y, Z, gens, hd;
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    if GCD(d,q-1) ne 1 then
      return S where S := sub< SL(d,q) | SOMinus(d,q), ScalarMatrix(d,w^p) >
            where w := PrimitiveElement(GF(q)) where p := (q-1) div GCD(d,q-1);
      else return S where S := SOMinus(d,q);
    end if;
  end if;

  Z := ScalarMatrix(GF(q),d,w) where w:=PrimitiveElement(GF(q));
  hd := d div 2;
  X := GOMinusSO(d,q,-1);
  Y := NormGOMinusGO(d,q,-1);
  //Normaliser in SL is generated by SO together with elements
  //X^x Y^y Z^z with x(q-1)/2 + yd/2 + zd = 0 mod q-1
  W := Matrix(Integers(),4,1,[(q-1) div 2, hd, d, q-1]);
  N := Nullspace(W);
  gens := [ X^n[1] * Y^n[2] * Z^n[3] : n in Generators(N) ];
  return sub< SL(d,q) | SOMinus(d,q), gens >;
end intrinsic;
*/

intrinsic PCGOMinus(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective conformal orthogonal group of minus type}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return G where G := PGOMinus(d,q);
  else
    return OrbitImage(G,sub<V|V.1>) where V:=VectorSpace(G)
                      where G := CGOMinus(d,q);
  end if;
end intrinsic;

intrinsic PCSOMinus(d:: RngIntElt, q:: RngIntElt) -> GrpPerm
{Projective conformal special orthogonal group of minus type}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return G where G := PSOMinus(d,q);
  else
    return OrbitImage(G,sub<V|V.1>) where V:=VectorSpace(G)
                      where G := CSOMinus(d,q);
  end if;
end intrinsic;
