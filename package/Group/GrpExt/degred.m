freeze;
 
forward DegreeReductionH;
PermutationRepresentationSumH := function(G,reps)
/* reps should be a list of homomorphisms from group G to permutation
 * groups (subgroups of Sym(n_i)). The summed permutation representation
 * reps[1]+..resp[r] of degree n_1+n_2+..n_r is returned, together
  * with the image group.
 */
  local nreps, degrees, phi, cdphi, g, ims, img, sumdeg, deg, cd, cdgens;
  nreps := #reps;
  degrees := [];
  sumdeg := 0;
  for j in [1..nreps] do
    phi:=reps[j];
    if Domain(phi) cmpne G then
      error
    "Domain of maps in reps must be G in PermutationRepresentationSum(G,reps)";
    end if;
    cdphi :=  Codomain(phi);
    if Category(cdphi) ne GrpPerm then
      error
  "Codomain of maps must be perm-gps in PermutationRepresentationSum(G,reps)";
    end if;
    degrees[j]:=Degree(cdphi);
    sumdeg +:= degrees[j];
  end for;
  deg:=sumdeg;

  // The codomain of the summed representation will be the direct product of the
  // codomains of the given maps.
  cdgens := [Sym(deg)|];
  sumdeg := 0;
  for j in [1..nreps] do
    for g in Generators(Codomain(reps[j])) do
      Append(~cdgens,[i:i in [1..sumdeg]] cat
            [i^g + sumdeg : i in [1..degrees[j]]] cat
            [i : i in [sumdeg+degrees[j]+1..deg]]);
    end for;
    sumdeg +:= degrees[j];
  end for;

  cd := sub<Sym(deg)|cdgens>;
  ims := [cd|];
  for i in [1..Ngens(G)] do
    g := G.i;
    img:=[];
    sumdeg:=0;
    for j in [1..nreps]  do
      for k in [1..degrees[j]] do
        img[sumdeg+k] := sumdeg + k^reps[j](g);
      end for;
      sumdeg +:= degrees[j];
    end for;
    Append(~ims,img);
  end for;

  return hom<G -> cd | ims >, sub<cd|ims>;

end function;

DegreeReductionH := function(G:maxdeg:=100,tried:={})
/* G should be a permutation group.
 * Attempt at an improved version of DegreeReduction.
 * Returns perm gp G' of degree <= degree of G, plus homomorphism phi:G->G'
 */
  local fac, sylords, primes,
        iphi, l, act, Q, QR, phi, actn, Qn, QRn, phin, phir, deg;
  G, iphi := DegreeReduction(G);
  deg := Degree(G);
  fac := Factorisation(#G);
  sylords := Sort([f[1]^f[2] : f in fac]);
  primes := [ f[1][1] : f in [Factorisation(so) : so in sylords] ]; 
  while primes[#primes] in tried do Prune(~primes); end while;
  l := #primes;
  if l le 1 then
    return G, iphi;
  end if;
  act, Q := CosetAction(G,Sylow(G,primes[l]));
  if #Q eq #G then
    QR, phi := DegreeReduction(Q);
  else 
    QR, phi := DegreeReductionH(Q);
  end if;
  phi := act*phi;
  if #QR eq #G then
    if Degree(QR) ge deg then
      QR, phi := DegreeReductionH(G:tried:=tried join {primes[l]});
    end if;
    if Degree(QR) gt maxdeg then
      QR,phir := DegreeReductionH(QR:tried:=tried join {primes[l]});
      phi := phi*phir;
    end if;
    return QR, iphi*phi;
  end if;
  for i in Reverse([1..l-1]) do
    if primes[i] in tried then
      continue;
    end if;
    actn, Qn := CosetAction(G,Sylow(G,primes[i]));
    if #Qn eq #G then
      QRn, phin := DegreeReduction(Qn);
    else 
      QRn, phin := DegreeReductionH(Qn);
    end if;
    phin := actn*phin;
    if #QRn eq #G then
      if Degree(QRn) ge deg then
        QRn, phin := DegreeReductionH(G:tried:=tried join {primes[i]});
      end if;
      if Degree(QRn) gt maxdeg then
        QRn,phir := DegreeReductionH(QRn:tried:=tried join {primes[i]});
        phin := phin*phir;
      end if;
      return QRn, iphi*phin;
    end if;
    if Degree(QR)+Degree(QRn) ge deg then
      continue;
    end if;
    phi, QR := PermutationRepresentationSumH(G,[phi,phin]);
    if #QR eq #G then
      if Degree(QR) ge deg then
        QR, phi := DegreeReductionH(G:tried:=tried join {primes[i]});
      end if;
      if Degree(QR) gt maxdeg then
        QR,phir := DegreeReductionH(QR:tried:=tried join {primes[i]});
        phi := phi*phir;
      end if;
      return QR, iphi*phi;
    end if;
  end for;
  return G, iphi;
end function;
