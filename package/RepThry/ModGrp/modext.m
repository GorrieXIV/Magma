freeze;

import "peakwords.m": ComputeInfo;

HomMod := function(M,N)
// M,N KG-modules. Return Hom(M,N) as KG-module.
  local dm, dn, mgi, ng, V, H, G;
  dm := Dimension(M); dn := Dimension(N);
  mgi := [ g^-1 : g in ActionGenerators(M)];
  ng := ActionGenerators(N);
  V := RSpace(BaseRing(M), dm*dn);
  H := Hom(M,N);
  G := Group(M);
  return GModule(G, [
  Matrix( [ V!Eltseq(Matrix( [ M.k * mgi[i] * H.j * ng[i] : k in [1..dm] ] )) :
              j in [1..dm*dn] ] ) :
           i in [1..#ng] ] );
end function;

ExtM := function(M, N : sglimit := 100000, F := 0 )
// M,N KG-modules. Return Ext(M,N)
  local G, MN, mats, Z1, B1, d,  phi, sg, gpos, rho, m, nr;
  G := Group(M);
  MN := HomMod(M,N);
  d := Dimension(MN);
  if F cmpne 0 then //then assume F := FPGroup(G)
    mats := [ ActionGenerator(MN, i) : i in [1..Nagens(MN)] ];
    F := FPGroup(G);
    Z1 := Nullspace( ComplementEquationsMatrix( GModule(F, mats) ) );
  elif (Type(G) eq GrpPerm or Type(G) eq GrpMat) and #G gt sglimit then
    //need to use strong generators for FPGroup.
    F,phi := FPGroupStrong(G);
    sg := [ phi(F.i) : i in [1..Ngens(F)] ];
    gpos := [ Position(sg, G.i) : i in [1..Ngens(G)] ];
    rho := Representation(MN);
    mats := [ rho(s) : s in sg ];
    Z1 := Nullspace( ComplementEquationsMatrix( GModule(F, mats) ) );
    //only want bit of nullspace corresponding to original generators
    m := Matrix( Basis(Z1) );
    nr := Nrows(m);
    m := HorizontalJoin( [ ExtractBlock(m, 1, (p-1)*d+1, nr, d) : p in gpos] ); 
    Z1 := Image(m);
  else
    mats := [ ActionGenerator(MN, i) : i in [1..Nagens(MN)] ];
    F := FPGroup(G);
    Z1 := Nullspace( ComplementEquationsMatrix( GModule(F, mats) ) );
  end if;
  mats := [ ActionGenerator(MN, i) : i in [1..Nagens(MN)] ];
  B1 := Image( HorizontalJoin([x - 1: x in mats]) );
  return quo< Z1 | B1 >;
end function;

ModuleExtension := function(M, N, e, rho)
//Module extension EM of N by M corresponding to e in E,rho:=ExtM(M,N).
//return also morphisms N->EM and EM->N
  local dm, dn, d, V, mg, ng, G, K, EM, m1, m2, nselt;
  G := Group(M);
  K := BaseRing(M);
  dm := Dimension(M); dn := Dimension(N);
  d := dm*dn;
  mg := ActionGenerators(M);
  ng := ActionGenerators(N);
  nselt := ElementToSequence(e @@ rho);
  V := RSpace(K,d);
  genims := [ V!(nselt[(i-1)*d+1 .. i*d]) : i in [1..#mg] ];
  EM := GModule(G, [
      VerticalJoin( HorizontalJoin( mg[i], mg[i] * Matrix(dm, dn, genims[i]) ),
                    HorizontalJoin( ZeroMatrix(K, dn, dm), ng[i] ) ) :
           i in [1..#mg] ] );
  m1 :=AHom(N,EM)!hom< N->EM | [EM.(dm+i) : i in [1..dn]] >;
  m2 :=AHom(EM,M)!hom< EM->M | [ M.i : i in [1..dm]] cat [M!0 : i in [1..dn]] >;
  return EM, m1, m2;
end function;

HasComp := function(EM, N)
/* N submodule of EM, inj:N->EM. Does N have complement? If so return one
 * But this function exists already!
 */
  local inj, M, p, dn, dm, G, genims, ibm, agm, agem, mat, MN, mats, B1mat,
        sol, comp;
  inj := Morphism(N, EM);
  M, p := quo< EM | inj(N) >;
  dn := Dimension(N);
  dm := Dimension(M);
  G := Group(EM);
  genims := [];
        //will images of G.i in Hom(M,N) to define cocycle corresponding to M
  ibm := Matrix([ M.i @@ p : i in [1..dm]]); //inverse images in ME of basis of M
  for i in [1..Ngens(G)] do
    agm := ActionGenerator(M, i);
    agem := ActionGenerator(EM, i);
    mat := [];
    for j in [1..dm] do
      Append( ~mat, (ibm[j] * agem - agm[j] * ibm) @@ inj );
    end for;
    mat := agm^-1 * Matrix(mat);
    genims cat:= Eltseq(mat);
  end for;
  genims := Vector(genims);
  MN := HomMod(M, N);
  mats := [ ActionGenerator(MN, i) : i in [1..Nagens(MN)] ];
  B1mat :=  HorizontalJoin([x - 1: x in mats]);
  if not genims in Image(B1mat) then
    return false, _;
  end if;
  sol := Matrix(dm, dn, Solution(B1mat,genims) );
  comp := sub< EM | [ EM!ibm[i] - (Vector(M.i) * sol) @ inj : i in [1..dm] ] >;
  return true, comp;
end function;

ModuleExtensionSum := function(M1, M2, M, m1, m2)
/* given two module epimorphisms m1:M1->M ,m2:M2->M defined on M, return the
 * pullback E with morphism E->M1, E->M2
 */
  local D, i1, i2, p1, p2, h, N, inj, r1, r2;
  D, i1, i2, p1, p2 := DirectSum(M1, M2);
  h := AHom(D,M)!hom< D->M | VerticalJoin( Matrix(m1), -Matrix(m2) ) >;
  N := Kernel(h);
  inj := Morphism(N,D);
  r1 := AHom(N,M1)!hom< N->M1 | [ N.i @ inj @ p1 : i in [1..Dimension(N)]] >;
  r2 := AHom(N,M2)!hom< N->M2 | [ N.i @ inj @ p2 : i in [1..Dimension(N)]] >;
  return N, r1, r2;
end function;

ExtendByIrreducible := function(M, N, E, rho)
/* M KG-module, N irreducible KG-module, E,rho = ExtM(M,N).
 * Put as many copies of N as possible under M subject to not splitting
 */
  local dm, K, MM, m, td, ME, m1, m2, newMM, r1, r2, newm;
  dm := Dimension(M);
  K := BaseRing(M);
  MM := M;
  m := AHom(MM,M)!hom< MM->M | IdentityMatrix(K,dm) >;
  td := Dimension(M) - Dimension(JacobsonRadical(M));
  for i in [1..Ngens(E)] do
    ME, m1, m2 := ModuleExtension(M, N, E.i, rho);
    newMM, r1, r2 := ModuleExtensionSum(MM, ME, M, m, m2);
    if Dimension(newMM) - Dimension(JacobsonRadical(newMM)) eq td then
      MM := newMM;
      m := r1 * m;
    end if;
  end for;
  return MM, m;
end function;
  
/* remaining functions are for getting projective indecomposables by
 * repeated downward extensions of modules.
 * But the method of spinning up peakwords in permutation modules is
 * usually superior!
 */

ProjectiveIndecomposableA := function(M : F:=0 )
//M KG-module with unique top factor.
//Compute projective indecomposable mapping onto M
  local dm, G, T, ind, E, N, blocks, rho, I, facs, afacs,
        K, entry,  S, Si, setSi, split, Z,  mQ, MM, mm, r1, r2; 

  dm := Dimension(M);
  T := quo< M | JacobsonRadical(M) >;
  assert IsIrreducible(T);
  G := Group(M);
  K := BaseRing(M);
  ComputeInfo(G, K);
  entry := [ t : t in G`modrepinfo | t`field cmpeq K ][1];
  I := entry`irreds;
  //locate T in list
  for i in [1..#I] do if IsIsomorphic(I[i], T) then
    ind := i; break;
  end if; end for;
  //locate composition factors of M
  facs := [ 0 : i in [1..#I] ];
  for c in CompositionFactors(M) do
    for i in [1..#I] do if IsIsomorphic(I[i], c) then
      facs[i]+:=1; break;
    end if; end for;
  end for;
  afacs := [ entry`cartan[ind][i] : i in [1..#I] ];

  if F cmpne 0 then
    F := FPGroup(G);
  end if;
  while facs ne afacs do
    exts := [**];
    //M is module we are extending downwards on this pass
    //exts is a list of pairs <M1, m1> of extnesions constructed by
    //putting irreducibles under M.
    for i in [1..#I] do if afacs[i] gt facs[i] then
          N := I[i];
"Attempting to extend with",N;
          E, rho := ExtM(M, N : F:=F );
          MM, m := ExtendByIrreducible(M, N, E, rho);
          Append( ~exts, <MM, m> ); 
"Dimension",Dimension(MM);
          facs[i] +:= (Dimension(MM) - Dimension(M)) div Dimension(N);
    end if; end for;
    //add up all the new extensions
    MM := exts[1][1];
    m := exts[1][2];
    for i in [2..#exts] do
        MM, mm := ModuleExtensionSum(MM, exts[i][1], M, m, exts[i][2]);
        m := mm * m;
    end for;
    M := MM;
"Dimension at end of cycle:", Dimension(M);
  end while;
  return M;
end function;

ProjectiveIndecomposablesA := function(G, K)
//Get all projective indecomposable GF(p)G-modules
  ComputeInfo(G, K);
  entry := [ t : t in G`modrepinfo | t`field cmpeq K ][1];
  entry`pdim;
  I := entry`irreds;
  F := FPGroup(G);
  return I, [ ProjectiveIndecomposableA(i : F:=F ) : i in I ];
end function;
