freeze;
 
ModuleExtensions := function(M1,M2:all:=true)
/* M1 and M2 should be modules over the same finite (permutation or matrix)
 * group G over a finite field K.
 * The dimensions of Ext_KG(M1,M2) (the space of extensions of M1 by M2)
 * is returned, together with a list of all such extensions.
 * If the optional parameter all is false, then a (possibly smaller) list
 * of nonisomorphic modules of this form is returned.
 */
  local G, D, T, TT, F, phi, rep, E, N, NC, X, fgno, havemod,
        d1, d2, nag, vec, vecmat, mats, mat, ib, M, mods;


  G:=Group(M1);
  if G ne Group(M2) then
    error "Modules are not defined over the same group!";
  end if;
  d1 := Dimension(M1);
  d2 := Dimension(M2);
  nag := Nagens(M1);
  
  D:=Dual(M2);
  T:=TensorProduct(D,M1);
  F,phi:=FPGroup(G);
  rep := Representation(T);
  // We need to define the equivalent module over F */
  TT:=GModule(F,[ F.i @ phi @ rep : i in [1..Ngens(F)]]);
  E:=ComplementEquationsMatrix(TT);
  N:=NullSpace(E);
  NC:=ConjugateComplementSubspace(TT);
  EX := Complement(N,NC);
  mods := [];
  for v in EX do
    vec := ElementToSequence(v); 
    vecmat := Matrix(d1,vec);
    mats := [];
    for gno in [1..nag] do
      mat := DiagonalJoin(ActionGenerator(M2,gno),ActionGenerator(M1,gno));
      if G.nag ne Id(G) then
      //Unfortunately the generators of F might not correspond nicely to
      //those of G.
        fgno := Representative({i : i in [1..Ngens(F)] | phi(F.i) eq G.gno });
        ib := ActionGenerator(M2,gno) *
                                   ExtractBlock(vecmat,(fgno-1)*d2+1,1,d2,d1);
        InsertBlock(~mat,ib,1,d2+1);
        Append(~mats,mat);
      end if;
    end for;
    M := GModule(G,mats);
    if all then
      Append(~mods,M);
    else
      havemod := false;
      for m in mods do
        if IsIsomorphic(M,m) then
           havemod := true;
           break;
        end if;
      end for;
      if not havemod then
        Append(~mods,M);
      end if;
    end if;
  end for;

  return Dimension(EX), mods;
  
end function;

AllModules := function (irreds,n)
/* irreds should be a complete list of nonisomorphic irreducible modules
 * of a finite group G over a finite field K up to dimension n.
 * A complete list of all nonisomorphic modules up to dimension n
 * for G is returned.
 */
  local mods, ext, havemods, newmods;
  mods := [m: m in irreds | Dimension(m) eq 1];
  for deg in [2..n] do
    // Append modules of dimension deg to mods
    newmods := []; //new non-irreducibles
    for m in mods do
      if Dimension(m) lt deg then
        for im in irreds do
          if Dimension(im) + Dimension(m) eq deg then
            // adjoin extensions of m by im
            _,ext := ModuleExtensions(m,im:all:=false);
              for e in ext do
                  havemod := false;
                  for om in newmods do
                    if IsIsomorphic(e,om) then
                       havemod := true;
                       break;
                    end if;
                  end for;
                  if not havemod then
                    Append(~newmods,e);
                  end if;
              end for;                
          end if;
        end for;
      end if;
    end for;
    
    mods := mods cat [m: m in irreds | Dimension(m) eq deg] cat newmods;
  end for;

  return mods;
end function;

RepresentativeModules := function (G,N,K,n)
/* A list  of representatives of the distinct GK-modules of dimension n
 * under the action of H <= Aut(G) is computed, where H is the subgroup
 * of Aut(G) that fixes the normal subgroup N of G.
 */
  local irreds, mods, nm, A, a, perms, perm, P, m, rm, immats, imm, got, reps,
        innerno, autno, Norb, Nstab, Nreps, orbno, Ni, Nia, p, sa, Gab, phi;
  if not IsNormal(G,N) then
     error "N should be a normal subgroup of G";
  end if;
  if n eq 1 then
    //All modules are defined for G/G'.
    Gab, phi := quo<G | DerivedGroup(G)>;
    irreds := IrreducibleModules(Gab,K);
    irreds := [ GModule(G,[MatrixAlgebra(K, 1) |
                 ActionGenerator(im,i) : i in [1..Ngens(G)]]) :
                                    im in irreds | Dimension(im) eq 1];
    vprint GrpExt,1: #irreds,"irreducible modules of dimension 1";
  else
    irreds := IrreducibleModules(G,K);
    vprint GrpExt,1: #irreds,"irreducible modules";
  end if;
  mods := [ m : m in AllModules(irreds,n) | Dimension(m) eq n];
  nmods := #mods;
  vprint GrpExt,1: nmods, "modules of dimension", n;
  A := AutomorphismGroup(G);
  innerno := #A`InnerGenerators;
  autno := Ngens(A);
  /* Perform an orbit-stabiliser calculation for the action of the outer
   * automorphisms in A on N.
   */
  Norb := [N];
  Nreps := [Id(A)];
  Nstab := [];
  orbno:=1;
  while orbno le #Norb do
    Ni := Norb[orbno];
    for i in [innerno+1..autno] do
      a := A.i;
      Nia := Ni@a;
      p := Position(Norb,Nia);
      if p eq 0 then
        Append(~Norb,Nia);
        Append(~Nreps,Nreps[orbno]*a);
      else
        sa := Nreps[orbno]*a*Nreps[p]^-1;
        if not IsInner(sa) then
          Append(~Nstab,Nreps[orbno]*a*Nreps[p]^-1);
        end if;
      end if;
    end for;
    orbno +:=1;
  end while;
  /* Calculate permutation action of A on mods */
  perms := [];
  for ns in Nstab do
    a := ns^-1;
    perm := [];
    for j in [1..nmods] do
      m := mods[j];
      r := Representation(m);
      immats := [r(a(G.k)) : k in [1..Ngens(G)] ]; 
      imm := GModule(G,immats);
      got := false;
      for k in [1..nmods] do
        if IsIsomorphic(mods[k],imm) then
          perm[j] := k;
          got := true;
          break;
        end if;
      end for;
      if not got then
         error "Could not find image of module under group automorphism";
      end if;
    end for;
    Append(~perms,perm);
  end for; 
  P := sub<Sym(nmods) | perms >;
  reps := {Representative(o) : o in Orbits(P)};
  vprint GrpExt,1:
        #reps, "modules of dimension", n, "under automorphism action";
  return [ mods[rep] : rep in reps ];
end function;

SplitExtension := function(G,M)
/* G should  be a permutation group and M a G-module ove ra finite field.
 * The split extension of M by G is returned as a permutation group of
 * degree |M| + Degree(G).
 */
  local Melts, Mgens, d, perms, perm, g;
  Melts := [ m : m in M ];
  /* First the generators of M - let's try to find a minimal such set  */
  Mgens := [];
  for i in [1..Ngens(M)] do
    if not M.i in sub< M | Mgens > then
       Append(~Mgens,M.i);
    end if;
  end for;
  d := Degree(G);
  perms := [];
  for m in  Mgens do
    perm := [];
    for i in [1..#M] do
      perm[i] := Position(Melts,Melts[i]+m);
    end for;
    for i in [#M+1..#M+d] do
      perm[i] := i;
    end for;
    Append(~perms,perm);
  end for;
  /* Next the generators of G */
  for j in [1..Ngens(G)] do
    g := G.j;
    perm := [];
    for i in [1..#M] do
      perm[i] := Position(Melts,Melts[i]*ActionGenerator(M,j));
    end for;
    for i in [#M+1..#M+d] do
      perm[i] := (i-#M)^g + #M;
    end for;
    Append(~perms,perm);
  end for;

  return sub< Sym(#M+d) | perms >;
end function;
