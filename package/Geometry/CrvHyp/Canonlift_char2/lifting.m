freeze;

/******************************************************************

  Functions for computing the theta constants (referred to as taus)
  to a desired p-adic precision for the canonical lift of an
  ordinary hyperelliptic curve in characteristic 2.
  
  The basic method is Lercier/Lubicz's Newton lifting technique
  via Artin-Schreier solutions. This has been locally adapted by
  Mike Harrison to use a precision-truncated Artin_Schreier soln.
  to give smallish fixed precision increments in a similar way to
  the SST method for elliptic curves.
         Mike Harrison 01/2004
  
******************************************************************/

import "matrixblah.m": IminAinvB, IminAinv;

LOWER_LIMS      := [2006,9939,15140,30000];
LOWER_LIMS_GNB1 := [306,2239,10099,20000];
LOWER_LIMS_GNB2 := [2006,9939,15140,30000];

/* TODO: the values in LOWER_LIMS_GNB2 and the final values in all the
         above arrays should be reviewed.                           */

LiftDataStr := recformat<
    g     : RngIntElt,   // the genus (>= 2)
    n     : RngIntElt,   // the degree of the base field (over GF(2))
    gadj  : RngIntElt,   // max integral adjust for matrix calcs
    Rmax  : RngPadResExt,// max precision unramified quotient ring.
    booGNB: BoolElt,     // using ring with a GNB?
    
    stages: SeqEnum,     // sequences of ints representing the
    ws    : SeqEnum,     // SST stages - stages[i] SST iterations
                         // will be performed with increment ws[i]
    precAdjs: SeqEnum,   // boolean sequence of precision adjusts
                         // for Newton lift phase

    M     : AlgMatElt,   // -2^(g-2) * (Delta_y^(-1)*Delta_x)
    phis  : ModMatRngElt,// - Delta_y^(-1)*phis(x)/2^prec

    
    // Precomputes for SST lift
    w     : RngIntElt,   // current SST precisional increment    
    Apre1 : SeqEnum,     // matrix power precomputes
    Apre2 : SeqEnum,     // matrix power precomputes
    Aseq  : SeqEnum,     // matrix power precomputes
    MatInv: AlgMatElt,   // (I-Afin)^-1 if required
    expseq: SeqEnum,     // exponent sequence
    n_last: RngIntElt    //
>;

function PosSqrt(a)

    b := SquareRoot(a);
    if Valuation(b-1) eq 1 then
        b := -b;
    end if;
    return b;
    
end function;

procedure SSTClean(~LD)

    delete LD`Apre1,LD`Apre2,LD`Aseq,LD`expseq;
    if assigned LD`MatInv then delete LD`MatInv; end if;
    
end procedure;

function gAdjust(g)

    if g eq 2 then return 0; end if;
    max := 0;
    for k in [2..2*g-1] do
        r := #Intseq(k,2);
        if k eq 2^(r-1) then r -:=1; end if;
        max := Max(r*(g-2)+r+1-k,max);
    end for;
    return max;

end function;

function Wgt(n)

    return #bits + #[1:i in bits | i eq 1] - 2 where bits is
                        Intseq(n,2);

end function;

function Initialise(precfin,g,n)

    LD := rec<LiftDataStr| g:= g, n:= n, gadj:= gAdjust(g)>;
    t := g-2;

    // Get the "best" stage decomposition

    // look for Gaussian Normal Basis
    gnb_type := 1;
    R := pAdicQuotientRing(2,1);
    while gnb_type le 2 do //possible GNB types
       if (gnb_type eq 2) and
         (n lt ((g eq 2) select 130 else 55)) then break; end if;
       booGNB := HasGNB(R,n,gnb_type);
       if booGNB then break; end if;
       gnb_type +:= 1;
    end while;       
    
    // First decide on Newton stages     
    LD`precAdjs := [Booleans()|];
    prec := precfin;
    if booGNB then 
       if gnb_type eq 1 then 
          lower_lim := LOWER_LIMS_GNB1[Min(g-1,4)];
       else
          lower_lim := LOWER_LIMS_GNB2[Min(g-1,4)];
       end if;
    else
       lower_lim := LOWER_LIMS[Min(g-1,4)];
    end if;
    while prec gt lower_lim do
        Append(~LD`precAdjs,IsOdd(prec+g+1));
        prec := Ceiling((prec+g+1)/2);
    end while;
    Reverse(~LD`precAdjs);

    // now add SST stages  
    bestval := 10^50;
    paras := [];

    wadj := Max(3,2*t+g+LD`gadj);
    r2s := [];
    for w2 in [25-2*t..30-2*t] do
      r2 := (prec div w2)-1;
      if r2 gt 0 then
        p1 := prec-r2*w2;
        while p1 lt w2+wadj do 
          p1 +:= w2;
          r2 -:=1;
        end while;
      else
        r2 := 0;
      end if;
      Append(~r2s,r2);
    end for;
    w2vals := [r2s[i]*(20+Wgt(25+i)) : i in [1..6]];
    goodw2 := [i : i in [1..6] | w2vals[i] eq min] where min is Min(w2vals);
    for i in goodw2 do
      w2 := 24-2*t+i; r2 := r2s[i];
      p1 := prec-r2*w2;
      if p1 lt 10+wadj then
        r1 := 0; w1 := 2;
        val := 2*((g-1)^2)*p1;
        if val lt bestval then
            bestval := val;
	    prec0 := p1;
            LD`stages := [r2]; LD`ws := [w2];
        end if;
      else
        for d in [wadj..wadj+3] do
            pre1 := p1-d;
            divs := [a : a in Divisors(Factorization(pre1)) | (a ne 1) and
                                                  (a ne pre1)];
            for w1 in divs do
                r1 := (pre1 div w1)-1;
                val := 2*((g-1)^2)*(w1+d)+r1*(Wgt(w1+2*t+1)+5);
                if val lt bestval then
                    bestval := val;
                    prec0 := w1+d;
                    if r2 eq 0 then
                        LD`stages := [r1]; LD`ws := [w1];
                    else
                        LD`stages := [r1,r2]; LD`ws := [w1,w2];
                    end if;
                end if;
            end for;
        end for;
      end if;
    end for;
    
    precmax := Max(prec0*(g-1)-g+7,prec+3*(g-1));
    if #(LD`ws) gt 0 then
        precmax := Max(precmax,mx+LD`gadj+3*g-4) where mx is Max(LD`ws);
    end if;
    if #(LD`precAdjs) gt 0 then
        precmax := Max(precmax,2*Ceiling((precfin+g+1)/2)+2*g+LD`gadj-2);
    end if;

    LD`booGNB := booGNB;
    if booGNB then
       LD`Rmax := 
        UnramifiedExtension(pAdicQuotientRing(2,precmax),n: GNBType := gnb_type);
    else
       LD`Rmax := 
        UnramifiedExtension(pAdicQuotientRing(2,precmax),n: Cyclotomic := true);
    end if;
    return LD,prec0;

end function;

function LastBits(bits,r)

    p := #bits;
    nmax := 0;
    while p gt 0 do
       n := 0;
       while n lt r do
           if p eq 0 then break; end if;
           n := 2*n + bits[p];
           p -:= 1;
       end while;
       nmax := Max(nmax,n);
    end while;
    return n,nmax;

end function;

function NextBits(bits,pos,r)

    p := pos;
    n := 0;
    while n lt r do
       if p eq 0 then break; end if;
       n *:= 2;
       n +:= bits[p];
       p -:= 1;
    end while;
    return pos-p,n;

end function;

function gettaus(roots,diffs,g)

  R := Parent(roots[1]);
  taus := [R|];
  for i in [1..(2^g)-1] do
    prod := R!1;
    seq := Intseq(i,2);
    seq := [0] cat seq cat [0 : i in [1..g-#seq]];
    for m in [2..g+1], n in [1..m-1] do
      if seq[n]+seq[m] eq 1 then
        elt := roots[n]-roots[m];
        prod := (prod*(elt+diffs[n])*(elt-diffs[m])) div
                    (elt*(elt+diffs[n]-diffs[m]));
      end if;
    end for;
    Append(~taus,prod);
  end for;
  return [PosSqrt(PosSqrt(x)) : x in taus];

end function;

function badd(i,j)

    if j eq 0 then return i; end if;
    s1 := Intseq(i,2); s2 := Intseq(j,2);
    if #s1 lt #s2 then
        s := s1; s1 := s2; s2 := s;
    end if;
    d := #s1-#s2;
    for i in [1..#s2] do
        if s2[i] eq 1 then
         s1[i] := 1-s1[i];
        end if;
    end for;
    return Seqint(s1,2);

end function;

function Iterate(taus,g)

  R := Parent(taus[1]);
  tau1 := [R|];
  t :=  [R!1] cat taus;
  s := &+[ a^2 : a in t];
  assert Valuation(s) eq g;
  G := 2^g;
  for j in [1..G-1] do
    Append(~tau1, (&+[t[i]*t[badd(j,i-1)+1] : i in [1..G]]) div s);
  end for;
  return [PosSqrt(x) : x in tau1];

end function;

function IReps(i,N)

    m := 2^Valuation(i,2);
    return [j : j in [1..N] | (j mod (2*m)) lt m];

end function;

procedure TauCalcs(~LD,taus,prec,bSST)

    g := LD`g; gadj := LD`gadj;
    bPreComp := bSST and not assigned LD`expseq;
    N := #taus;
    w := bSST select LD`w else prec-g-1;

    if bPreComp then
        R1 := ChangePrecision(LD`Rmax,w+3*g+gadj-4);   
    else    
        R1 := ChangePrecision(LD`Rmax,prec+w+3*(g-1));
    end if;

    // Change precision for phi(taus,staus) calculation
    tbig := ChangeUniverse(taus,R1);
    staus := [GaloisImage(x,1) : x in tbig];    
    E := (R1!1) div ((&+[x^2 : x in tbig] + R1!1) div 2^g);
    stinv := [(R1!1) div x : x in staus];

    if bPreComp then
        if g gt 2 then
	    ChangePrecision(~R1,Precision(R1)+2-g);
        end if;   
    else    
        // Revert back to lower precision
        ChangePrecision(~R1,w+2*(g-2)+(bSST select 0 else (gadj+2)));

        LD`phis := Matrix(N,1, [R1| -( staus[i] -
          (((tbig[i] + &+[tbig[j]*tbig[badd(j,i)] : j in IReps(i,N)])
	    *stinv[i]) div 2^(g-1))*E ) div 2^(prec+1)
		    : i in [1..N]]);
        if bSST then return; end if;
    end if;
    
    E := -(R1!E);
    ChangeUniverse(~stinv,R1);
    ChangeUniverse(~staus,R1);
    ChangeUniverse(~tbig,R1);
    
    LD`M := Matrix(N,N,
            [ ((tbig[i]*staus[j] - stinv[j]*
              ((i eq j) select R1!1  else tbig[badd(i,j)])) div 4) * E
                         : i in [1..N], j in [1..N]    ]);
    
end procedure;

function MatFrob(M,t)

    return Matrix(NumberOfRows(M),NumberOfColumns(M),
                   [GaloisImage(a,t) : a in Eltseq(M)]);

end function;

// precomputes for fixed precision increment stages.
procedure SSTPrecomp(~LD)

    g := LD`g;
    n := LD`n;
    R := Parent((LD`M)[1,1]);
    N := LD`w+2*g-3;
    d := NumberOfRows(LD`M);

    bits := Intseq((N le n) select N else n,2);
    if g eq 2 then 
        n_last := 0; n_max := 1;
    else
        n_last,n_max := LastBits(bits,g-1);
        if n_last ge g-1 then n_last := 0; end if;
    end if;
    LD`n_last := n_last;
    A_last := 0;
    R1 := ChangePrecision(R,N-g+1);
    R2 := ChangePrecision(R,N-1);
    bUgly := ((N le n) or (n_last eq 0));
    if bUgly then
        R := R1;
    else
        R := ChangePrecision(R,N-n_last);
    end if;

    // make precomputes (if g > 2)
    //vprintf JacHypCnt,4 : "Making precomputes... ";
    //tyme := Cputime();
    Atmp := [];
    Apre := [];
    if g eq 2 then
        Append(~Apre,Matrix(R,LD`M));
    else
        Append(~Atmp,LD`M);
        if n_last eq 1 then
            if N gt n then A_last := Matrix(R,LD`M); end if;
        end if;
        for i in [2..n_max] do
            A := MatFrob(Atmp[Ceiling(i/2)],i div 2) * Atmp[i div 2];
            assert Min([Valuation(elt) : elt in Eltseq(A)]) ge g-1;
            if i ge g-1 then
	       A := Matrix(d,d,[elt div 2^(2*(g-1)-i) : elt in Eltseq(A)]);
               if i eq g-1 then Append(~Atmp,A); end if;
               Append(~Apre,Matrix(R,A));
            else
               Append(~Atmp,Matrix(d,d,[elt div 2^(g-1) :
                                elt in Eltseq(A)]));
               if n_last eq i then 
                   if N gt n then A_last := Matrix(R,Atmp[#Atmp]); end if;
               end if;
            end if;
            delete A;
        end for;
    end if;
    LD`Apre1 := [MatFrob(Matrix(R2,A),1) : A in Atmp];
    delete LD`M,Atmp;

    pos := #bits;
    ndble,expo := NextBits(bits,pos,g-1);
    A := Apre[expo-g+2];
    nseq := [expo];    
    Aseq := [];
    pos -:= ndble;
    while pos gt 0 do
       ndble,i := NextBits(bits,pos,g-1);
       pos -:= ndble;
       for j in [1..ndble] do
           Append(~nseq,0);
           A1 := MatFrob(A,expo);
           Append(~Aseq,Matrix(R1,A1));
           A := A1*A;
           expo *:= 2;
       end for;
       if i gt 0 then
           Append(~nseq,i);
           A1 := MatFrob(A,i);
           Append(~Aseq,Matrix(R1,A1));
           expo +:= i;
           if pos gt 0 then
               A := A1*Apre[i-g+2];
           else 
               if N gt n then
                  if i ge g-1 then
                    A := A1*Apre[i-g+2];
                  else
                    A := Matrix(R,d,d,[elt div 2^(g-1-i) :
                                elt in Eltseq(A1*A_last)]);
                  end if;
               end if;
           end if;
       end if;
    end while;
    LD`Apre2 := [MatFrob(Matrix(R1,a),1) : a in Apre];
    delete Apre;
    LD`Aseq := Aseq;
    LD`expseq := nseq;
    val := Min([Valuation(m):m in Eltseq(A)]);
    if (N gt n) and (val lt N-g+1) then
        LD`MatInv := IminAinv(Matrix(R1,A),N-g+1,val,LD`Rmax);
    end if;
    //vprintf JacHypCnt,4 :  "Time: %o\n",Cputime(tyme);

end procedure;

// does a fixed precision increment step.
function SSTArtinSchr(LD)

    b_last := 0;
    g := LD`g;
    d := NumberOfRows(LD`phis);
    R := Parent((LD`phis)[1,1]);
    if g gt 2 then
        R := ChangePrecision(R,LD`w+g-2);
    end if;
    nseq := LD`expseq;
    Aseq := LD`Aseq;
    
    //make b precomputes and get first b
    b := Matrix(R,LD`phis);
    if g eq 2 then
        bpres := [b];
        expo := 1;
    else
        b1 := b;
        bpres := [];
        if LD`n_last eq 1 then b_last := b; end if;
        for i in [2..#(LD`Apre2)+g-2] do
            b := MatFrob(b,1)+v where v is (i lt g) select
              Matrix(R,d,1,[elt div 2^(g-i) : 
                         elt in Eltseq((LD`Apre1)[i-1]*LD`phis)])
              else (LD`Apre2)[i-g+1]*b1;
            if i ge g-1 then
                Append(~bpres,b);
            else if i eq LD`n_last then
                b_last := b;
            end if; end if;
        end for;
        expo := nseq[1];
        b := bpres[expo-g+2];
        delete b1;
    end if;
    delete LD`phis;

    for i in [1..#nseq-1] do
        op := nseq[i+1];
        if op eq 0 then
            b := MatFrob(b,expo)+Aseq[i]*b;
            expo *:= 2;
        else
            b := MatFrob(b,op)+Aseq[i]*
                 ((op eq LD`n_last) select b_last else bpres[op-g+2]);
            expo +:= op;
        end if;
    end for;
    if expo lt LD`n then
      b := MatFrob(b,LD`n-expo);
    end if;
    if assigned LD`MatInv then
       b := (LD`MatInv)*b;
    end if;
    return Eltseq(b);

end function;    

// does a full Lercier/Lubicz Newton lift step.
function ArtinSchrSol(LD)

    g := LD`g;
    n := LD`n;
    gadj := LD`gadj;
    R := Parent((LD`M)[1,1]);
    N := Precision(R)-gadj;
    d := NumberOfRows(LD`phis);

    bits := Intseq((N le n) select N-1 else n,2);
    if g eq 2 then 
        n_last := 0; n_max := 1;
    else
        n_last,n_max := LastBits(bits,g-1);
    end if;
    b_last := 0;
    A_last := 0;
    R := ChangePrecision(R,N-(((N le n) or (n_last eq 0) or (n_last ge g))
                                   select g else (n_last+1)));

    // make precomputes (if g > 2)
    tyme := Cputime();
    vprintf JacHypCnt,4 : "Making precomputes... ";
    Atmp := [];
    Apre := [];
    bpre := [];
    b := Matrix(R,LD`phis);
    b1 := b;
    if g eq 2 then
        Append(~Apre,Matrix(R,LD`M));
        Append(~bpre,b);
    else
        Append(~Atmp,LD`M);
        if n_last eq 1 then
            b_last := b;
            if N gt n then A_last := Matrix(R,LD`M); end if;
        end if;
        for i in [2..n_max] do
            b := MatFrob(b,1)+v where v is (i lt g) select
              Matrix(R,d,1,[elt div 2^(g-i) : 
                         elt in Eltseq(MatFrob(Atmp[i-1],1)*LD`phis)])
              else MatFrob(Apre[i-g+1],1)*b1;
            A := MatFrob(Atmp[Ceiling(i/2)],i div 2) * Atmp[i div 2];
            assert Min([Valuation(elt) : elt in Eltseq(A)]) ge g-1;
            if i ge g-1 then
	       A := Matrix(d,d,[elt div 2^(2*(g-1)-i) : elt in Eltseq(A)]);
               if i eq g-1 then Append(~Atmp,A); end if;
               Append(~Apre,Matrix(R,A));
               Append(~bpre,b);
            else
               Append(~Atmp,Matrix(d,d,[elt div 2^(g-1) :
                                elt in Eltseq(A)]));
               if n_last eq i then 
                   b_last := b;
                   if N gt n then A_last := Matrix(R,Atmp[#Atmp]); end if;
               end if;
            end if;
            delete A;
        end for;
    end if;
    delete b1,Atmp,LD`M,LD`phis;
    vprintf JacHypCnt,4 : "Time: %o\n",Cputime(tyme);

    tyme := Cputime();
    vprintf JacHypCnt,4 : "Computing solution...  ";
    pos := #bits;
    ndble,expo := NextBits(bits,pos,g-1);
    A := Apre[expo-g+2]; b := bpre[expo-g+2];
    pos -:= ndble;
    while pos gt 0 do
       ndble,i := NextBits(bits,pos,g-1);
       pos -:= ndble;
       for j in [1..ndble] do
           A1 := MatFrob(A,expo);
           b := MatFrob(b,expo)+A1*b;
           A := A1*A;
           expo *:= 2;
       end for;
       if i gt 0 then
           expo +:= i;
           A1 := MatFrob(A,i);
           b := MatFrob(b,i)+A1*((i ge g-1) select bpre[i-g+2]
                                      else b_last);
           if pos gt 0 then
               A := A1*Apre[i-g+2];
           else 
               if N gt n then
                  if i ge g-1 then
                    A := A1*Apre[i-g+2];
                  else
                    A := Matrix(R,d,d,[elt div 2^(g-1-i) :
                                elt in Eltseq(A1*A_last)]);
                  end if;
               end if;
           end if;
       end if;
    end while;

    vprintf JacHypCnt,4 : "Time: %o\n",Cputime(tyme);
    if N gt n then
        return A,b;
    else
        return ScalarMatrix(d,R!0),MatFrob(b,n-N+1);
    end if;

end function;     

function LiftMain(roots,diffpol,fld,precfin)

    n := Degree(fld);
    g := #roots - 1;

    LD,prec := Initialise(precfin,g,n);
    Embed(fld,ResidueClassField(LD`Rmax));
    n0 := prec*(g-1)-g+7;
    R := ChangePrecision(LD`Rmax,n0);
    rts := ChangeUniverse(roots,R);
    PolR := PolynomialRing(R); x := PolR.1;
    pol := &*[ x-r : r in rts] + 4*PolR!diffpol;
    diffs := [HenselLift(pol,r)-r : r in rts];
    delete pol,PolR;

    vprintf JacHypCnt,3 :
             "Iterating to base precision (%o)..  ",prec;
    tyme := Cputime();
    taus := gettaus(rts,diffs,g);
    ChangePrecision(~R,Precision(R)-2);
    ChangeUniverse(~taus,R);
    for i in [3..prec] do
        taus := Iterate(taus,g);
        if g gt 2 then
           ChangePrecision(~R,Precision(R)-g+2);
           ChangeUniverse(~taus,R);
        end if;
    end for;
    vprintf JacHypCnt,3 : "Time: %o\n",Cputime(tyme);
    // make sure elements are "reduced"
    taus := [elt*1 : elt in taus];

    SSTct := 1;
    phasetime := Cputime();
    if #(LD`stages) gt 0 then // do SST precomputes
        nSST := LD`stages[1]; LD`w := (LD`ws)[1];
        vprintf JacHypCnt, 3 : 
    "Using fixed-precision Artin-Schreier for %o precision increments of %o\n",
                nSST, LD`w;
        tyme := Cputime();
        TauCalcs(~LD,taus,prec,true);
        SSTPrecomp(~LD);
        vprintf JacHypCnt, 4 : "Precompute time: %o\n",Cputime(tyme);
        bSST := true;
    else
        vprint JacHypCnt, 3 : "Using full (Artin-Schreier) Newton lifting";
        bSST := false;
    end if;
    lpcnt := 0;
    while prec lt precfin do
        lpcnt +:=1;
        tyme := Cputime();
        TauCalcs(~LD,taus,prec,bSST);
        if bSST then
            b := SSTArtinSchr(LD);
            R := ChangePrecision(LD`Rmax,prec+LD`w+g-2);
            if lpcnt eq nSST then
                lpcnt := 0;
                SSTClean(~LD);
            end if;
        else;
            A,b := ArtinSchrSol(LD);
            b := IminAinvB(A,prec-3,b,LD`Rmax);
            R := ChangePrecision(LD`Rmax,2*prec-3);
        end if;
        taus := [ (R!taus[i] + (2^prec)*R!(b[i]*1))*1 : i in [1..#taus]];
        if bSST then
            prec +:= LD`w;
        else
            prec *:= 2;
            prec -:= g+1+((LD`precAdjs)[lpcnt] select 1 else 0);
        end if;
        vprintf JacHypCnt, 4 : "New precision: %o   Increment time: %o\n",
                      prec, Cputime(tyme);
        if lpcnt eq 0 then
            vprintf JacHypCnt, 3 : "Total phase time: %o\n",Cputime(phasetime);
            phasetime := Cputime();
            SSTct +:= 1;
            if SSTct gt #(LD`ws) then
                if prec lt precfin then
                    vprint JacHypCnt, 3 :
                        "Using full (Artin-Schreier) Newton lifting";
                end if;
                bSST := false;
            else
                nSST := LD`stages[SSTct]; LD`w := (LD`ws)[SSTct];
                vprintf JacHypCnt, 3 : 
    "Using fixed-precision Artin-Schreier for %o precision increments of %o\n",
                           nSST, LD`w;
                tyme := Cputime();
                TauCalcs(~LD,taus,prec,true);
                SSTPrecomp(~LD);
                vprintf JacHypCnt, 4 : "Precompute time: %o\n",Cputime(tyme);
            end if;		
        end if;
    end while;
    if lpcnt gt 0 then
       vprintf JacHypCnt, 3 : "Total phase time: %o\n",Cputime(phasetime);
    end if;
    return taus, LD`booGNB;
    
end function;
