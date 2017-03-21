freeze;

declare verbose PowerProductMod, 1;


intrinsic PreviousPrimeWithSplitting(p::RngIntElt, O::RngOrd, d::RngIntElt) -> RngIntElt, SeqEnum[RngOrdIdl]
{No explanation required}

    f := DefiningPolynomial(NumberField(O));

    repeat
        p := PreviousPrime(p : Proof := false);
        F := Factorization(f, GF(p));
    until forall{t : t in F | t[2] eq 1 and Degree(t[1]) le d};

    return p, [t[1] : t in Factorization(p*O)];

end intrinsic;


intrinsic ModulusWithSplitting(n::RngIntElt, O::RngOrd, d::RngIntElt) -> RngIntElt, SeqEnum[RngOrdIdl]
{No explanation required}

    m := 1;
    P := [];
    p := Ceiling(2^26.5);
    while m lt n do
        p, Pp := PreviousPrimeWithSplitting(p, O, d);
        m := m * p;
        P := P cat Pp;
    end while;
  
    return m, P;

end intrinsic;


intrinsic PowerProductMod(B::SeqEnum[RngElt], E::SeqEnum[RngIntElt], m::RngIntElt
                          : Primes:=[], Residues:=[**])
       -> RngElt
{Power product modulo m using finite fields}
    
    O := MaximalOrder(Universe(B));
    D := Discriminant(O);

    require m gt 1 : "Modulus must be greater than 1";

    require GCD(D, m) eq 1 : "Modulus must be coprime to discriminant";

    require IsSquarefree(m) : "Modulus must be squarefree";

    primes := PrimeDivisors(m);

    if not IsEmpty(Primes) then

        require Norm(O!m) eq &* [Norm(p) : p in Primes] :
                "Invalid optional argument 'Primes'";

        P := Primes;
        R := [* r where _, r := ResidueClassField(p) : p in Primes *];

    else

        P := [];
        R := [* *];
vprintf PowerProductMod: "Residue fields : ";
vtime PowerProductMod:
        for p in primes, t in Factorization(p*O) do
            _, r := ResidueClassField(t[1]);
            Append(~R, r);
            Append(~P, t[1]);
            assert t[2] eq 1;
        end for;

    end if;

    if not IsEmpty(Residues) then

        require Type(Residues) eq List and #Residues eq #P
                and forall{X : X in Residues | #X eq #B} :
                "Invalid optional argument 'Residues'";

        BR := Residues;

    else

vprintf PowerProductMod: "Residues : ";
vtime PowerProductMod:
        BR := [* [b@r : b in B] : r in R *];

    end if;

    require forall{x : x in X, X in BR | not IsZero(x)} :
            "Elements must be coprime to the modulus";

    PPR := [];
vprintf PowerProductMod: "Power products : ";
vtime PowerProductMod:
    for i := 1 to #R do
        // reduce E modulo order of multiplicative group
        // TO DO: least residues?
        o := #Codomain(R[i]) - 1;
        mo2 := - (o div 2);
        Ei := [e lt 0 and e gt mo2 select e else e mod o : e in E];
        PPi := PowerProduct(BR[i], Ei);
        Append(~PPR, PPi @@ R[i]);
    end for;
//"PPR:"; PPR;

    CRTs := [];
vprintf PowerProductMod: "CRT over O : ";
vtime PowerProductMod:
    for p in primes do
        inds := [i : i in [1..#P] | Minimum(P[i]) eq p];
        Append(~CRTs, CRTZ(PPR[inds], P[inds] : LCM:=p*O));
    end for;

    Z := Integers();
    C := [Eltseq(O!x) : x in CRTs];
    e := [];
vprintf PowerProductMod: "CRT over Z : ";
vtime PowerProductMod:
    for j := 1 to Degree(O) do
        e[j] := CRT([Z| C[i,j] : i in [1..#primes]], primes);
assert e[j] eq e[j] mod m;
    end for;

    return (O!e) mod (m*O);

end intrinsic;


/*


SetVerbose("ClassGroup", 2);

SetClassGroupBounds("GRH");

x := PolynomialRing(Rationals()).1;
F := NumberField(x^16 - 7);
ZF := Integers(F);

time
U, mU, bU := SUnitGroup(1*ZF : Raw);
B := Eltseq(bU);

s := Ceiling(Degree(F)/4));
s := 1;
m, P := ModulusWithSplitting(10^100, ZF, s);

R := [* r where _, r := ResidueClassField(p) : p in P *];
BR := [* [b@r : b in B] : r in R *];

for i := 1 to 2 do // Ngens(U) do

    E := Eltseq(U.i @ mU);
    printf "#%o : max exp %o digits\n", i, Ilog(10, Max([Abs(e) : e in E]));
    time 
    PPm := PowerProductMod(B, E, m : Primes:=P, Residues:=BR);
    assert IsUnit(PPm);
    if 1 eq 1 then
       time 
       PP := ZF! PowerProduct(B, E);
       assert IsUnit(PP);
       assert PPm eq PP mod (m*ZF);
    end if;

end for;


*/

