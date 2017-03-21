freeze;
/******************************************************************************
 *
 * cosets.m
 *
 * date:   22/9/2003
 * author: Nils Bruin
 *
 * Routines to compute with cosets in finitely generated abelian groups.
 *
 * Interface:
 *
 * ShortLift - return a "short" representative of a coset (takes a map
 *             G -> G/K)
 * CosetIntersection - Intersect cosets.
 *
 ******************************************************************************/

intrinsic ShortLift(pi::Map,a::GrpAbElt)->GrpAbElt
  {For internal use only}
  G:=Domain(pi);
  Q:=Codomain(pi);
  require ISA(Type(G),GrpAb) and ISA(Type(Q),GrpAb):
    "Map must be a homomorphism between abelian groups";
  require a in Image(pi): "Element must have a preimage under map";
  L:=[Eltseq(LHS(g)-RHS(g)) cat [0]: g in Relations(G)];
  L cat:=[Eltseq(G!a) cat [0]:a in OrderedGenerators(Kernel(pi))];
  L cat:=[Eltseq(a@@pi) cat [IsFinite(Q) select (#Q)^2 else 1000000]];
  M:=RowSequence(LLL(Matrix(L)));
  v:=M[#M];
  g:=G!(v[1..#v-1]);
  if v[#v] lt 0 then
    g:=-g;
  end if;
  assert pi(g) eq a;
  return g;
end intrinsic;

intrinsic CosetIntersection(V::Tup,W::Tup:Weak:=false)->Tup
  {Computes the intersection of two collections of cosets of an abelian group.
   If the parameter Weak is supplied, returns cosets of the kernel associated
   with V, otherwise returns cosets of the intersection of the kernels
   associated with V and W}
  require #V eq 2 and #W eq 2 and ISA(Type(V[1]),Map) and ISA(Type(W[1]),Map)
  and ISA(Type(V[2]),SetEnum) and ISA(Type(W[2]),SetEnum) and
  ISA(Type(Domain(V[1])),GrpAb) and Domain(V[1]) eq Domain(W[1]) and
  Universe(V[2]) eq Codomain(V[1]) and Universe(W[2]) eq Codomain(W[1]):
    "V and W must describe coset collections of the same abelian group";
  m1:=V[1];m2:=W[1];
  if Weak then
    G:=Domain(m1);
    gcd,togcd:=quo<G|Generators(Kernel(m1))join Generators(Kernel(m2))>;
    m1togcd:=hom<Codomain(m1)->gcd|
        [togcd(a@@m1):a in OrderedGenerators(Codomain(m1))]>;
    m2togcd:=hom<Codomain(m2)->gcd|
        [togcd(a@@m2):a in OrderedGenerators(Codomain(m2))]>;
    gcdW:={m2togcd(w):w in W[2]};
    return <V[1],{Universe(V[2])|v:v in V[2]| m1togcd(v) in gcdW}>;
  else
    G:=FreeAbelianGroup(Ngens(Domain(V[1])));
    m1:=hom<G->Image(m1)|[m1(g):g in OrderedGenerators(Domain(m1))]>;
    m2:=hom<G->Image(m2)|[m2(g):g in OrderedGenerators(Domain(m2))]>;
    gcd,togcd:=quo<G|Generators(Kernel(m1))join Generators(Kernel(m2))>;
    lcm,tolcm:=quo<G|Kernel(m1) meet Kernel(m2)>;
    lcmto1:=hom<lcm->Codomain(m1)|[m1(a@@tolcm):a in OrderedGenerators(lcm)]>;
    lcmto2:=hom<lcm->Codomain(m2)|[m2(a@@tolcm):a in OrderedGenerators(lcm)]>;
    m1togcd:=hom<Codomain(m1)->gcd|
        [togcd(a@@m1):a in OrderedGenerators(Codomain(m1))]>;
    m2togcd:=hom<Codomain(m2)->gcd|
        [togcd(a@@m2):a in OrderedGenerators(Codomain(m2))]>;
    function CRT(e1,e2)
      if m1togcd(e1) eq m2togcd(e2) then
        v:=Eltseq(e1@@m1-e2@@m2);
        A1:=[Eltseq(G!a):a in OrderedGenerators(Kernel(m1))];
        A2:=[Eltseq(G!a):a in OrderedGenerators(Kernel(m2))];
        w:=Solution(Matrix(A1 cat A2),Vector(v));
        crt:=tolcm(e1@@m1-Kernel(m1)![w[i]:i in [1..Ngens(Kernel(m1))]]);
        return {crt+a:a in Kernel(lcmto1)meet Kernel(lcmto2)};
      else
        return {lcm|};
      end if;
    end function;
    //This creates #V[2] * #W[2] complexity. Especially if
    //#gcd is comparatively large, one can do quite a bit better by first
    //sorting W[2] according to class in gcd and only CRT-ing with
    //elements of V[2] of the same class in gcd.
    return <hom<Domain(V[1])->lcm|[tolcm(g):g in OrderedGenerators(G)]>,
                  &join[CRT(v,w):v in V[2],w in W[2]]>;
  end if;
end intrinsic;
