freeze;

/*
**
**  TWISTED ROOT DATA
**
**      $Id: RootDtmExt.m 48315 2014-09-09 02:23:13Z don $
**    
**      January-February 2006
**  
**      Sergei Haller, Scott H Murray
**
**
*/

import "Const.m": maxMultiplicity;
import "MapRootDtm.m" : check_matrices;
import "../../Algebra/AlgLie/rootsystem.m" : CartInt;
import "RootDtm.m" : toType, nonredSimpleRoots;

GA_RF := recformat<
  gamma   : GrpPerm,    //  the acting group      
  perm_ac : HomGrp,     //  the permutation action of Gamma, i.e. a hom : Gamma -> Sym(2*N)
  mats_rt,              //  two sequences of matrices describing the linear
  mats_co >;            //  action of Gamma on the (co)root spaces

declare attributes RootDtm:
  RelativeRootDatum;

forward test_tits_index;

computeGA := function(R, twist)

/*
**  This function will accept following kinds of arguments:
**  
**          HomGrp: (only if IsSemiSimple)
**                  a homomorphism from Gamma into AutoDW.
**                  we don't check those.
**  
**               i: (only if i eq 1 or (IsSemisimple and IsIrreducible))
**                  integer, e.g.,  1,2,3,6   for   1D4, 2D4, 3D4, 6D4
**  
**          <DO,i>: (only if IsSemiSimple and IsIrreducible)
**                  DO is a set of distinguished orbits as sets of integers
**                  i (integer) is the order of the Dynkin diagram symmetry involved
**
**	GrpPermElt ims: A permutation of the Dynkin Diagram; equivalent to <Gamma,ims>
**                  below, but Gamma is computed automatically.
**  
**     <Gamma,ims>: (only if IsSemiSimple)
**                  Gamma is the acting group.
**                  ims define images either as permutations on the Dynkin diagram,
**                  e.g. (1,5)(2,3) for 2A5
**                  or as elements in AutoDW.
**  
**     <Gamma,imsR,imsC>:
**                  Gamma is the acting group.
**                  imsR (imsC) is a sequence of matrices defining the action
**                  of Gamma on the RootSpace (CorootSpace)
**  
**  we return an error as a string if something different was passed.
**
**  returned is a record in format GA_RF.
**
*/

    n := Rank(R);
    d := Dimension(R);
    N := NumPosRoots(R);
    codom := N eq 0 select Sym(1) else Sym(2*N);
    
    function from_perm(twist)
        Ga := Domain(twist);
        M := MatrixAlgebra(BaseRing(R),d);
        return rec<GA_RF| gamma := Ga, perm_ac := twist,
            mats_rt := [M| R`SimpleRoots^-1   * Matrix( [  Root(R,r^twist(Ga.i)) : r in [1..n]] ) : i in [1..Ngens(Ga)]],
            mats_co := [M| R`SimpleCoroots^-1 * Matrix( [Coroot(R,r^twist(Ga.i)) : r in [1..n]] ) : i in [1..Ngens(Ga)]]>;
    end function;

    case Category(twist):
    when HomGrp:
        if not IsSemisimple(R) then
            return "Root datum must be semisimple for this type of twist";
		elif #GSet(Codomain(twist)) ne #Roots(R) then
			return Sprintf("Incompatible codomain of twist (should act on set of size %o)", #Roots(R));
        else
            return from_perm(twist);
        end if;
    when RngIntElt:
        if twist eq 1 then
	    return from_perm( hom<Sym(1)->codom|[]> );
        elif not IsIrreducible(R) then
            return "Root datum must be irreducible for this type of twist";
        else
            if maxMultiplicity(R) gt 1 and twist ne 1 then
                return "The induced permutation on roots is not a linear map";
            end if;
            DD := AutoDD(R);
            if not exists(s){c`subgroup:c in SubgroupClasses(DD)|c`order eq twist} then
                return Sprintf("There is no subgroup of order %o in the group"*
                               " of symmetries of the Dynkin diagram", twist);
            else
                return from_perm(hom<s->codom|[ExtendDynkinDiagramPermutation(R,s.i) : i in [1..Ngens(s)]] >);
            end if;
        end if;
	when GrpPermElt:
		if not IsSemisimple(R) then
			return "Root datum must be semisimple for this type of twist";
		end if;
		if Degree(Parent(twist)) ne Rank(R) then
			return "The degree of the permutation should be equal to the rank of R";
		end if;
		Gamma := CyclicGroup(Order(twist));
		return $$(R, <Gamma, [twist]>);
    when Tup:
        if #twist notin {2,3} then
            return "Wrong number of components in the Twist parameter";
        end if;

        if ISA(Category(twist[1]),GrpPerm) then
            Ga := twist[1];
            tits_index := false;
        elif ISA(ExtendedCategory(twist[1]),SetEnum[SetEnum]) then
            DO := twist[1];
            tits_index := true;
        else
            return "The first component of the Twist parameter is not GrpPerm";
        end if;

        if #twist eq 2 then
            if not IsSemisimple(R) then
                return "Root datum must be semisimple for this type of twist";
            else
                if tits_index then
                    if not IsIrreducible(R) then
                        return "Root datum must be semisimple and irreducible for this type of twist";
                    end if;
                    twist := twist[2];
                    if twist eq 1 then 
                        tau := Sym(n)!1;
                    else
                        if maxMultiplicity(R) gt 1 then
                            return "The induced permutation on roots is not a linear map";
                        end if;
                        DD := AutoDD(R);
                        if not exists(s){c`subgroup:c in SubgroupClasses(DD)|
                            c`order eq twist and forall{o:o in DO|GSet(c`subgroup,o) eq o}} then
                            DO := Setseq(DO);
                            return Sprintf("There is no subgroup of order %o in the group "*
                                           "of symmetries of\nthe Dynkin diagram "*
                                           "that has orbits {%o}", twist,
                                           &*[Sprintf("%o%o",DO[i],i eq #DO select "" else ", ") : i in [1..#DO]]);
                        end if;
                        tau := s.1;
                    end if;
                    if twist eq 6 then
                        Ga := s;
                        case DO:
                        when {{2}}:
                            // s = sub<Sym(4)|(3,4),(1,4,3)> 
                            etau2 := RootPermutation( hom<R->R|Sym(4)!(3,4)  > );
                            etau3 := RootPermutation( hom<R->R|Sym(4)!(1,3,4)> );
                            W := CoxeterGroup(R);
                            ims := [etau2*W.1*W.3*W.4,etau3];
                        when {{2},{1,3,4}}:
                            // s = sub<Sym(4)|(3,4),(1,4,3)> 
                            ims := [Sym(4)|(3,4),(1,4,3)];
                        else:
                            return "Invalid distinguished orbits given";
                        end case;
                    else
                        Ga,ims := test_tits_index(R,DO,tau);
                    end if;
                else /* not tits_index */
                    ims := twist[2];
                    if not ISA(ExtendedCategory(ims), SeqEnum[GrpPermElt]) then
                        return "The second component of the Twist parameter is not a sequence of permutations";
                    end if;
                end if;

                case Degree(Universe(ims)):
                when 2*N: ;
                    W := CoxeterGroup(R);
                    if maxMultiplicity(R) gt 1 and exists{im:im in ims|im notin W} then
                        return "The induced permutation on roots is not a linear map";
                    end if;
                when n:
                    if maxMultiplicity(R) gt 1 and exists{im:im in ims|Order(im) gt 1} then
                        return "The induced permutation on roots is not a linear map";
                    end if;
                    ims := [ExtendDynkinDiagramPermutation(R,ims[i]) : i in [1..Ngens(Ga)]];
                else:
                    return "permutations have wrong degree";
                end case;

                is_hom, h := IsHomomorphism(Ga,codom,ims);
                if is_hom then
                    return from_perm(h);
                else
                    return "The second component of the Twist parameter does not define a homomorphism";
                end if;
            end if;
        else // elif #twist eq 3 then
            mats_rt := twist[2];
            mats_co := twist[3];
            if not ( ISA(ExtendedCategory(mats_rt), SeqEnum[Mtrx]) and
	    ISA(ExtendedCategory(mats_co), SeqEnum[Mtrx]) ) then
                return "The second and third components of the Twist parameter must be sequences of matrices";
            elif #{#mats_rt,#mats_co,Ngens(Ga)} ne 1 then
                return "Number of matrices must be equal to number of generators of the acting group";
            end if;
		    n := Dimension( R );
		    M := MatrixAlgebra( Rationals(), n );
		    okr, mats_rt := CanChangeUniverse( mats_rt, M );
		    okc, mats_co := CanChangeUniverse( mats_co, M );
		    if not ( okr and okc ) or 
		    	exists{i:i in [1..Ngens(Ga)]| not check_matrices(R,R,mats_rt[i],mats_co[i] : Check := true)} then
	                return "Given matrices do not define maps of root data";
	        end if;
            if (N eq 0) then
                return rec<GA_RF| gamma := Ga, perm_ac := hom<Ga->codom|[Sym(1)|1:i in [1..Ngens(Ga)]]>,
                    mats_rt := mats_rt, mats_co := mats_co >;
            else
                rts := Roots(R);
                cor := Coroots(R);
                perm_rt := [ codom![ Position(rts,rts[r]*mats_rt[i]) : r in [1..2*N] ] : i in [1..Ngens(Ga)]];
                perm_co := [ codom![ Position(rts,rts[r]*mats_rt[i]) : r in [1..2*N] ] : i in [1..Ngens(Ga)]];
                if perm_rt ne perm_co then
                    return "Root and coroot action matrices define different permutations on roots and coroots";
                end if;
                return rec<GA_RF| gamma := Ga, perm_ac := hom<Ga->codom|perm_rt>, mats_rt := mats_rt, mats_co := mats_co >;
            end if;
        end if;
    else
        return "Wrong parameter Twist";
    end case;

end function;

intrinsic ExtendDynkinDiagramPermutation( R::RootStr, p::GrpPermElt ) -> GrpPermElt
{Internal function.  Extend a permutation of the simple roots to a permutation of all roots}
  n := Rank( R );  
  require n gt 0 : "The root datum/system must not be toral";
  require n eq Degree(Parent(p)) 
    : "The degree of the permutation must be equal to the rank of the root datum/system";

  pinv := p^-1;
  N := NumPosRoots(R);
  Phi := Roots( R : Basis:= "Root" );
  norms := RootNorms( R );
  ChangeUniverse( ~norms, Integers() );
  apply := func< r | Parent(v)![ v[i^pinv] * 
    ( (i eq i^pinv) select 1 else (norms[i^pinv]/norms[r]) ) : i in [1..n] ] 
    where v is Phi[r] >;
  seq := [ Position( Phi, apply(r) ) : r in [1..2*N] ];

  // this we actually should be able to check at the beginning!!
  require Seqset(seq) eq {1..2*N} : "The permutation must be a morphism of the Dynkin diagram";

  p := Sym(2*N)!seq;
  return p;
end intrinsic;



intrinsic AutoDD( R::RootDtm ) -> GrpPerm
{Internal.  Group of symmetries of the dynkin diagram as permutation group on simple roots}

    if assigned R`AutoDD then
        return R`AutoDD;
    end if;

    fullrank := Rank(R);
    
    if fullrank eq 0 then
        R`AutoDD := Sym(1);
    else
        G := Sym(fullrank);
        gens := [G|];

        for S in toType(R) do
            rts := S[2];
            n   := #rts;
            case S[1]:
            when "A", "F":
                Append(~gens, &*[G| (rts[n-i+1],rts[i]) : i in [1..n div 2]]);
            when "B", "C", "G":
                if n eq 2 then
                    // the group autos only exist in char 2, 2, and 3 respectively
                    // but the diagramms are intdep. of the char.
                    Append(~gens, G!(rts[1],rts[2]));
                end if;
            when "D":
                if n gt 1 then
                    Append(~gens, G!(rts[n-1],rts[n]));
                end if;
                if n eq 4 then
                    Append(~gens, G!(rts[1],rts[3],rts[4]));
                end if;
            when "E":
                if n eq 6 then
                    Append(~gens, G!(rts[1],rts[6])(rts[3],rts[5]));
                end if;
            end case;
        end for;
 
        R`AutoDD := sub<G|gens>; _:= Order(R`AutoDD);
    end if;
    
    return R`AutoDD;
end intrinsic;

intrinsic AutoDR( R::RootDtm ) -> GrpPerm
{Intenal.  Group of symmetries of the dynkin diagram as permutation group on all roots}

    if assigned R`AutoDR then
        return R`AutoDR;
    end if;

    N := NumPosRoots(R);
    
    if N eq 0 then
        R`AutoDR := Sym(1);
        R`dd2dr  := iso<Sym(1)->Sym(1)|>;
    end if;
    
    DD       := AutoDD(R); n := Ngens(DD);
    DR       := sub<Sym(2*N)| [ ExtendDynkinDiagramPermutation(R,DD.i) : i in [1..n]] >;
    R`dd2dr  := iso< DD->DR | [ DR.i                                   : i in [1..n]] >;
    R`AutoDR := DR; _ := Order(DR);
    
    return R`AutoDR;
end intrinsic;

intrinsic AutoDW( R::RootDtm ) -> GrpPerm
{Internal.  Automorphism group of R}

    if assigned R`AutoDW then
        return R`AutoDW;
    end if;

    if Rank(R) eq 0 then
        R`AutoDW := Sym(1);
    else
        W := CoxeterGroup(R);
        N := NumPosRoots(R);
        DR := AutoDR(R);

        R`AutoDW := sub<Sym(2*N)|DR,W>;
    end if;
    
    return R`AutoDW;
end intrinsic;





intrinsic TwistedRootDatum( R::RootDtm : Twist:=1 ) -> RootDtm
{Twisted version of the root datum R}

    require Category(R) ne RootDtmSprs : "Root datum is sparse";
    require IsReduced(R)               : "Root datum is non-reduced";

	if Twist cmpeq 1 then
		printf "WARNING: TwistedRootDatum with Twist := 1 will return an untwisted root datum.\n";
	end if;

    ga1 := R`GammaAction;
    
    if Category(Twist) ne Rec then
        ga2 := computeGA(R,Twist);
		if Type(ga2) eq MonStgElt then error ga2; end if;
    else 
        ga2 := Twist;
    end if;
    
    g1 := ga1`gamma; 
    g2 := ga2`gamma; 

    require #g1 eq 1 
         or #g2 eq 1 
         or g1 eq g2 and Ngens(g1) eq Ngens(g2) 
                     and [g1.i:i in [1..Ngens(g1)]] eq [g2.i:i in [1..Ngens(g2)]]: 
        "The acting groups must either be the same or one of them must be trivial";

    if #g1 eq 1 then
        new_ga := ga2;
    elif #g2 eq 1 then
        return R;
        new_ga := ga1; 
    else /* g1 eq g2 */
        new_gamma := g1;

        new_mats_rt := [ ga1`mats_rt[i]*ga2`mats_rt[i] : i in [1..Ngens(g2)] ];
        new_mats_co := [ ga1`mats_co[i]*ga2`mats_co[i] : i in [1..Ngens(g2)] ];
    
        new_ga      := computeGA(R,<new_gamma,new_mats_rt,new_mats_co>);
    end if;
        
    T := RootDatum(R`SimpleRoots,R`SimpleCoroots 
                   : Signs := R`ExtraspecialSigns, 
                     Twist := new_ga );

    for attr in [ "IsAdjoint", "IsSimplyConnected" ] do
        if assigned R``attr then
            T``attr := R``attr;
        end if;
    end for;

    return T;
end intrinsic;

intrinsic TwistedRootDatum( N::MonStgElt : Twist:=1 ) -> RootDtm
{Twisted root datum of type N}
	return TwistedRootDatum(RootDatum(N) : Twist := Twist);
end intrinsic;


intrinsic UntwistedRootDatum( R::RootDtm ) -> RootDtm
{Untwisted version of the (twisted) root datum R}

    if not IsTwisted(R) then 
        return R;
    end if;
    
    U := RootDatum(R`SimpleRoots,R`SimpleCoroots 
                   : Signs  := R`ExtraspecialSigns, 
                     Nonreduced := nonredSimpleRoots(R),
                     Twist  := 1 );

    for attr in [ "IsAdjoint", "IsSimplyConnected" ] do
        if assigned R``attr then
            U``attr := R``attr;
        end if;
    end for;

    return U;
end intrinsic;

intrinsic SplitRootDatum( R::RootDtm ) -> RootDtm
{Untwisted version of the (twisted) root datum R}
    return UntwistedRootDatum( R );
end intrinsic;

intrinsic GammaOrbitOnRoots( R::RootDtm, r::RngIntElt ) -> GSetIndx
{Orbit on Phi through r}
    N := NumPosRoots(R);
    return Orbit(Image(R`GammaAction`perm_ac), r);
end intrinsic;

intrinsic GammaOrbitsOnRoots( R::RootDtm ) -> SeqEnum[SeqEnum[GSetIndx]]
{Orbits on Phi}
    N := NumPosRoots(R);
    O := Orbits(Image(R`GammaAction`perm_ac));
    
    // sort orbits
    Sort( ~O, func< x,y | Min(x)-Min(y) > );

    Op := [Universe(O)|];  // positive orbits
    On := [Universe(O)|];  // negative orbits
    Oz := [Universe(O)|];  //   zero   orbits

    for o in O do
          if o subset {1..N} then
            Append(~Op,o);
        elif o subset {N+1..2*N} then
            Append(~On,o);
        else
            Append(~Oz,o);
        end if;
    end for;
    
    return [Op,Oz,On];
end intrinsic;

intrinsic PositiveGammaOrbitsOnRoots( R::RootDtm ) -> SeqEnum[GSetIndx]
{Positive orbits on Phi}
    return GammaOrbitsOnRoots(R)[1];
end intrinsic;

intrinsic ZeroGammaOrbitsOnRoots( R::RootDtm ) -> SeqEnum[GSetIndx]
{Zero-orbits on Phi}
    return GammaOrbitsOnRoots(R)[2];
end intrinsic;

intrinsic NegativeGammaOrbitsOnRoots( R::RootDtm ) -> SeqEnum[GSetIndx]
{Negative orbits on Phi}
    return GammaOrbitsOnRoots(R)[3];
end intrinsic;



intrinsic GammaAction( R::RootDtm ) -> HomGrp
{The action of Gamma on an extended root datum R}
    return R`GammaAction;
end intrinsic;

intrinsic GammaActionOnSimples( R::RootDtm ) -> HomGrp
{The action of Gamma on the simple (co)roots}
    gamma := R`GammaAction`gamma;
    n := AbsoluteRank(R);
    W := CoxeterGroup(R);
    N := NumPosRoots(R);
    if n eq 0 then 
        return hom<gamma->Sym(1)|[1:i in [1..Ngens(gamma)]]>;
    end if;

    len := func< w | #{ r : r in [1..N] | r^w gt N } >;

    Pi  := {1..n};

    function find_w(tau)
        w := W!1;
        l := len(tau);
        while l gt 0 do
            _ := exists(i){i:i in Pi|len(tau*W.i) lt l};
            tau *:= W.i;
            w   *:= W.i;
            l   -:= 1;
        end while;
        return w;
    end function;

    ims := [Sym(n)| [1..n]^(tau * find_w(tau)) 
                        where tau is R`GammaAction`perm_ac(gamma.i)     
                  : i in [1..Ngens(gamma)] ];

    return hom<gamma->Sym(n)|ims>;
end intrinsic;

intrinsic OrbitsOnSimples( R::RootDtm ) -> SeqEnum[GSetIndx]
{Orbits of the [Gamma]-action}
    O := Orbits(Image(GammaActionOnSimples(R)));
    Sort( ~O, func< x,y | Min(x)-Min(y) > );
    return O;
end intrinsic;

intrinsic DistinguishedOrbitsOnSimples( R::RootDtm ) -> SeqEnum[GSetIndx]
{Distinguished orbits of the [Gamma]-action}
    O  := OrbitsOnSimples(R);
    Op := PositiveGammaOrbitsOnRoots(R);
    return [ o : o in O | exists{op:op in Op| Rep(o) in op} ];
end intrinsic;




intrinsic AbsoluteRank( R::RootDtm ) -> RngIntElt
{The absolute rank of R}
    return Rank(R);
end intrinsic;

intrinsic RelativeRank( R::RootDtm ) -> RngIntElt
{The relative rank of R}
    return #DistinguishedOrbitsOnSimples(R);
end intrinsic;

intrinsic IsAnisotropic( R::RootDtm ) -> RngIntElt
{True iff R is anisotropic}
    return RootSpace(R) eq ZeroRootSpace(R);
end intrinsic;

intrinsic TwistingDegree( R::RootDtm ) -> RngIntElt
{The ``twisting degree'', e.g. the 3 in $^3D_4$}
    gamma := R`GammaAction`gamma;
    return Integers()!(#gamma/#Kernel(GammaActionOnSimples(R)));
end intrinsic;

intrinsic IsInner( R::RootDtm ) -> BoolElt, RngIntElt
{Returns true iff the (twisted) root datum is inner. 
the twisting degree is returned as the second value}
    return t eq 1, t where t is  TwistingDegree(R)  ;
end intrinsic;

intrinsic IsOuter( R::RootDtm ) -> BoolElt, RngIntElt
{Returns true iff the (twisted) root datum is outer.
the twisting degree is returned as the second value}
    return t gt 1, t where t is  TwistingDegree(R)  ;
end intrinsic;



intrinsic IsTwisted( R::RootDtm ) -> BoolElt
{Returns true iff the root datum is twisted, that is, nonsplit}
    return exists{a:a in R`GammaAction`mats_rt|a ne Universe(R`GammaAction`mats_rt)!1};
end intrinsic;

intrinsic IsSplit( R::RootDtm ) -> BoolElt
{Returns true iff the root datum is split}
    return forall{a:a in R`GammaAction`mats_rt|a eq 1};
end intrinsic;

intrinsic IsQuasisplit( R::RootDtm ) -> BoolElt
{Returns true iff the root datum is quasisplit}
    return OrbitsOnSimples(R) eq DistinguishedOrbitsOnSimples(R);
    // same, but creates a root datum:
    return Rank(AnisotropicSubdatum(R)) eq 0;
end intrinsic;




intrinsic TwistedCartanName( R::RootDtm ) -> MonStgElt
{}

    // this is quite complicated if we've got combined root data.
    // we have to go over R`Type and take all normalised irred. components
    // then go over the rest and take all subsets of two, which are normalised
    // then all subsets of three, and so on...

    // first we took it easy and assumed that all irreducible components are
    //      normalised... but that was no good
    // now we just do a "general" thing for compound types, e.g.
    //      2(A1 A1)2,0
    
    type := "";
    
    // workaround for compound types
    if #toType(R) gt 1 then
    
        td := TwistingDegree(R);
        rr := RelativeRank(R);
        ar := AbsoluteRank(R);
        ct := CartanName(R);
//        ct := ct[1..#ct-1];
// DET Cartan name does not have a space at the end 2011-06-03

        // wonna be clever :)
        td := td eq 1  select "" else td;
        rr := rr eq ar select "" else Sprintf(",%o",rr);
        
        type *:= Sprintf("%o(%o)%o%o ", td,ct,ar,rr) ;

        return type;
        
    end if;
    
    for t in toType(R) do // only one element here !!
        
        S := sub< R | t[2] >;
        
        td := TwistingDegree(S);
        rr := RelativeRank(S);
        ar := #t[2]; // absolute rank
        ct := t[1];  // cartan type
        
        // wonna be clever :)
        td := td eq 1  select "" else td;
        rr := rr eq ar select "" else Sprintf(",%o",rr);

        type *:= Sprintf("%o%o%o%o ", td,ct,ar,rr);

    end for;

    return type;
end intrinsic;

intrinsic TwistedCartanName( R::RootDtmSprs ) -> MonStgElt
{The type of the twisted root datum}
    // don't have twisted sparse root data. so just return CartanName
    return CartanName(R);
end intrinsic;

intrinsic GammaRootSpace( R::RootDtm ) -> ModTupFld, Map
{The fixed point space of Gamma on the rational root space QX of R}
    d := Dimension(R);
    I := MatrixAlgebra(Rationals(),d)!1;
    
    A := [ M - I : M in R`GammaAction`mats_rt ];

    return sub<RootSpace(R)|&meet[ NullSpace(a) : a in A ]>;
end intrinsic;


intrinsic GammaCorootSpace( R::RootDtm ) -> ModTupFld, Map
{The fixed point space of Gamma on the rational coroot space QY of R}
    d := Dimension(R);
    I := MatrixAlgebra(Rationals(),d)!1;
    
    A := [ M - I : M in R`GammaAction`mats_co ];

    return sub<CorootSpace(R)|&meet[ NullSpace(a) : a in A ]>;
end intrinsic;


intrinsic ZeroRootSpace( R::RootDtm ) -> ModTupFld, Map
{The zero root space QX0 of R}

    gamma   := R`GammaAction`gamma;
    perm_ac := R`GammaAction`perm_ac;
    mats    := R`GammaAction`mats_rt;
    GaFP, h := FPGroup(gamma);

    fix := function(word)
        newword := [];
        for w in word do 
            if w gt 0 then
                Append(~newword,w);
            else
                newword cat:= [-w:i in [1..Order(gamma.-w)-1]];
            end if;
        end for;
        return newword;
    end function;

    A := &+[ &*mats[word] where word is fix(Eltseq(ga@@h)) 
           : ga in gamma ];

    return sub<RootSpace(R)| NullSpace(A) >;
end intrinsic;

intrinsic ZeroRootLattice( R::RootDtm ) -> ModTupFld
{The zero root lattice X0 of R}

    gamma   := R`GammaAction`gamma;
    perm_ac := R`GammaAction`perm_ac;
    mats    := R`GammaAction`mats_rt;
    GaFP, h := FPGroup(gamma);

    fix := function(word)
        newword := [];
        for w in word do 
            if w gt 0 then
                Append(~newword,w);
            else
                newword cat:= [-w:i in [1..Order(gamma.-w)-1]];
            end if;
        end for;
        return newword;
    end function;

    A := &+[ &*mats[word] where word is fix(Eltseq(ga@@h)) 
           : ga in gamma ];

    A := Matrix(Integers(),A);

    return Lattice(Matrix(Basis(NullSpace(A))));
end intrinsic;

/*
 * intrinsic ZeroCorootLattice( R::RootDtm ) -> ModTupFld
 * {The zero root space X0 of R}
 * 
 *     gamma   := R`GammaAction`gamma;
 *     perm_ac := R`GammaAction`perm_ac;
 *     mats    := R`GammaAction`mats_co;
 *     GaFP, h := FPGroup(gamma);
 * 
 *     fix := function(word)
 *         newword := [];
 *         for w in word do 
 *             if w gt 0 then
 *                 Append(~newword,w);
 *             else
 *                 newword cat:= [-w:i in [1..Order(gamma.-w)-1]];
 *             end if;
 *         end for;
 *         return newword;
 *     end function;
 * 
 *     A := &+[ &*mats[word] where word is fix(Eltseq(ga@@h)) 
 *            : ga in gamma ];
 * 
 *     A := Matrix(Integers(),A);
 * 
 *     return Lattice(Matrix(Basis(NullSpace(A))));
 * end intrinsic;
 * 
 * intrinsic ZeroCorootSpace( R::RootDtm ) -> ModTupFld
 * {The zero coroot space Y0 of R}
 * 
 *     gamma   := R`GammaAction`gamma;
 *     perm_ac := R`GammaAction`perm_ac;
 *     mats    := R`GammaAction`mats_co;
 *     GaFP, h := FPGroup(gamma);
 * 
 *     fix := function(word)
 *         newword := [];
 *         for w in word do 
 *             if w gt 0 then
 *                 Append(~newword,w);
 *             else
 *                 newword cat:= [-w:i in [1..Order(gamma.-w)-1]];
 *             end if;
 *         end for;
 *         return newword;
 *     end function;
 * 
 *     A := &+[ &*mats[word] where word is fix(Eltseq(ga@@h))
 *            : ga in gamma ];
 * 
 *     return sub<CorootSpace(R)| NullSpace(A) >;
 * end intrinsic;
 */

intrinsic AnisotropicSubdatum( R::RootDtm ) -> RootDtm
{The anisotropic subdatum of R}

    require AbsoluteRank(R) ge 1 : "The root datum is a torus";
    
    Pi0 := Setseq(
            &join ChangeUniverse(             OrbitsOnSimples(R), Parent({1}))
       diff &join ChangeUniverse(DistinguishedOrbitsOnSimples(R), Parent({1}))
    );

    return sub< R | Pi0 >;

    W := CoxeterGroup(R);
    W0 := ReflectionSubgroup(W,Pi0);
    R0 := RootDatum(W0);

    return R0;
end intrinsic;




intrinsic RelativeRootSpace( R::RootDtm ) -> ModTupFld, Map
{The relative root space X/X0 of R}
    X  := RootSpace(R);
    X0 := ZeroRootSpace(R);
    return quo<X|X0>;
end intrinsic;

/*
 * intrinsic RelativeCorootSpace( R::RootDtm ) -> ModTupFld, Map
 * {The relative coroot space Y/Y0 of R}
 *     Y  := CorootSpace(R);
 *     Y0 := ZeroCorootSpace(R);
 *     return quo<Y|Y0>;
 * end intrinsic;
 */

intrinsic PositiveRelativeRoots( R::RootDtm ) -> SetIndx
{The relative roots of R}
    _, pi := RelativeRootSpace(R);
    
    Op := PositiveGammaOrbitsOnRoots(R);

    // pi( Phi+ \setminus X_0 )
    return pi(Roots(R)[[Rep(o):o in Op]]);
end intrinsic;

/*
 * intrinsic PositiveRelativeCoroots( R::RootDtm ) -> SetIndx
 * {The relative coroots of R}
 *     _, pi := RelativeCorootSpace(R);
 *     
 *     Op := PositiveGammaOrbitsOnRoots(R);
 * 
 *     // pi( Phi+ \setminus X_0 )
 *     return pi(Coroots(R)[[Rep(o):o in Op]]);
 * end intrinsic;
 */

intrinsic NegativeRelativeRoots( R::RootDtm ) -> SetIndx
{The relative roots of R}
    _, pi := RelativeRootSpace(R);
    On := NegativeGammaOrbitsOnRoots(R);

    // pi( Phi- \setminus X_0 )
    return pi(Roots(R)[[Rep(o):o in On]]);
end intrinsic;

/*
 * intrinsic NegativeRelativeCoroots( R::RootDtm ) -> SetIndx
 * {The relative coroots of R}
 *     _, pi := RelativeCorootSpace(R);
 *     
 *     On := NegativeGammaOrbitsOnRoots(R);
 * 
 *     // pi( Phi+ \setminus X_0 )
 *     return pi(Coroots(R)[[Rep(o):o in On]]);
 * end intrinsic;
 */

intrinsic SimpleRelativeRoots( R::RootDtm ) -> SetIndx
{The relative roots of R}
    _, pi := RelativeRootSpace(R);
    return [ pi(Root(R,Rep(o))) : o in DistinguishedOrbitsOnSimples(R)];
end intrinsic;

/*
 * intrinsic SimpleRelativeCoroots( R::RootDtm ) -> SetIndx
 * {The relative roots of R}
 *     _, pi := RelativeCorootSpace(R);
 *     return [ pi(Coroot(R,Rep(o))) : o in DistinguishedOrbitsOnSimples(R)];
 * end intrinsic;
 */

intrinsic RelativeRoots( R::RootDtm ) -> SetIndx
{The relative roots of R}
    // pi( Phi \setminus X_0 )
    return PositiveRelativeRoots(R) join NegativeRelativeRoots(R);
end intrinsic;


/*
**   This function implements the method described on
**   page 40 in Tits 66 "Classif. of alg. semisimpl. grps."
*/
function cartan_by_tits(R)

    DO := DistinguishedOrbitsOnSimples(R);
    l := RelativeRank(R);
    
    TI := MatrixAlgebra(Rationals(),l)!0;
    
    C  := Matrix(Rationals(),CartanMatrix(R));
    CI := C^-1;
    
    for i,j in [1..l] do
    
        TI[i,j] := &+[CI[r,s]:r in DO[i],s in DO[j]];
    
    end for;
    
    T := TI^-1;
    
    return T;
end function;

intrinsic RelativeRootDatum( R::RootDtm ) -> RootDtm
{The relative root datum of R}

    if assigned R`RelativeRootDatum then
        return R`RelativeRootDatum;
    end if;

    posR  := PositiveRelativeRoots(R);
    negR  := NegativeRelativeRoots(R);
    fullR := posR join negR;
    fundR := SimpleRelativeRoots(R);
    n := #fundR;

    // reduced system? if not: which fundamental root has its double
    nonred := { r : r in [1..n] | 2*fundR[r] in posR };    

    // calculate the Cartan matrix
    C := Matrix( Integers(), n,n,
            [ CartInt( fullR, fundR[i], fundR[j] ) : i,j in [1..n] ]
         );

    // compute the fundamental relative coroots
    A := Matrix(fundR);
    B := Transpose(A^-1*C);

    // I don't think we need signs here, since the multiplication
    // will base on the multiplication of the untwisted form.
    
    Rrel := RootDatum( A,B : Nonreduced := nonred );
       _ := IsAdjoint(Rrel);
       _ := IsSimplyConnected(Rrel);

    // if false and not IsReduced(Rrel) then
    //     IndentPush();
    //     "This is a non-reduced root datum. Non-reduced root data are freshly implemented.";
    //     "Please double-check the results and email sergei@maths.usyd.edu.au if anything is wrong";
    //     // replace by magma-bugs@maths.usyd.edu.au
    //     IndentPop();
    // end if;

    R`RelativeRootDatum := Rrel;

    return Rrel;
end intrinsic;



function test_tits_index( R, pi_, tau ) 
    // R   - RootDatum
    // pi_ - indices of the distinguished orbits on pi (set of sets)
    // tau - the dynkin diagramm symmetry

// this only works when Gamma is cyclic!!!
//
//   i.e. in all cases but in ^6D_4,*
//

    N   := NumPosRoots(R);
    n   := Rank(R);

    tau_orbs := Orbits(sub<Sym(n)|tau>); 
    ok := forall{i:i in pi_| exists{o:o in tau_orbs|i eq o} };
    if not ok then
        error "Distinguished orbits and tau do not fit together";
    end if;

    W   := CoxeterGroup(R);
    etau := ExtendDynkinDiagramPermutation(R,tau);
    
    pi0 := {1..n} diff &join pi_;
    // don't call subdatum, since the root datum is not yet complete!!!
    // R0  := sub< R | pi0 >;
    // we actually only want the positive roots spanned by pi0.
    //

    V0 := sub<RootSpace(R)|{Root(R,i) : i in pi0}>;
    psi := [i:i in [1..N]| Root(R,i) notin V0];
    
    if not 
    exists(w){ w : w in W |
         //    forall{ i : i in pi_ | o subset o           where o is Orbit(s,Rep(i)) } and
         //  don't know why this was here. just left it here if it was here for some reason (???)
             forall{ i : i in psi | o subset Seqset(psi) where o is Orbit(s,    i ) }
         and forall{ i : i in pi0 | not Orbit(s,i) subset {1..N} }
         and forall{ o : o in Orbits(s) | o subset {1..N} or o subset {N+1..2*N} or &+Roots(R)[Setseq(o)] eq 0 }
         where s is sub<Sym(2*N)|etau*w> }
    then error "No Weyl element found !!!";
    end if;

    // print "There might be much ``better'' choices for the Weyl element.\nWe just pick first available one.";

    //s := sub<Sym(2*N)|etau*w>;
    o := Order(etau*w);
    
    if o eq 1 then
        return Sym(1),                 [];
    else 
        return CyclicGroup(GrpPerm, o),[etau*w];
    end if;
end function;

// J_delta
intrinsic GammaOrbitsRepresentatives( R::RootDtm, delta::RngIntElt ) -> SeqEnum
{Returns the representatives J_delta. delta is the root in the relative root datum of R}
    R0 := RelativeRootDatum(R);
    
    requirerange delta, 1, 2*NumPosRoots(R0);

    delta_rt := Root(R0,delta);
    
    _,pi := RelativeRootSpace(R);
    gammaOrbits := GammaOrbitsOnRoots(R);
    gammaOrbits := gammaOrbits[1] cat gammaOrbits[3];
      // take positive and negative orbits, ignore isotropic orbits
      
    return [ Rep(o) : o in gammaOrbits
                    | pi(Root(R,Rep(o))) eq delta_rt ]; 
    
end intrinsic;




