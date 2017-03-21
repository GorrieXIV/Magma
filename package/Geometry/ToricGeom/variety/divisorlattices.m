freeze;

/////////////////////////////////////////////////////////////////////////
// divisorlattices.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 40461 $
// $Date: 2012-10-18 04:46:47 +1100 (Thu, 18 Oct 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Creation and operations with divisor related lattices and groups.
/////////////////////////////////////////////////////////////////////////

import "../lattice/lattice.m": lattice_get_Zlattice;

declare attributes TorVar:
    cartier_to_weil_map,            // The lattice map from T-inv Cartier divs
                                    // to T-inv Weil divs (=Dual(Raylattice))
    Picard_to_class_lattices_map;   // The embedding of Pic in DivCl lattices

/////////////////////////////////////////////////////////////////////////
// Divisor related lattices
/////////////////////////////////////////////////////////////////////////

intrinsic RayLattice(X::TorVar) -> TorLat
{The lattice of dimension equal to the number of rays of the fan of X}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return RayLattice(CoxRing(X));
end intrinsic;

intrinsic CoxMonomialLattice(X::TorVar) -> TorLat
{The lattice whose elements represent monomials on X (or Weil Divisors on X). It is dual to Ray Lattice.}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return CoxMonomialLattice(CoxRing(X));
end intrinsic;

intrinsic RayLatticeMap(X::TorVar) -> Map[TorLat,TorLat]
{The map from the ray lattice of X to the 1-parameter subgroups lattice of X, which maps generators of the ray lattice to rays of the fan.}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return RayLatticeMap(CoxRing(X));
end intrinsic;

intrinsic CartierToWeilMap(X::TorVar) -> Map[TorLat, TorLat]
{The embedding map from the lattice of T-invariant Cartier divisors to the lattice of T-invariant Weil divisors of X.}
    if not assigned X`cartier_to_weil_map then
        require IsField(BaseRing(X)): "Base ring must be a field";
        rays:=AllRays(Fan(X));
        cone_indices:=ConeIndices(Fan(X));
        ML:=MonomialLattice(X);
        MLdim:=Dimension(ML);
        indices:=[PowerSequence(Integers()) | SetToSequence(I) :
                                            I in Subsets({1..#cone_indices},2)];
        if IsEmpty(indices) then
            X`cartier_to_weil_map:=Dual(RayLatticeMap(X));
        else
            embs1:=[];
            projs1:=[];
            Z:=ZeroMatrix(Integers(), MLdim, MLdim);
            I:=IdentityMatrix(Integers(),MLdim);
            Zrow:=[Z : i in [1..#cone_indices]];
            for i in [1..#cone_indices] do
                S:=Zrow;
                S[i]:=I;
                Append(~embs1,HorizontalJoin(S));
                Append(~projs1,VerticalJoin(S));
            end for;
            restrictions:=[* Transpose(EchelonForm(Matrix(
                             [Universe(rays) | rays[i] :
                                i in cone_indices[I[1]] meet
                                       cone_indices[I[2]]]))) : I in indices *];
            cachedIDs:=AssociativeArray(Integers());
            cachedZeros:=AssociativeArray(PowerSequence(Integers()));
            embs2:=[* *];
            for i in [1..#restrictions] do
                dim1:=Ncols(restrictions[i]);
                bool,I:=IsDefined(cachedIDs,dim1);
                if not bool then
                    I:=IdentityMatrix(Integers(),dim1);
                    cachedIDs[dim1]:=I;
                end if;
                for j in [1..#restrictions] do
                    if i eq j then
                        M2:=I;
                    else
                        dim2:=Ncols(restrictions[j]);
                        bool,Z:=IsDefined(cachedZeros,[dim1,dim2]);
                        if not bool then
                            Z:=ZeroMatrix(Integers(),dim1,dim2);
                            cachedZeros[[dim1,dim2]]:=Z;
                        end if;
                        M2:=Z;
                    end if;
                    if j eq 1 then
                        M1:=M2;
                    else
                        M1:=HorizontalJoin(M1,M2);
                    end if;
                end for;
                Append(~embs2,M1);
            end for;
            delete cachedIDs;
            delete cachedZeros;
            phi:=&+[(projs1[indices[i][1]] - projs1[indices[i][2]]) * 
                             (restrictions[i] * embs2[i]) : i in [1..#indices]];
            delete embs2;
            delete restrictions;
            delete indices;
            psi:=Basis(Kernel(phi));
            delete phi;
            mtrx:=[CoxMonomialLattice(X)|];
            for b in psi do
                weil:=[Integers()|];
                for i in [1..#rays] do
                    if i in VirtualRayIndices(Fan(X)) then
                        Append(~weil, Zero(Integers()));
                    else 
                        j:=Index([i in cone: cone in cone_indices], true);
                        Append(~weil, -((rays[i]) * (ML ! ((Matrix([b]) *
                                                              projs1[j])[1]))));
                    end if;
                end for;
                Append(~mtrx,weil);
            end for;
            delete psi;
            _,cartier_to_weil_map:=Sublattice(mtrx : name:="TCart%d");
            X`cartier_to_weil_map:=cartier_to_weil_map;
        end if;
    end if;
    return X`cartier_to_weil_map;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Picard and divisor class lattices and groups
/////////////////////////////////////////////////////////////////////////

intrinsic WeilToClassLatticesMap(X::TorVar) ->  Map[TorLat,TorLat]
{The surjective lattice map from CoxMonomialLattice to the DivisorClassLattice}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return WeilToClassLatticesMap(CoxRing(X));
end intrinsic;

intrinsic PicardToClassLatticesMap(X::TorVar) -> Map[TorLat,TorLat]
{The natural embedding of Picard lattice into divisor class lattice}
    if not assigned X`Picard_to_class_lattices_map then
        require IsField(BaseRing(X)): "Base ring must be a field";
        weil_to_class:=WeilToClassLatticesMap(X);
        class:=Codomain(weil_to_class);
        cart_to_weil:=CartierToWeilMap(X);
        cart_to_class:=cart_to_weil*weil_to_class;
        pic_gens:=cart_to_class(Basis(Domain(cart_to_class)));
        _,Picard_to_class:=Sublattice(pic_gens : name:="Pic%d");
        X`Picard_to_class_lattices_map:=Picard_to_class;
    end if;
    return  X`Picard_to_class_lattices_map;
end intrinsic;

intrinsic PicardLattice(X::TorVar) -> TorLat
{The lattice, whose integral elements correspond to Cartier divisors up to linear equivalence and modulo torsion}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return Domain(PicardToClassLatticesMap(X));
end intrinsic;

intrinsic DivisorClassLattice(X::TorVar) -> TorLat	
{The divisor class lattice of X, i.e. the lattice of Weil divisors modulo linear equivalence and modulo torsion}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return DivisorClassLattice(CoxRing(X));
end intrinsic;

intrinsic WeilToClassGroupsMap(X::TorVar) ->  Map[ModED, ModED]
{The surjective map of Z-modules from underlying module of CoxMonomialLattice to DivisorClassGroup}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return WeilToClassGroupsMap(CoxRing(X));
end intrinsic;

//THINK: Add PicardGroup and fix this...
intrinsic PicardToClassGroupsMap(X::TorVar)-> Map[ModED, ModED]
{The embedding of Picard group into the divisor class group}
    require IsField(BaseRing(X)): "Base ring must be a field";
    Pic:=lattice_get_Zlattice(PicardLattice(X));
    M:=DefiningMatrix(PicardToClassLatticesMap(X));
    q:=NumberOfQuotientGradings(X);
    Q:=HorizontalJoin(ZeroMatrix(Integers(), Dimension(Pic), q), M);
    return  hom<Pic -> DivisorClassGroup(X) | RowSequence(M)>;
end intrinsic;

intrinsic DivisorClassGroup(X::TorVar) -> ModED
{The divisor class group of X, i.e. the group of Weil divisors modulo linear equivalence}
    require IsField(BaseRing(X)): "Base ring must be a field";
    return DivisorClassGroup(CoxRing(X));
end intrinsic;
