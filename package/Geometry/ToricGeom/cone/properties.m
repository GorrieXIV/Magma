freeze;

////////////////////////////////////////////////////////////////////////
// properties.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 27125 $
// $Date: 2010-06-04 12:14:46 +1000 (Fri, 04 Jun 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating properties of cones.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// Contains intrinsics to answer questions: "is this simplcial?", "is this
// zero?", etc. Properties differ from attributes in the sense that I
// consider properties are true/false questions of the form
// "IsSomething(C)", whereas I regard attributes as answering questions
// such as: "what is the dimension?", "what is the linear span?".
/////////////////////////////////////////////////////////////////////////

import "generators.m": are_inequalities_minimal;

declare attributes TorCon:
    is_of_max_dim,          // Is C of maximal dimension?
    is_linear_space,        // Is C a linear space?
    is_simplicial;          // Is this cone simplicial?

/////////////////////////////////////////////////////////////////////////
// Local Functions
/////////////////////////////////////////////////////////////////////////

// Copies the data from "C" to "dC".
procedure properties_copy(C,dC)
    if assigned C`is_of_max_dim then
        dC`is_of_max_dim:=C`is_of_max_dim; end if;
    if assigned C`is_linear_space then
        dC`is_linear_space:=C`is_linear_space; end if;
    if assigned C`is_simplicial then
        dC`is_simplicial:=C`is_simplicial; end if;
end procedure;

// Sets the data of "dC" equal to minus "C".
procedure properties_minus(C,dC)
    if assigned C`is_of_max_dim then
        dC`is_of_max_dim:=C`is_of_max_dim; end if;
    if assigned C`is_linear_space then
        dC`is_linear_space:=C`is_linear_space; end if;
    if assigned C`is_simplicial then
        dC`is_simplicial:=C`is_simplicial; end if;
end procedure;

// Sets the data of "dC" equal to "C", but with the ambient changed to "L".
procedure properties_change_ambient(C,dC,L)
    if assigned C`is_of_max_dim then
        dC`is_of_max_dim:=C`is_of_max_dim; end if;
    if assigned C`is_linear_space then
        dC`is_linear_space:=C`is_linear_space; end if;
    if assigned C`is_simplicial then
        dC`is_simplicial:=C`is_simplicial; end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic IsZero(C::TorCon)-> BoolElt
{True iff the cone C is supported at the origin}
    return Dimension(C) eq 0;
end intrinsic;

intrinsic IsSimplicial(C::TorCon) -> BoolElt
{True iff the cone C is simplicial (i.e. iff the corresponding affine variety is Q-factorial)}
    if not assigned C`is_simplicial then 
        C`is_simplicial:=#MinimalRGenerators(C) eq Dimension(C);
    end if;
    return C`is_simplicial; 
end intrinsic;

intrinsic IsStrictlyConvex(C::TorCon) -> BoolElt
{True iff the cone C is strictly convex (i.e. iff there exists a hyperplane H such that C is contained on one side of H and C meets H in single point 0)}
    return IsMaximumDimensional(Dual(C));
end intrinsic;

intrinsic IsMaximumDimensional(C::TorCon) -> BoolElt
{True iff the cone C has dimension equal to that of its ambient lattice}
    if not assigned C`is_of_max_dim then 
        if are_inequalities_minimal(C) and IsSimplicial(Dual(C)) then 
            C`dim:=Dimension(Ambient(C));
            C`is_of_max_dim:= true;
        else
            C`is_of_max_dim:= Dimension(C) eq Dimension(Ambient(C));
        end if;
    end if;
    return C`is_of_max_dim;
end intrinsic;

intrinsic IsLinearSpace(C::TorCon) -> BoolElt
{True iff the cone C is a linear space}
    if not assigned C`is_linear_space then 
        if assigned C`dual and assigned C`dual`is_linear_space then 
            C`is_linear_space:=C`dual`is_linear_space;
        else
            C`is_linear_space:= -&+RGenerators(C) in C;
        end if;
    end if;
    return C`is_linear_space;  
end intrinsic;
