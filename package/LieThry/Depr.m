freeze;

/*
**  $Id: Depr.m 22947 2009-09-16 02:52:13Z murray $
**
**  This file contains deprecated functions, which are kept for one major release of Magma
**
**
**
**
*/

import "GrpCox.m" : groupToRootSystem;


declare verbose LieThryDepr, 1;
SetVerbose("LieThryDepr", 1); 


/*
**
**  Deprecated since 2.13  --  To be removed in 2.14
**


intrinsic RootSubdatum( R::RootDtm, simples::SeqEnum ) -> RootDtm, .
{}
    vprint LieThryDepr,1 : 
        "The function RootSubdatum is deprecated and will be removed in the next\n" *
        "major release of Magma. Use the sub constructor sub<R|...> instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
    return sub<R|simples>;
end intrinsic;

intrinsic RootSubsystem( R::RootSys, simples::SeqEnum ) -> RootSys, .
{}
    vprint LieThryDepr,1 : 
        "The function RootSubsystem is deprecated and will be removed in the next\n" *
        "major release of Magma. Use the sub constructor sub<R|...> instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
    return sub<R|simples>;
end intrinsic;

intrinsic RootSubdatum(R::RootDtm, gens::SetEnum ) -> RootDtm, .
{}
    vprint LieThryDepr,1 : 
        "The function RootSubdatum is deprecated and will be removed in the next\n" *
        "major release of Magma. Use the sub constructor sub<R|...> instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
    return sub<R|gens>;
end intrinsic;

intrinsic RootSubsystem(R::RootSys, gens::SetEnum ) -> RootSys, .
{Deprecated. Use sub<R|...> instead}
    vprint LieThryDepr,1 : 
        "The function RootSubsystem is deprecated and will be removed in the next\n" *
        "major release of Magma. Use the sub constructor sub<R|...> instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
    return sub<R|gens>;
end intrinsic;

intrinsic RootSubdatum( R::RootDtm, U::ModTupFld, V::ModTupFld ) -> RootDtm, .
{Deprecated. Use sub<R|...> instead}
    vprint LieThryDepr,1 : 
        "The function RootSubdatum is deprecated and will be removed in the next\n" *
        "major release of Magma. Use the sub constructor sub<R|...> instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
    return sub<R|U,V>;
end intrinsic;

intrinsic HasExtraspecialSigns( R::RootDtm ) -> BoolElt
{deprecated}
    vprint LieThryDepr,1 : 
        "The function ``HasExtraspecialSigns'' is deprecated and will be removed in the \n" *
        "next major release of Magma.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
    return true;
end intrinsic;

intrinsic SetExtraspecialSigns( ~R::RootDtm, signs::RngIntElt )
{deprecated}
// dont use vprint, since SetExtraspecialSigns has no effect at all now.
// and the user must not ignore this warning.
    // vprint LieThryDepr,1 : 
    print 
        "The function ``SetExtraspecialSigns'' is deprecated and has no effect.\n" *
        "It will be removed in the next major release of Magma.\n" *
        "Use the optional parameter ``Signs'' when creating a root datum instead.";
    //  "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
end intrinsic;

intrinsic SetExtraspecialSigns( ~R::RootDtm, signs::SeqEnum[RngIntElt] )
{deprecated}
// dont use vprint, since SetExtraspecialSigns has no effect at all now.
// and the user must not ignore this warning.
    // vprint LieThryDepr,1 : 
    print 
        "The function ``SetExtraspecialSigns'' is deprecated and has no effect.\n" *
        "It will be removed in the next major release of Magma.\n" *
        "Use the optional parameter ``Signs'' when creating a root datum instead.";
end intrinsic;

intrinsic SetNormalising( ~G::GrpLie, Normalising::BoolElt )
{deprecated}
// dont use vprint, since SetNormalising has no effect at all now.
// and the user must not ignore this warning.
    // vprint LieThryDepr,1 : 
    print 
        "The function ``SetNormalising'' is deprecated and has no effect.\n" *
        "It will be removed in the next major release of Magma.\n" *
        "Use the optional parameter ``Normalising'' when creating a group of Lie type.";
end intrinsic;
*/


intrinsic SemiSimpleType( L::AlgLie ) -> MonStgElt
{deprecated}
    vprint LieThryDepr,1 : 
        "The function ``SemiSimpleType'' is deprecated and will be removed in the next\n" *
        "major release of Magma. Use ``SemisimpleType'' instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
    return SemisimpleType( L );
end intrinsic;

intrinsic PthPowerMapping( L::AlgLie ) -> Map
{deprecated}
    vprint LieThryDepr,1 : 
        "The function ``PthPowerMapping'' is deprecated and will be removed in the next\n" *
        "major release of Magma. Use ``pMap'' instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
    return pMap( L );
end intrinsic;





intrinsic DirectSum( W1::GrpPermCox, W2::GrpPermCox ) -> GrpPermCox
{The direct sum of W1 and W2}
    vprint LieThryDepr,1 : 
        "The function ``DirectSum'' is deprecated and will be removed in the next\n" *
        "major release of Magma. Use ``DirectProduct'' instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
  R := DirectSum( groupToRootSystem( W1 ), groupToRootSystem( W2 ) );
  return CoxeterGroup( R );
end intrinsic;

intrinsic DirectSum( W1::GrpFPCox, W2::GrpFPCox ) -> GrpFPCox
{The direct sum of W1 and W2}
    vprint LieThryDepr,1 : 
        "The function ``DirectSum'' is deprecated and will be removed in the next\n" *
        "major release of Magma. Use ``DirectProduct'' instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
  return CoxeterGroup( GrpFPCox, 
    CoxeterGraph( W1 ) join CoxeterGraph( W2 ) );
end intrinsic;

intrinsic IsIrreducible( G::GrpLie ) -> BoolElt
{True iff G is irreducible}
    vprint LieThryDepr,1 : 
        "The function ``IsIrreducible'' is deprecated and will be removed in the next\n" *
        "major release of Magma. Use ``IsSimple'' instead.\n" *
        "This message can be turned off by using ``SetVerbose(\"LieThryDepr\", 0);''.";
  return IsIrreducible( RootDatum(G) );
end intrinsic;


