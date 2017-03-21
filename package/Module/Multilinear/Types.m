freeze;

/*
  This file contains all the definitions of all the new types and attributes 
  of the Multilinear package.
*/


// ------------------------------------------------------------------------------
//                             Tensor space categories.
// ------------------------------------------------------------------------------
declare type TenCat; 	
declare attributes TenCat : Arrows, Contra, Repeats, Valence;

/*
  Description of attributes:
    Arrows. . . . . . . . . . The function from Repeats to {-1,0,1} detailing which spaces are dualized.
    Contra. . . . . . . . . . True/false whether the category is contravariant.
    Repeats . . . . . . . . . A partition of {0..v}.
    Valence . . . . . . . . . The valence v.
*/

// ------------------------------------------------------------------------------
//                                  Tensor Space
// ------------------------------------------------------------------------------
declare type TenSpc[TenSpcElt]; // eventually inherit ModRng structure
declare attributes TenSpc : Cat, Frame, Mod, Ring, UniMap, Valence;

/* 
  Description of attributes:
    Cat. . . . . . . . . . The category of the tensor space tensors.
    Frame. . . . . . . . . The sequence of the modules in the frame.
    Mod. . . . . . . . . . The R-module T.
    Ring . . . . . . . . . The base ring.
    UniMap . . . . . . . . The universal map; either into the space of multimaps or from the tensor product.
    Valence. . . . . . . . The valence of the space.
*/

// ------------------------------------------------------------------------------
//                                     Tensor
// ------------------------------------------------------------------------------
declare attributes TenSpcElt : Adjoint, Bimap, Cat, Centroids, Codomain, Coerce, CoordImages, Derivations, Domain, Element, FullyNondeg, 
Image, Map, Nondegenerate, Nuclei, Parent, Permutation, Radicals, Reflexive, Valence;

/* 
  Tensors will be thought of as multimaps but will be allowed flexibility for the user.

  Description of attributes:
    Adjoint. . . . . . . . The adjoint *-algebra of the bimap. Only used when valence is 2 and is Hermitian.
    Bimap. . . . . . . . . The record of bimap info. Only defined when the valence is 2.
    Centroids. . . . . . . The list of centroids sorted by subsets of {1..v} of order at least 2.
    Cat . . . . . . . . .  The tensor category.
    Codomain . . . . . . . The codomain of the tensor.
    Coerce . . . . . . . . If the multimap is created from some algebraic object, this will contain maps to the modules.
    CoordImages. . . . . . The sequence of images of the coordinates.
    Derivations. . . . . . The associated Lie algebra of derivations.
    Domain . . . . . . . . A list of the modules in the domain.
    Element. . . . . . . . The corresponding element in the tensor space.
    FullyNondeg. . . . . . The fully nondegenerate tensor.
    Image. . . . . . . . . The image of the tensor.
    Map. . . . . . . . . . The map from the domain into the codomain.
    Nondegenerate. . . . . A tuple containing the nondegenerate multimap and a homotopism to get there.
    Nuclei . . . . . . . . A list of spaces sorted by the subsets of {0..v} of order 2.
    Parent . . . . . . . . A tensor space which contains the tensor.
    Permutation. . . . . . Used for shuffling tensors. Allows for on-the-fly computations; defaults is Sym({1..v+1})!1.
    Radicals . . . . . . . A list of the radicals for each Cartesian factor in the domain and the coradical.
    Reflexive. . . . . . . A record which states if the tensor is reflexive.
    Valence. . . . . . . . The number of modules involved - 1.
*/

// ------------------------------------------------------------------------------
//                                   Homotopism
// ------------------------------------------------------------------------------
declare type Hmtp;
declare attributes Hmtp : Cat, Codomain, Domain, Kernel, Maps;

/* 
  Description of attributes:
    Cat. . . . . . . . . . The tensor category.
    Codomain . . . . . . . The tensor it maps into.
    Domain . . . . . . . . The tensor in the domain.
    Kernel . . . . . . . . The kernel of the homotopism.
    Maps . . . . . . . . . The list of maps from the spaces in the domain to the spaces in the codomain.
                           Vn x ... x V1 >-> V0
                           |          |      |
                           Un x ... x U1 >-> U0 
                           The maps go in order from left to right.
*/

// ------------------------------------------------------------------------------
//                                  Bimap Spaces
// ------------------------------------------------------------------------------
declare type BmpU[BmpUElt];
declare type BmpV[BmpVElt];

declare attributes BmpU : Parent, Space;
declare attributes BmpV : Parent, Space;

/*
  Description of attributes:
    Parent . . . . . . . . The parent bimap.
    Space. . . . . . . . . The vector space U or V.
*/

declare attributes BmpUElt : Element, Parent;
declare attributes BmpVElt : Element, Parent;

/*
  Description of attributes:
    Element. . . . . . . . The element from the vector space U or V.
    Parent . . . . . . . . The parent space BmpU or BmpV.
*/

// ------------------------------------------------------------------------------
//                                 New Attributes
// ------------------------------------------------------------------------------
declare attributes GrpMat : DerivedFrom;
declare attributes AlgMat : DerivedFrom;
declare attributes AlgMatLie : DerivedFrom;
declare attributes AlgGen : Star; 

/*
  Description of attributes:
    DerivedFrom. . . . . . A tuple containing the tensor it came from and the indices of the spaces.
    Star . . . . . . . . . An involution on the algebra.
*/
