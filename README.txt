 
              =============================================
              The Magma Distribution: Information for Users
              =============================================

1. Introduction
---------------

This file summarises the important files of interest to all users that are
supplied as part of the Magma distribution. Your system manager will unpack
and install these files in some appropriate place as described in the
document "The Magma Distribution: Information for the System Manager"
(INSTALL.txt).


2. Magma Documentation
----------------------

The Magma documentation is contained within the doc subdirectory of the
Magma installation directory.  Please see the file doc/README.txt or
point your favourite web browser at doc/index.htm .

2.1 Summary
-----------

There are several components to the Magma documentation:-

  * A first steps overview ("First Steps in Magma")

  * A full reference manual ("Magma Handbook")
 
  * A set of examples of solving problems with Magma ("Solving Problems
    with Magma")

  * An internal Help system with a Browser
 
  * An HTML version of the Help system overview and the Magma Handbook
    (doc/html)

  * A low-level internal help facility for Categories and Intrinsics


2.2 Books and Manuals
---------------------

FIRST STEPS IN MAGMA: First Steps In Magma consists of a very terse
overview of how to start using Magma.  It is suitable for use in the
initial stages of learning the system [16 pages: FirstSteps.pdf]
 
MAGMA HANDBOOK: The Handbook is the complete reference manual for
Magma.  It provides a terse summary of the language and gives full
descriptions of the facilities provided for each of the mathematical
modules.  It constitutes the central reference manual for the system.
A large number of examples are included. These examples are listed
under a unique name in the Handbook and are included as one of the
libraries distributed with the system (see below).  This allows the
reader to run any example appearing in the Handbook by typing
   
        load "Name";
   
where "Name" is the name appearing at the head of the example in the
Handbook [over 4000 pages: Handbook.pdf]
 
SOLVING PROBLEMS WITH MAGMA: This book contains a varied collection of
annotated examples of the application of Magma to the solution of
non-trivial problems in a range of different areas. In many cases these
are polished versions of actual problems that have been solved by
mathematicians using Cayley or Magma [180 pages: SolvingProblems.pdf]
 
 
2.3 The On-line Help System
---------------------------
 
Information about the on-line help system in Magma may be obtained by
typing
 
?
 
at the Magma prompt.
 
 
2.4 The HTML Help
-----------------
 
The Magma HTML Help Document is contained in the directory doc/html
(unpacked from doc.tar).  To view it, move to the doc/html directory
and then type
 
        mozilla MAGMA.htm
or
        firefox MAGMA.htm
 
or similar, depending on your browser.  The file doc/index.htm has
a link pointing to this file.

 
2.5 Signature-based Help
------------------------
 
Terse help for functions and operators may be obtained within Magma
as follows:
 
   ListCategories();
 
will produce a list of all "category" names;
 
   ListSignatures(cat)
 
will list all operators and functions whose signatures involve the category
"cat";
 
   <intrinsic>;
  
will print all signatures for the intrinsic (function or procedure) having
name <intrinsic>, together with a synopsis of the semantics of the function.
For example, typing:
 
    Order;
 
will print all signatures for the intrinsic function 'Order' (note there
are no parentheses here).  See the Introduction or Handbook for full
details.
 
 
3. Magma Libraries
------------------
 
3.1 Introduction
----------------
 
A collection of files containing:
 
   * The examples appearing in the Introduction and Handbook in executable
     form;
 
   * Useful collections of finite groups.
        
In the past a number of other collections of objects (e.g., transitive
groups) have been exported in the form of libraries.  However, since V2.4
the more widely used libraries have been converted into standard
databases and are directly accessible through standard Magma intrinsics.
The libraries listed here may only be accessed by first explicitly
loading them. Full information concerning their contents and use may be
obtained using the on-line help system.  For example, to obtain details
of the library of irreducible soluble groups, type
 
?isolgps
 
The available libraries in V2.20 are as follows:
 
 
3.2 Examples from the Handbook
------------------------------
 
File:   examples
 
        This library consists of all the examples in the Handbook.  Each
        example is of the form H<chapter>E<name> where <chapter> is the name
        of the chapter and <name> is the name used for the specific example
        in that chapter.
 
3.3 Examples from the Introduction
----------------------------------
 
File:   intro
 
	_An Introduction to Algebraic Programming with Magma_ is a book
	currently being revised and not distributed at the moment.  The
	examples from it are still available for the time being.

        This library consists of all the examples in the Introduction.  Each
        example is of the form I<chapter>E<name> where <chapter> is the name
        of the chapter and <name> is the name used for the specific example
        in that chapter.
 
3.4 Polynomials Realising Galois Groups
---------------------------------------
 
File:   galpols
 
        This database contains for each transitive group G with degree
        between 2 and 11, a univariate polynomial over the integers
        which has G as its Galois group.
 
 
3.5 Maximal Finite Subgroups of GL(n, Z)
----------------------------------------
 
File:  glnzgps
 
        This library contains the maximal finite subgroups of GL(n, Z) for
        n = 2, 3, 4, 5.  The groups are taken from the tables which appear in
        R. Buelow, "Ueber Dadegruppen in GL(5, Z)", Diss, RWTH Aachen 1973.
 
  
3.6 Irreducible Soluble Subgroups of GL(n, p)
---------------------------------------------
 
File:   isolgps
 
        A library of irreducible soluble subgroups of GL(n, p) for n > 1
        and p^n < 256 prepared by M. W. Short.
 
3.7 Matrix Groups
-----------------
        
File:   matgps
        
        This library contains various useful matrix groups, almost all
        over finite fields (the only exception is the Weyl group E6).
 
3.8 Permutation Groups
----------------------
 
File:   pergps
 
        This library contains permutation representations for various
        finite groups. A particular group is included either if
        (a) It is an 'interesting' group. In practice this means a
        simple group or a close relative of a simple group; or
        (b) It is representative of some class of groups which is
        useful for testing conjectures and algorithms.

3.9 Simple of Order Less Than a Million
----------------------------------------
        
File:   simgps
        
        This library contains presentations for all simple groups  of
        order less than a million. The library was prepared by Jamali,
        Robertson and Campbell.
 
3.10 Finite soluble Groups
--------------------------
 
File:   solgps
 
        This library contains pc-presentations of 13 soluble groups
        constructed by S.P. Glasby.
 
3.11 Database Files
-------------------
 
The directory also contains:
 
File:   data
 
        This a directory containing database files used within Magma.
        The directory should be left in the top of the libs/ directory.
 
 
5. Contacting the Magma Group
------------------------------
 
For all enquiries and problems please mail us at:
 
        magma@maths.usyd.edu.au



************************
* USE OF FREE SOFTWARE *
************************

		Third party libraries used by Magma

Depending on architecture, one or more of the following third party
libraries may be used by Magma, in accordance with any appropriate
licenses.

  * ATLAS	http://math-atlas.sourceforge.net/
  * GMP		http://www.swox.com/gmp/
  * GMP-ECM	http://www.komite.net/laurent/soft/ecm/ecm-6.0.1.html
  * MPC		http://www.lix.polytechnique.fr/Labo/Andreas.Enge/Mpc.html
  * MPFR	http://www.mpfr.org/

In each case the appropriate license is reproduced in the ThirdParty
subdirectory of the Magma installation directory.

Some of the above libraries use the GNU LGPL license.  To comply with
this license (point 6) we will provide to licensed Magma users on request
a shared-library version of Magma which will be linkable against future
versions of these libraries.  Please note that this is quite unnecessary
for current licensed Magma users, since all versions of Magma which use
these libraries will always be kept up to date with the latest version;
this offer is made simply to comply with the GNU LGPL license.

