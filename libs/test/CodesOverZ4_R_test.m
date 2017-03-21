/************************************************************/
/*                                                          */
/* Project name: Codes over Z4 in MAGMA                     */
/* Regression test file name: CodesOverZ4_R_test.m          */
/*                                                          */
/* Comments:                                                */
/*                                                          */
/* Authors: R. D. Barrolleta, J. Pujol and M. Villanueva    */
/*                                                          */
/* Revision version and last date: 1.0  2016/02/20          */
/*                                                          */
/************************************************************/

SetAssertions(true);
Alarm(30*60);
SetQuitOnError(false);

/************************************************************/
/*                                                          */
/* BLACK-BOX TESTS                                          */
/*                                                          */
/************************************************************/
load "testCodesOverZ4.m";
load "testDecodeOverZ4_part1.m";
load "testDecodeOverZ4_part2.m";

load "testPermDecodeOverFq.m";




