//#Safe
/*
 * Example that we used in the following paper.
 * 2013CAV - Heizmann,Hoenicke,Podelski - Software Model Checking for People Who Love Automata
 * 
 * This example is motivated by a programs with pointers the was used in the
 * following publications which are related to the Goanna tool.
 * 
 * 2013ISSE - Ansgar Fehnker, Ralf Huuck - Model Checking Driven Static Analysis for the Real World
 * (Journal of Innovations in Systems and Software Engineering Springer-Verlag, doi:10.1007/s11334-012-0192-5, pages 1-12, August 2012.)
 * 2012ICFEM -  Maximilian Junker, Ralf Huuck, Ansgar Fehnker, Alexander Knapp -  SMT-Based False Positive Elimination in Static Program Analysis
 * 2012TAPAS -  Mark Bradley, Franck Cassez, Ansgar Fehnker, Thomas Given-Wilson, Ralf Huuck -  High Performance Static Analysis for Industry
 * 
 * 
 * Date: November 2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */


procedure main()
{
  var n, p: int;

  assume p != 0;
  while (n >= 0) {
    assert(p != 0);
    if (n == 0) {
      p := 0;
    }
    n := n - 1;
  } 
}