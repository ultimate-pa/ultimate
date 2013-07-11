package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;


/**
 * Computes the integral hull of a polyhedron given by a set of linear
 * inequalities
 * 
 * Applying this preprocessor yields more solutions in cases with integer
 * variables
 */
public class IntegralHull {
	
	/**
	 * Computes the interal hull of a polyhedron given by a set of linear
	 * inequalities
	 * @param polyhedron list of inequalities defining the polyhedron
	 * @return additional inequalities
	 */
	public static Collection<LinearInequality>
			compute(Collection<LinearInequality> polyhedron) {
		
		// TODO
		
		throw new UnsupportedOperationException(
				"Integral hull is no yet implemented.");
	}
}
