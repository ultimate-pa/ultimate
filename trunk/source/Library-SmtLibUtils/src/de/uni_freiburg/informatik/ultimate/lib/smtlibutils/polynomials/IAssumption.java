package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
*
* This represents an Assumption (possibly consisting of multiple sub-assumptions)
* for solvability of an {@link AbstractGeneralizedAffineRelation}.
*
* @author Leonard Fichtner (leonard.fichtner@web.de)
*
*/
public interface IAssumption {

	public Sort getSort();
	
	/**
	 * Get the representation of this Assumption, as a Term that is supported by the solver.
	 * Explicit here means the conjunction of all sub-assumptions.
	 * An example would be:
	 * "Part"-assumptions: x != 0,  y != 0
	 * Explicit form  x != 0 and y != 0
	 */
	public Term toExplicitTerm();
	
	/**
	 * Get the representation of this Assumption, as a Term that is supported by the solver.
	 * Contracted here means the sub-assumptions are synthesized, such that the returned term is 
	 * equivalent to the explicit (conjunction of all sub-assumptions) form.
	 * Some assumptions might not have a suitable contraction, in that case the explicit form is returned.
	 * An example would be:
	 * Assumptions so far  x != 0,  y != 0
	 * Contracted form  x*y != 0
	 */
	public Term toContractedTermIfPossible();
	
	public boolean hasContractedForm();
}
