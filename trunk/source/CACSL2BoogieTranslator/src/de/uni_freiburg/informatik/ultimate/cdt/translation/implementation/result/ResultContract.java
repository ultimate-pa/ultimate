/**
 * Holds a specification array.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.03.2012
 */
public class ResultContract extends Result {
	/**
	 * Specifications.
	 */
	public Specification[] specs;

	/**
	 * Constructor.
	 * 
	 * @param specs a specification array.
	 */
	public ResultContract(Specification[] specs) {
		super(null);
		this.specs = specs;
	}
}
