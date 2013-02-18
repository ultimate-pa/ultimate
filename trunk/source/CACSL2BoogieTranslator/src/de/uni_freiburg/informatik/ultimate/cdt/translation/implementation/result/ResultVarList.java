/**
 * A Result node holding a variable list array.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public class ResultVarList extends Result {
	/**
	 * Hold the VarList array.
	 */
	public VarList[] varList;

	/**
	 * Constructor.
	 * 
	 * @param varList
	 *            the variable list to hold
	 */
	public ResultVarList(VarList[] varList) {
		super(null);
		this.varList = varList;
	}
}
