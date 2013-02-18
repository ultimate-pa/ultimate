/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.03.2012
 */
public class ResultExpressionList extends Result {
	/**
	 * The list holding the single elements.
	 */
	public final ArrayList<ResultExpression> list;
	
	/**
	 * The Constructor.
	 */
	public ResultExpressionList() {
		super(null);
		this.list = new ArrayList<ResultExpression>();
	}
}
