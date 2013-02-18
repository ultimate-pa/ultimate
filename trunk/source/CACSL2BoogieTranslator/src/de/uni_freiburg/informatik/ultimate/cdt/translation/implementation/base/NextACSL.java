/**
 * Container for a list of ACSL nodes and one C node.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayList;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 28.02.2012
 */
public class NextACSL {
	/**
	 * a list of ACSL comments to hold.
	 */
	public ArrayList<ACSLNode> acsl;
	/**
	 * The successor C node as reference, where the ACSL is contained in the
	 * translation unit.
	 */
	public IASTNode successorCNode;

	/**
	 * Constructor.
	 * 
	 * @param acsl
	 *            a list of ACSL comments to hold.
	 * @param successorCNode
	 *            the successor C node as reference, where the ACSL is contained
	 *            in the translation unit.
	 */
	public NextACSL(ArrayList<ACSLNode> acsl, IASTNode successorCNode) {
		assert acsl != null;
		this.acsl = acsl;
		this.successorCNode = successorCNode;
	}
}
