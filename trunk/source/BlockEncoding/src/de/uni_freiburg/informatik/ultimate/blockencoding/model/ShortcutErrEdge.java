/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;

/**
 * To mark so called shortcuts to error locations (which means we have more
 * calls than returns) we use this class which basically extends the normal
 * Conjunction. While converting it to an RCFG we have to treat them separately.
 * 
 * @author Stefan Wissert
 * 
 */
public class ShortcutErrEdge extends ConjunctionEdge {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param left
	 * @param right
	 */
	public ShortcutErrEdge(IMinimizedEdge left, IMinimizedEdge right) {
		super(left, right);
	}

}
