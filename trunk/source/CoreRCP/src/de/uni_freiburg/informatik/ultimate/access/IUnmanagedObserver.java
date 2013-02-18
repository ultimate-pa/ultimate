package de.uni_freiburg.informatik.ultimate.access;

import de.uni_freiburg.informatik.ultimate.model.IElement;
/**
 * 
 * This class provides unmanaged access to the data structures of Ultimate. 
 * 
 * @author dietsch
 *
 */
public interface IUnmanagedObserver extends IObserver {
	
	/**
	 * Supplies a INode of a selected structure in the order determined by
	 * getWalkerOptions(). The return value determines if the walker continues
	 * to expand all the children of the given INode or not. You are free to
	 * change the supplied data structure but keep in mind that you have to obey
	 * the structural invariants of the model. Ultimate currently does not check
	 * those invariants and any break in them could cause non-termination or
	 * undesired behavior of other tools
	 * 
	 * @param root
	 *            The instance of INode which represents the root of the current
	 *            subgraph or subtree.
	 * @return true if the walker should descent to the children of the current
	 *         node, false if it should skip them.
	 */
	
	public abstract boolean process(IElement root);
}
