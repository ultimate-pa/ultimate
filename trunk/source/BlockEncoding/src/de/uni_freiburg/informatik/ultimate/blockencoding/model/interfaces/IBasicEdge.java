/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Such edges map to the original RCFG.
 * 
 * @author Stefan Wissert
 *
 */
public interface IBasicEdge extends IMinimizedEdge{
	
	/**
	 * Returns the underlying original edge (from the RCFG).
	 * 
	 * @return original edge (which is a "CodeBlock")
	 */
	public CodeBlock getOriginalEdge();

}
