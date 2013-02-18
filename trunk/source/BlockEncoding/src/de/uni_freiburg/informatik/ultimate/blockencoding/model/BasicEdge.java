/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Wrapper class for a normal edge, which exists in the RCFG.
 * 
 * @author Stefan Wissert
 * 
 */
public class BasicEdge extends
		ModifiableMultigraphEdge<MinimizedNode, IMinimizedEdge> implements
		IBasicEdge {

	/**
	 * Serial number, do not really use it.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * the underlying original edge (of type "CodeBlock")
	 */
	private CodeBlock originalEdge;


	public BasicEdge(CodeBlock originalEdge, MinimizedNode source,
			MinimizedNode target) {
		super(source, target);
		this.originalEdge = originalEdge;
	}

	@Override
	public boolean isBasicEdge() {
		return true;
	}

	@Override
	public CodeBlock getOriginalEdge() {
		return originalEdge;
	}

	@Override
	public String toString() {
		if (originalEdge instanceof GotoEdge) {
			return "goto";
		}
		return originalEdge.getPrettyPrintedStatements();
	}

	@Override
	public int getElementCount() {
		return 1;
	}

}
