package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * A conditional block groups nodes within a conditional preprocessor region, i.e. the source text enclosed in
 * #if/#else/#endif directives. Only nodes in the active branch are children of this node.
 */
public interface IPSTConditionalBlock extends IPSTNode {
	ISourceRange getActiveBranchLocation();

	@Override
	default IASTNode getASTNode() {
		return null;
	}

	List<IPSTDirective> getConditionalDirectives();

	boolean hasActiveBranch();
}