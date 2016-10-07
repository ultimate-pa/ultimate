package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.Objects;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * A child node in a comma separated list together with the location of the next comma (if known).
 */
public class CommaSeparatedChild {

	private final IASTNode astNode;
	private final IPSTRegularNode node;
	ISourceRange nextCommaLocation = null;

	/**
	 * @param astNode
	 *            the child node in the AST
	 * @param node
	 *            the corresponding regular PST node if existing
	 */
	public CommaSeparatedChild(final IASTNode astNode, final IPSTRegularNode node) {
		this.astNode = Objects.requireNonNull(astNode);
		this.node = node;
	}

	/**
	 * @return IASTNode (not null)
	 */
	public IASTNode astNode() {
		return astNode;
	}

	/**
	 * @return location of the first comma encountered after the child node. null of co comma was found.
	 */
	public ISourceRange nextCommaLocation() {
		return nextCommaLocation;
	}

	/**
	 * @return regular PST node corresponding to the IASTNode if it exists (null otherwise)
	 */
	public IPSTRegularNode node() {
		return node;
	}

	@Override
	public String toString() {
		return "CommaSeparatedChild [astNode=" + astNode + ", node=" + node + ", nextCommaLocation=" + nextCommaLocation
				+ "]";
	}
}