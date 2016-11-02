package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTGapVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;

/**
 * Utility class to collect information about all comma separated children and the corresponding comma locations.
 *
 * Implementation notes: By checking the "gaps" in the PST we can easily find tokens between nodes without preprocessing
 * the source text. Only requirement is that all preprocessor directives and comments actually exist in the PST.
 */
public class CommaSeparatedChildFinder {

	private static class Visitor implements IPSTGapVisitor {
		private final IPSTRegularNode parentNode;
		private final ASTNodeProperty childProperty;
		private final List<CommaSeparatedChild> result = new ArrayList<>();

		private Visitor(final IPSTRegularNode parentNode, final ASTNodeProperty childProperty) {
			this.parentNode = Objects.requireNonNull(parentNode);
			this.childProperty = Objects.requireNonNull(childProperty);
		}

		@Override
		public int defaultLeave(final IPSTNode node) {
			for (final IASTNode child : node.getUnexpandedChildNodes()) {
				if (child.getPropertyInParent() == childProperty) {
					result.add(new CommaSeparatedChild(child, null));
				}
			}
			return PROCESS_CONTINUE;
		}

		@Override
		public int visit(final IPSTLiteralRegion literalRegion) {
			// Also add ast nodes from literal regions (but don't collect commas)
			defaultLeave(literalRegion);
			return PROCESS_SKIP;
		}

		@Override
		public int visit(final IPSTRegularNode node) {
			if (node == parentNode) {
				return PROCESS_CONTINUE;
			}
			if (node.getASTNode().getPropertyInParent() == childProperty) {
				result.add(new CommaSeparatedChild(node.getASTNode(), node));
			}
			return PROCESS_SKIP;
		}

		@Override
		public int visitGap(final int offset, final int endOffset) {
			final String text = parentNode.getSource().getText(offset, endOffset);
			if (!text.trim().startsWith(",")) {
				return PROCESS_CONTINUE;
			}

			// Store the position of the first comma encountered after each
			// element
			if (!result.isEmpty()) {
				final CommaSeparatedChild previousElement = result.get(result.size() - 1);
				if (previousElement.mNextCommaLocation == null) {
					final int commaOffset = offset + text.indexOf(',');
					previousElement.mNextCommaLocation =
							parentNode.getSource().newSourceRange(commaOffset, commaOffset + 1);
				}
			}
			return PROCESS_CONTINUE;
		}

	}

	/**
	 * @param parentNode
	 *            parent node that may have comma separated children
	 * @param childProperty
	 *            property to identify the child nodes
	 * @return sorted list of all child nodes with comma location
	 */
	public static List<CommaSeparatedChild> run(final IPSTRegularNode parentNode, final ASTNodeProperty childProperty) {
		final CommaSeparatedChildFinder.Visitor instance = new Visitor(parentNode, childProperty);
		GapVisitor.invokeAccept(parentNode, instance);
		return instance.result;
	}

	private CommaSeparatedChildFinder() {
	}
}
