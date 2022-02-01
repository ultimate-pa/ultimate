package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

/**
 * Partial visitor implementation that remembers leading comments and macros of a node.
 */
abstract class LeadingNodeCollector implements IPSTVisitor {
	private List<IPSTMacroExpansion> mLeadingMacroExpansions = new ArrayList<>();
	private IPSTACSLComment mLeadingACSLComment;

	protected abstract int visitRegular(final IPSTRegularNode node);

	protected IPSTACSLComment getLeadingACSLComment() {
		return mLeadingACSLComment;
	}

	protected List<IPSTMacroExpansion> getLeadingMacroExpansions() {
		return new ArrayList<>(mLeadingMacroExpansions);
	}

	protected List<IPSTMacroExpansion> getFilteredLeadingMacroExpansions(boolean includeEmpty,
			boolean includeExtension) {
		return mLeadingMacroExpansions.stream().filter(expansion -> {
			if (includeExtension && "__extension__".equals(expansion.getAstNode().getMacroReference().toString())) {
				return true;
			}
			return includeEmpty && expansion.getAstNode().getMacroDefinition().getExpansion().isEmpty();
		}).collect(Collectors.toList());
	}

	@Override
	public int visit(IPSTMacroExpansion expansion) {
		mLeadingMacroExpansions.add(expansion);
		return PROCESS_SKIP;
	}

	@Override
	public int visit(IPSTACSLComment acslComment) {
		mLeadingACSLComment = acslComment;
		return PROCESS_SKIP;
	}

	@Override
	public int visit(final IPSTRegularNode node) {
		final int res = visitRegular(node);
		mLeadingACSLComment = null;
		mLeadingMacroExpansions.clear();
		return res;
	}

	@Override
	public int defaultLeave(final IPSTNode node) {
		mLeadingACSLComment = null;
		mLeadingMacroExpansions.clear();
		return PROCESS_CONTINUE;
	}
}
