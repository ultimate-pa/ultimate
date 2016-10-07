package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public class ReplaceChange extends Change {
	final String replacement;
	
	ReplaceChange(IPSTNode node, String replacement) {
		super(node);
		this.replacement = replacement;
	}

	@Override
	public void apply(SourceRewriter rewriter) {
		rewriter.replace(getNode(), replacement);
	}

	@Override
	public String toString() {
		return "Replace " + getNode() + " (by \"" + replacement + "\")";
	}
}