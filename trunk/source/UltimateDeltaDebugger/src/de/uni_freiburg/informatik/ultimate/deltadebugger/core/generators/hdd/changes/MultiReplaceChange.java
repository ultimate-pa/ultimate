package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by replacing a node with one of multiple alternatives.
 */
public class MultiReplaceChange extends Change {
	private final List<String> mReplacements;
	
	MultiReplaceChange(final IPSTNode node, final List<String> replacements) {
		super(node);
		if (replacements.isEmpty()) {
			throw new IllegalArgumentException("missing list of replacements");
		}
		mReplacements = replacements;
	}
	
	@Override
	public void apply(final SourceRewriter rewriter) {
		rewriter.replace(getNode(), mReplacements.get(0));
	}
	

	@Override
	public Optional<Change> createAlternativeChange() {
		if (mReplacements.size() > 1) {
			return Optional.of(new MultiReplaceChange(getNode(), mReplacements.subList(1, mReplacements.size())));
		}
		return Optional.empty();
	}

	
	@Override
	public String toString() {
		return "Replace " + getNode() + " (by one of ["
				+ mReplacements.stream().map(s -> "\"" + s + "\"").collect(Collectors.joining(", ")) + "])";
	}
}
