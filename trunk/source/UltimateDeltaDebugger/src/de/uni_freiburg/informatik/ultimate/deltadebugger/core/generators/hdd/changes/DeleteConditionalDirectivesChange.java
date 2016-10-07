package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public class DeleteConditionalDirectivesChange extends Change {
	private final ISourceRange[] deleteLocations;
	
	public DeleteConditionalDirectivesChange(IPSTConditionalBlock block) {
		super(block);
		if (!block.hasActiveBranch()) {
			deleteLocations = null;
			return;
		}
		deleteLocations = new ISourceRange[2];
		final ISourceRange activeBranchLocation = block.getActiveBranchLocation();
		deleteLocations[0] = block.getSource().newSourceRange(block.offset(), activeBranchLocation.offset());
		deleteLocations[1] = block.getSource().newSourceRange(activeBranchLocation.endOffset(), block.endOffset());
	}

	@Override
	public void apply(SourceRewriter rewriter) {
		if (deleteLocations == null) {
			rewriter.delete(getNode());
		} else {
			rewriter.delete(deleteLocations[0]);
			rewriter.delete(deleteLocations[1]);
		}
	}

	@Override
	public String toString() {
		return "Delete conditional directives " + getNode()
				+ (deleteLocations != null ? " (deleting " + deleteLocations[0] + " and " + deleteLocations[1] + ")" : "");
	}
}