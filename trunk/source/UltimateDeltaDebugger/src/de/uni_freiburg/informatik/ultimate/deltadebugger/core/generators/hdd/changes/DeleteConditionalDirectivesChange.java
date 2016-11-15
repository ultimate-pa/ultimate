package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by conditional directives deletion.
 */
public class DeleteConditionalDirectivesChange extends Change {
	private final ISourceRange[] mDeleteLocations;
	
	/**
	 * @param block
	 *            PST block.
	 */
	public DeleteConditionalDirectivesChange(final IPSTConditionalBlock block) {
		super(block);
		if (!block.hasActiveBranch()) {
			mDeleteLocations = null;
			return;
		}
		mDeleteLocations = new ISourceRange[2];
		final ISourceRange activeBranchLocation = block.getActiveBranchLocation();
		mDeleteLocations[0] = block.getSource().newSourceRange(block.offset(), activeBranchLocation.offset());
		mDeleteLocations[1] = block.getSource().newSourceRange(activeBranchLocation.endOffset(), block.endOffset());
	}
	
	@Override
	public void apply(final SourceRewriter rewriter) {
		if (mDeleteLocations == null) {
			rewriter.delete(getNode());
		} else {
			rewriter.delete(mDeleteLocations[0]);
			rewriter.delete(mDeleteLocations[1]);
		}
	}
	
	@Override
	public String toString() {
		return "Delete conditional directives " + getNode() + (mDeleteLocations != null
				? (" (deleting " + mDeleteLocations[0] + " and " + mDeleteLocations[1] + ")")
				: "");
	}
}
