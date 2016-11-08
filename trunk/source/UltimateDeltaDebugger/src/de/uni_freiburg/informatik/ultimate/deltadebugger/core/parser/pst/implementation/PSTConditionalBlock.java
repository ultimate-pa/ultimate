package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTConditionalBlock extends PSTNode implements IPSTConditionalBlock {
	protected final List<IPSTDirective> mConditionalDirectives;
	protected final ISourceRange mActiveBranchLocation;

	public PSTConditionalBlock(final ISourceDocument source, final ISourceRange location,
			final List<IPSTDirective> conditionalDirectives, final ISourceRange activeBranchLocation) {
		super(source, location, null);
		mConditionalDirectives = Objects.requireNonNull(conditionalDirectives);
		mActiveBranchLocation = activeBranchLocation;
	}

	@Override
	int dispatchLeave(final IPSTVisitor action) {
		return action.leave(this);
	}

	@Override
	int dispatchVisit(final IPSTVisitor action) {
		return action.visit(this);
	}

	@Override
	public ISourceRange getActiveBranchLocation() {
		if (mActiveBranchLocation != null) {
			return mActiveBranchLocation;
		}
		return mSource.newSourceRange(offset(), offset());
	}

	@Override
	public List<IPSTDirective> getConditionalDirectives() {
		return mConditionalDirectives;
	}

	@Override
	public boolean hasActiveBranch() {
		return mActiveBranchLocation != null;
	}

}
