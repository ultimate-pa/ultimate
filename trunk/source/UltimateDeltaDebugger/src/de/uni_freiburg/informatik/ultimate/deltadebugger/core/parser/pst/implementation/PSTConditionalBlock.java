package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTConditionalBlock extends PSTNode implements IPSTConditionalBlock {	
	protected final List<IPSTDirective> conditionalDirectives;
	protected final ISourceRange activeBranchLocation;
	
	public PSTConditionalBlock(ISourceDocument source, ISourceRange location, List<IPSTDirective> conditionalDirectives, ISourceRange activeBranchLocation) {
		super(source, location, null);
		this.conditionalDirectives = Objects.requireNonNull(conditionalDirectives);
		this.activeBranchLocation = activeBranchLocation;
	}

	@Override
	public boolean hasActiveBranch() {
		return activeBranchLocation != null;
	}

	@Override
	public ISourceRange getActiveBranchLocation() {
		if (activeBranchLocation != null) {
			return activeBranchLocation;
		}
		return source.newSourceRange(offset(), offset());
	}
	
	@Override
	public List<IPSTDirective> getConditionalDirectives() {
		return conditionalDirectives;
	}

	@Override
	int dispatchVisit(IPSTVisitor action) {
		return action.visit(this);
	}
	
	@Override
	int dispatchLeave(IPSTVisitor action) {
		return action.leave(this);
	}
	
}

