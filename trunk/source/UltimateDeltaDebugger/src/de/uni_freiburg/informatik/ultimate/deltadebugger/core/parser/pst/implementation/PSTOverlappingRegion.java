package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTOverlappingRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTOverlappingRegion extends PSTNode implements IPSTOverlappingRegion {

	public PSTOverlappingRegion(ISourceDocument source, ISourceRange location) {
		super(source, location, null);
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
