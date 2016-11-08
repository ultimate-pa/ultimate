package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTGapVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;

/**
 * Utility class to invoke an IPSTGapVisitor on a given node
 */
public final class GapVisitor {

	private GapVisitor() {
	}
	
	public static boolean invokeAccept(final IPSTNode node, final IPSTGapVisitor action) {
		return node.accept(new GapVisitorDecorator(action, node.offset()));
	}
}

