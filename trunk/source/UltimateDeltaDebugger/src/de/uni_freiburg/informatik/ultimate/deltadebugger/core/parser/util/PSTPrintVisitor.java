package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

public class PSTPrintVisitor implements IPSTVisitor {
	final boolean visitLiteralRegions;
	int depth = 0;

	public PSTPrintVisitor() {
		this(false);
	}

	public PSTPrintVisitor(final boolean visitLiteralRegionContents) {
		visitLiteralRegions = visitLiteralRegionContents;
	}

	@Override
	public int defaultLeave(final IPSTNode node) {
		--depth;
		return PROCESS_CONTINUE;
	}

	@Override
	public int defaultVisit(final IPSTNode node) {
		if (!visitLiteralRegions && node.getParent() instanceof IPSTLiteralRegion) {
			return PROCESS_SKIP;
		}

		printNode(node);
		++depth;
		return PROCESS_CONTINUE;
	}

	@Override
	public int leave(final IPSTLiteralRegion literalRegion) {
		return defaultLeave(literalRegion);
	}

	void printNode(final IPSTNode node) {
		for (int i = 0; i < depth; i++) {
			System.out.print("|   ");
		}
		System.out.println(node);
	}

	@Override
	public int visit(final IPSTLiteralRegion literalRegion) {
		return defaultVisit(literalRegion);
	}
}
