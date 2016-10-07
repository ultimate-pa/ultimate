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
	
	public PSTPrintVisitor(boolean visitLiteralRegionContents) {
		this.visitLiteralRegions = visitLiteralRegionContents;
	}	
	
	void printNode(IPSTNode node) {	
		for (int i = 0; i < depth; i++) {
			System.out.print("|   ");
		}
		System.out.println(node);
	}
	
	@Override
	public int defaultVisit(IPSTNode node) {
		if (!visitLiteralRegions && node.getParent() instanceof IPSTLiteralRegion) {
			return PROCESS_SKIP;
		}
		
		printNode(node);
		++depth;
		return PROCESS_CONTINUE;
	}

	@Override
	public int defaultLeave(IPSTNode node) {
		--depth;
		return PROCESS_CONTINUE;
	}
	
	@Override
	public int visit(IPSTLiteralRegion literalRegion) {
		return defaultVisit(literalRegion);
	}
	
	@Override
	public int leave(IPSTLiteralRegion literalRegion) {
		return defaultLeave(literalRegion);
	}
}
