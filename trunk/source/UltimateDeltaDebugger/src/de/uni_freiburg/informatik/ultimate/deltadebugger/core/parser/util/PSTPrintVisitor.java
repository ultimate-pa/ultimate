package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

public class PSTPrintVisitor implements IPSTVisitor {
	private final Consumer<String> mPrinter;
	private final boolean mVisitLiteralRegions;
	private int mDepth;

	public PSTPrintVisitor(final Consumer<String> printer) {
		this(printer, false);
	}

	public PSTPrintVisitor(final Consumer<String> printer, final boolean visitLiteralRegionContents) {
		mPrinter = printer;
		mVisitLiteralRegions = visitLiteralRegionContents;
	}

	@Override
	public int defaultLeave(final IPSTNode node) {
		--mDepth;
		return PROCESS_CONTINUE;
	}

	@Override
	public int defaultVisit(final IPSTNode node) {
		if (!mVisitLiteralRegions && node.getParent() instanceof IPSTLiteralRegion) {
			return PROCESS_SKIP;
		}

		printNode(node);
		++mDepth;
		return PROCESS_CONTINUE;
	}

	@Override
	public int leave(final IPSTLiteralRegion literalRegion) {
		return defaultLeave(literalRegion);
	}

	void printNode(final IPSTNode node) {
		for (int i = 0; i < mDepth; i++) {
			mPrinter.accept("|   ");
		}
		mPrinter.accept(node.toString());
		mPrinter.accept(System.lineSeparator());
	}

	@Override
	public int visit(final IPSTLiteralRegion literalRegion) {
		return defaultVisit(literalRegion);
	}
}
