/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

/**
 * A PST print visitor.
 */
public class PSTPrintVisitor implements IPSTVisitor {
	private final Consumer<String> mPrinter;
	private final boolean mVisitLiteralRegions;
	private int mDepth;
	
	/**
	 * @param printer
	 *            Printer.
	 */
	public PSTPrintVisitor(final Consumer<String> printer) {
		this(printer, false);
	}
	
	/**
	 * @param printer
	 *            Printer.
	 * @param visitLiteralRegionContents
	 *            {@code true} iff literal region contents should be visited
	 */
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
