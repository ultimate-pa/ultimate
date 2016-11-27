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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

/**
 * Printer for a source document location.
 */
public final class SourceDocumentLocationPrinter {
	private SourceDocumentLocationPrinter() {
		// static access
	}
	
	/**
	 * @param document
	 *            Document.
	 * @param offset
	 *            offset
	 * @param endOffset
	 *            end of the offset
	 * @param builder
	 *            string builder
	 * @return the appended string
	 */
	public static StringBuilder appendTo(final ISourceDocument document, final int offset, final int endOffset,
			final StringBuilder builder) {
		final int startingLineNumber = document.getLineNumber(offset);
		final int startingLineColumn = document.getColumnNumber(offset);
		builder.append("Line ").append(startingLineNumber).append(", Column ").append(startingLineColumn);
		if (offset == endOffset) {
			return builder;
		}
		
		final int endingLineNumber = document.getLineNumber(endOffset - 1);
		final int endingLineColumn = document.getColumnNumber(endOffset);
		if (startingLineNumber == endingLineNumber) {
			builder.append(" - ").append(endingLineColumn);
			return builder;
		}
		
		builder.append(" - ").append("Line ").append(endingLineNumber).append(", Column ").append(endingLineColumn);
		return builder;
	}
	
	/**
	 * @param document
	 *            Document.
	 * @param range
	 *            range
	 * @param builder
	 *            string builder
	 * @return the respective string
	 */
	public static StringBuilder appendTo(final ISourceDocument document, final ISourceRange range,
			final StringBuilder builder) {
		return appendTo(document, range.offset(), range.endOffset(), builder);
	}
	
	/**
	 * @param document
	 *            Document.
	 * @param offset
	 *            offset
	 * @param endOffset
	 *            end of the offset
	 * @return the respective string
	 */
	public static String makeString(final ISourceDocument document, final int offset, final int endOffset) {
		return appendTo(document, offset, endOffset, new StringBuilder()).toString();
	}
	
	/**
	 * @param document
	 *            Document.
	 * @param range
	 *            range
	 * @return the respective string
	 */
	public static String makeString(final ISourceDocument document, final ISourceRange range) {
		return makeString(document, range.offset(), range.endOffset());
	}
}
