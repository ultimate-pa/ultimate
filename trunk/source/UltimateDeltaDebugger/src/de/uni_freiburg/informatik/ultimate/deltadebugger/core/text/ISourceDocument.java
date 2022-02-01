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
 * Source document.
 */
public interface ISourceDocument {
	/**
	 * @param offset
	 *            Offset.
	 * @return column number
	 */
	int getColumnNumber(int offset);
	
	/**
	 * @return The length.
	 */
	int getLength();
	
	/**
	 * @param offset
	 *            Offset.
	 * @return line number
	 */
	int getLineNumber(int offset);
	
	/**
	 * @param lineNumber
	 *            Line number.
	 * @return line offset
	 */
	int getLineOffset(int lineNumber);
	
	/**
	 * @return The number of lines.
	 */
	int getNumberOfLines();
	
	/**
	 * @return The text.
	 */
	String getText();
	
	/**
	 * @param offset
	 *            Offset.
	 * @param endOffset
	 *            end of the offset
	 * @return text between offset
	 */
	String getText(int offset, int endOffset);
	
	/**
	 * @param location
	 *            Location.
	 * @return text of location
	 */
	String getText(ISourceRange location);
	
	/**
	 * @param offset
	 *            Offset.
	 * @param endOffset
	 *            end of the offset
	 * @return new source range
	 */
	ISourceRange newSourceRange(int offset, int endOffset);
}
