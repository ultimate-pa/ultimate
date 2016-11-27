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
 * Represents a character range in a source file.
 */
public interface ISourceRange {
	/**
	 * @param index Index.
	 * @return {@code true} iff the index is in the range
	 */
	default boolean contains(final int index) {
		return offset() <= index && index < endOffset();
	}
	
	/**
	 * 
	 * @param offset Offset.
	 * @param endOffset end of the offset
	 * @return @return {@code true} iff the offset is in the range
	 */
	default boolean contains(final int offset, final int endOffset) {
		return offset() <= offset && endOffset <= endOffset();
	}
	
	/**
	 * 
	 * @param other Other range.
	 * @return @return {@code true} iff the other range is in the range
	 */
	default boolean contains(final ISourceRange other) {
		return offset() <= other.offset() && other.endOffset() <= endOffset();
	}
	
	/**
	 * 
	 * @param other Other range.
	 * @return @return {@code true} iff the other range is disjoint
	 */
	default boolean disjoint(final ISourceRange other) {
		return endOffset() <= other.offset() || other.endOffset() <= offset();
	}
	
	/**
	 * @return Exclusive end-offset of the range.
	 */
	int endOffset();
	
	/**
	 * @param other Other range.
	 * @return {@code true} iff the two ranges are the same
	 */
	default boolean equalsSourceRange(final ISourceRange other) {
		return offset() == other.offset() && endOffset() == other.endOffset();
	}
	
	/**
	 * @return Number of characters in this range.
	 */
	default int length() {
		return endOffset() - offset();
	}
	
	/**
	 * @return Start offset of the range.
	 */
	int offset();
}
