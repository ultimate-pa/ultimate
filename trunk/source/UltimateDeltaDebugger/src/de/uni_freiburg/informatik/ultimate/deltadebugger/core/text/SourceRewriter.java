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

import java.util.List;

/**
 * Rewrites text in a source document.
 * 
 * @see de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.AbstractTextRewriter
 */
public class SourceRewriter extends AbstractTextRewriter {
	private final ISourceDocument mDocument;
	
	/**
	 * Creates a rewriter for the text in a source document.
	 *
	 * @param document
	 *            immutable original source document
	 */
	public SourceRewriter(final ISourceDocument document) {
		mDocument = document;
	}
	
	protected SourceRewriter(final ISourceDocument document, final List<Change> mergeChanges, final int mergedDelta) {
		super(mergeChanges, mergedDelta);
		mDocument = document;
	}
	
	/**
	 * Copy constructor.
	 *
	 * @param other
	 *            rewriter instance to copy
	 */
	public SourceRewriter(final SourceRewriter other) {
		super(other);
		mDocument = other.mDocument;
	}
	
	@Override
	public SourceRewriter delete(final int offset, final int endOffset) {
		super.delete(offset, endOffset);
		return this;
	}
	
	/**
	 * Removes a range of text.
	 * Equivalent to {@code delete(location.offset(), location.endOffset())}
	 *
	 * @param location
	 *            range to delete
	 * @return this
	 */
	public SourceRewriter delete(final ISourceRange location) {
		return delete(location.offset(), location.endOffset());
	}
	
	@Override
	protected String getExceptionText(final Change change) {
		return mDocument.newSourceRange(change.mOffset, change.mEndOffset).toString();
	}
	
	@Override
	protected final int getOriginalLength() {
		return mDocument.getLength();
	}
	
	@Override
	protected String getOriginalText() {
		return mDocument.getText();
	}
	
	/**
	 * Get rewritten text for the given range in the original text.
	 * Note: not particularly efficient...
	 *
	 * @param offset
	 *            inclusive start index
	 * @param endOffset
	 *            exclusive end index
	 * @param includeInsertionsAtEnd
	 *            include insertations at the endOffset
	 * @return rewritten text in the specified range
	 */
	public String getRewrittenSubstring(final int offset, final int endOffset, final boolean includeInsertionsAtEnd) {
		final ISourceRange remapped = remapRange(offset, endOffset, includeInsertionsAtEnd);
		return apply().substring(remapped.offset(), remapped.endOffset());
	}
	
	/**
	 * Get rewritten text for the given range in the original text.
	 * Note: not particularly efficient...
	 *
	 * @param location
	 *            original text range
	 * @param includeInsertionsAtEnd
	 *            include insertations at the endOffset
	 * @return rewritten text in the specified range
	 */
	public String getRewrittenSubstring(final ISourceRange location, final boolean includeInsertionsAtEnd) {
		return getRewrittenSubstring(location.offset(), location.endOffset(), includeInsertionsAtEnd);
	}
	
	public ISourceDocument getSourceDocument() {
		return mDocument;
	}
	
	@Override
	public SourceRewriter insert(final int offset, final String text) {
		super.insert(offset, text);
		return this;
	}
	
	/**
	 * Inserts a string at the end of a location.
	 * Equivalent to {@code insert(location.endOffset(), text)}
	 *
	 * @param location
	 *            location to insert at
	 * @param text
	 *            inserted text string
	 * @return this
	 */
	public SourceRewriter insertAfter(final ISourceRange location, final String text) {
		return insert(location.endOffset(), text);
	}
	
	/**
	 * Inserts a string at the beginning of a location.
	 * Equivalent to {@code insert(location.offset(), text)}
	 *
	 * @param location
	 *            location to insert at
	 * @param text
	 *            inserted text string
	 * @return this
	 */
	public SourceRewriter insertBefore(final ISourceRange location, final String text) {
		return insert(location.offset(), text);
	}
	
	/**
	 * Add all changes from the other rewriter to this instance.
	 * In case of a RewriteConflictException this instance is not modified.
	 * <p>
	 * Throws an {@link IllegalArgumentException} if document length in both rewriters is not the same.
	 *
	 * @param other
	 *            rewriter containing changes to be added
	 * @return this
	 */
	@Override
	public SourceRewriter merge(final AbstractTextRewriter other) {
		super.merge(other);
		return this;
	}
	
	/**
	 * Creates a new rewriter that contains all changes from this and the other instance.
	 * If insertions at the same offset exist, the insertions in this instance take precedence over those from the
	 * other.
	 * <p>
	 * Throws an {@link IllegalArgumentException} if document length in both rewriters is not the same.
	 *
	 * @param other
	 *            other instance
	 * @return new rewriter containing changse from this and other
	 */
	public SourceRewriter mergedCopy(final SourceRewriter other) {
		if (getOriginalLength() != other.getOriginalLength()) {
			throw new IllegalArgumentException("length mismatch");
		}
		return new SourceRewriter(mDocument, getMergedChanges(other), getDelta() + other.getDelta());
	}
	
	/**
	 * Computes a character range in the rewritten text for the given range in the original text.
	 *
	 * @param offset
	 *            inclusive start index
	 * @param endOffset
	 *            exclusive end index
	 * @param includeInsertionsAtEnd
	 *            include insertions at the endOffset
	 * @return corresponding range in the rewritten text
	 */
	public ISourceRange remapRange(final int offset, final int endOffset, final boolean includeInsertionsAtEnd) {
		if (offset > endOffset) {
			throw new IndexOutOfBoundsException();
		}
		return new PlainSourceRange(remapOffset(offset, false), remapOffset(endOffset, includeInsertionsAtEnd));
	}
	
	/**
	 * Computes a character range in the rewritten text for the given range in the original text.
	 *
	 * @param location
	 *            range to remap
	 * @param includeInsertionsAtEnd
	 *            include insertations at the endOffset
	 * @return corresponding range in the rewritten text
	 */
	public ISourceRange remapRange(final ISourceRange location, final boolean includeInsertionsAtEnd) {
		return remapRange(location.offset(), location.endOffset(), includeInsertionsAtEnd);
	}
	
	@Override
	public SourceRewriter replace(final int offset, final int endOffset, final String replacement) {
		super.replace(offset, endOffset, replacement);
		return this;
	}

	/**
	 * Replaces a range of text.
	 * Equivalent to {@code replace(location.offset(), location.endOffset(), replacement)}
	 *
	 * @param location
	 *            range to replace
	 * @param replacement
	 *            replacement string
	 * @return this
	 */
	public SourceRewriter replace(final ISourceRange location, final String replacement) {
		return replace(location.offset(), location.endOffset(), replacement);
	}
}
