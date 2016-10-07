package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.RewriteConflictException;

/**
 * {@inheritDoc}
 * 
 * @see de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.AbstractTextRewriter
 */
public class SourceRewriter extends AbstractTextRewriter {
	private final ISourceDocument document;

	/**
	 * Creates a rewriter for the text in a source document
	 * 
	 * @param document
	 *            immutable original source document
	 */
	public SourceRewriter(ISourceDocument document) {
		this.document = document;
	}

	/**
	 * Copy constructor
	 * 
	 * @param other
	 *            rewriter instance to copy
	 */
	public SourceRewriter(SourceRewriter other) {
		super(other);
		this.document = other.document;
	}

	protected SourceRewriter(ISourceDocument document, List<Change> mergeChanges, int mergedDelta) {
		super(mergeChanges, mergedDelta);
		this.document = document;
	}

	@Override
	protected final int getOriginalLength() {
		return document.getLength();
	}

	@Override
	protected String getOriginalText() {
		return document.getText();
	}

	public ISourceDocument getSourceDocument() {
		return document;
	}

	/**
	 * Removes a range of text.
	 * 
	 * Equivalent to {@code delete(location.offset(), location.endOffset())}
	 * 
	 * @param location
	 *            range to delete
	 * @return this
	 * @throws RewriteConflictException
	 */
	public SourceRewriter delete(ISourceRange location) {
		return delete(location.offset(), location.endOffset());
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public SourceRewriter delete(int offset, int endOffset) {
		super.delete(offset, endOffset);
		return this;
	}

	/**
	 * Inserts a string at the beginning of a location.
	 * 
	 * Equivalent to {@code insert(location.offset(), text)}
	 * 
	 * @param location
	 *            location to insert at
	 * @param text
	 *            inserted text string
	 * @return this
	 * @throws RewriteConflictException
	 */
	public SourceRewriter insertBefore(ISourceRange location, String text) {
		return insert(location.offset(), text);
	}

	/**
	 * Inserts a string at the end of a location.
	 * 
	 * Equivalent to {@code insert(location.endOffset(), text)}
	 * 
	 * @param location
	 *            location to insert at
	 * @param text
	 *            inserted text string
	 * @return this
	 * @throws RewriteConflictException
	 */
	public SourceRewriter insertAfter(ISourceRange location, String text) {
		return insert(location.endOffset(), text);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public SourceRewriter insert(int offset, String text) {
		super.insert(offset, text);
		return this;
	}

	/**
	 * Replaces a range of text.
	 * 
	 * Equivalent to
	 * {@code replace(location.offset(), location.endOffset(), replacement)}
	 * 
	 * @param location
	 *            range to replace
	 * @param replacement
	 *            replacement string
	 * @return this
	 * @throws RewriteConflictException
	 */
	public SourceRewriter replace(ISourceRange location, String replacement) {
		return replace(location.offset(), location.endOffset(), replacement);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public SourceRewriter replace(int offset, int endOffset, String replacement) {
		super.replace(offset, endOffset, replacement);
		return this;
	}

	/**
	 * Add all changes from the other rewriter to this instance.
	 * 
	 * In case of a RewriteConflictException this instance is not modified.
	 * 
	 * @param other
	 *            rewriter containing changes to be added
	 * @return this
	 * @throws RewriteConflictException
	 * @throws IllegalArgumentException
	 *             if document length in both rewriters is not the same
	 */
	@Override
	public SourceRewriter merge(AbstractTextRewriter other) {
		super.merge(other);
		return this;
	}

	/**
	 * Creates a new rewriter that contains all changes from this and the other
	 * instance.
	 * 
	 * If insertions at the same offset exist, the insertions in this instance
	 * take precedence over those from the other.
	 * 
	 * @param other
	 *            other instance
	 * @return new rewriter containing changse from this and other
	 * @throws RewriteConflictException
	 * @throws IllegalArgumentException
	 *             if document length in both rewriters is not the same
	 */
	public SourceRewriter mergedCopy(SourceRewriter other) {
		if (getOriginalLength() != other.getOriginalLength()) {
			throw new IllegalArgumentException("length mismatch");
		}
		return new SourceRewriter(document, getMergedChanges(other), getDelta() + other.getDelta());
	}

	/**
	 * Computes a character range in the rewritten text for the given range in
	 * the original text.
	 * 
	 * @param location
	 *            range to remap
	 * @param includeInsertionsAtEnd
	 *            include insertations at the endOffset
	 * @return corresponding range in the rewritten text
	 * @throws IndexOutOfBoundsException
	 */
	public ISourceRange remapRange(ISourceRange location, boolean includeInsertionsAtEnd) {
		return remapRange(location.offset(), location.endOffset(), includeInsertionsAtEnd);
	}

	/**
	 * Computes a character range in the rewritten text for the given range in
	 * the original text.
	 * 
	 * @param offset
	 *            inclusive start index
	 * @param endOffset
	 *            exclusive end index
	 * @param includeInsertionsAtEnd
	 *            include insertations at the endOffset
	 * @return corresponding range in the rewritten text
	 * @throws IndexOutOfBoundsException
	 */
	public ISourceRange remapRange(int offset, int endOffset, boolean includeInsertionsAtEnd) {
		if (offset > endOffset) {
			throw new IndexOutOfBoundsException();
		}
		return document.newSourceRange(remapOffset(offset, false), remapOffset(endOffset, includeInsertionsAtEnd));
	}

	/**
	 * Get rewritten text for the given range in the original text.
	 * 
	 * Note: not particularly efficient...
	 * 
	 * @param location
	 *            original text range
	 * @param includeInsertionsAtEnd
	 *            include insertations at the endOffset
	 * @return rewritten text in the specified range
	 * @throws IndexOutOfBoundsException
	 */
	public String getRewrittenSubstring(ISourceRange location, boolean includeInsertionsAtEnd) {
		return getRewrittenSubstring(location.offset(), location.endOffset(), includeInsertionsAtEnd);
	}

	/**
	 * Get rewritten text for the given range in the original text.
	 * 
	 * Note: not particularly efficient...
	 * 
	 * @param offset
	 *            inclusive start index
	 * @param endOffset
	 *            exclusive end index
	 * @param includeInsertionsAtEnd
	 *            include insertations at the endOffset
	 * @return rewritten text in the specified range
	 * @throws IndexOutOfBoundsException
	 */
	public String getRewrittenSubstring(int offset, int endOffset, boolean includeInsertionsAtEnd) {
		final ISourceRange remapped = remapRange(offset, endOffset, includeInsertionsAtEnd);
		return apply().substring(remapped.offset(), remapped.endOffset());
	}

	@Override
	protected String getExceptionText(Change change) {
		return document.newSourceRange(change.offset, change.endOffset).toString();
	}

}
