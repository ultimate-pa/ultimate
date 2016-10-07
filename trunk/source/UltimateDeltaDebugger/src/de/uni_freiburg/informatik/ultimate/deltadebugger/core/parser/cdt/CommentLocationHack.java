package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt;

import java.lang.reflect.Field;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

class CommentHackASTFileLocation implements IASTFileLocation {
	private final int offset;
	private final int length;
	private final String filePath;
	private final ISourceDocument source;
	private final IASTComment fallbackNode;

	public CommentHackASTFileLocation(final int offset, final int length, final String filePath,
			final ISourceDocument source, final IASTComment fallbackNode) {
		this.offset = offset;
		this.length = length;
		this.filePath = filePath;
		this.source = source;
		this.fallbackNode = fallbackNode;
	}

	@Override
	public IASTFileLocation asFileLocation() {
		return this;
	}

	@Override
	public IASTPreprocessorIncludeStatement getContextInclusionStatement() {
		return fallbackNode != null ? fallbackNode.getFileLocation().getContextInclusionStatement() : null;
	}

	@Override
	public int getEndingLineNumber() {
		if (source != null) {
			return source.getLineNumber(length == 0 ? offset : offset + length - 1);
		}
		return fallbackNode != null ? fallbackNode.getFileLocation().getEndingLineNumber() : 0;
	}

	@Override
	public String getFileName() {
		return filePath;
	}

	@Override
	public int getNodeLength() {
		return length;
	}

	@Override
	public int getNodeOffset() {
		return offset;
	}

	@Override
	public int getStartingLineNumber() {
		if (source != null) {
			return source.getLineNumber(offset);
		}
		return fallbackNode != null ? fallbackNode.getFileLocation().getStartingLineNumber() : 0;
	}

	@Override
	public String toString() {
		return getFileName() + "[" + offset + "," + (offset + length) + "]";
	}
}

/**
 * This is a reflection based workaround to prevent internal calls to ASTComment.getOffset() from
 * isPartOfTranslationUnitFile(), getFileLocation() and other methods performing location computations.
 *
 * A significant performance overhead occurs because a comments file offset is first converted into sequence number by
 * an expensive operation and then converted it back to file offset. The reason for this is unknown and this hack may
 * have negative side effects - but for now, it seems to work just fine.
 */
public class CommentLocationHack {
	private static Logger logger = Logger.getLogger(CommentLocationHack.class);

	private static final CommentLocationHack INSTANCE = new CommentLocationHack();

	public static CommentLocationHack getDefaultInstance() {
		return INSTANCE;
	}

	private final boolean enabled;

	// Call the original getFileLocation() to properly support getContextInclusionStatement()
	// and getStartingLineNumber()/getEndingLineNumber()
	private final boolean enableFallbackForUnsupportedMethods;
	private Field ASTComment_fFilePath;
	private Field ASTNode_offset;

	private Field ASTNode_length;

	public CommentLocationHack() {
		this(true, true);
	}

	public CommentLocationHack(final boolean enabled, final boolean enableFallbackForUnsupportedMethods) {
		boolean enableHack = enabled;
		if (enableHack) {
			try {
				final Class<?> ASTCommentClass =
						Class.forName("org.eclipse.cdt.internal.core.parser.scanner.ASTComment");
				final Class<?> ASTNodeClass = Class.forName("org.eclipse.cdt.internal.core.dom.parser.ASTNode");
				ASTComment_fFilePath = ASTCommentClass.getDeclaredField("fFilePath");
				ASTNode_offset = ASTNodeClass.getDeclaredField("offset");
				ASTNode_length = ASTNodeClass.getDeclaredField("length");
				ASTComment_fFilePath.setAccessible(true);
				ASTNode_offset.setAccessible(true);
				ASTNode_length.setAccessible(true);
			} catch (ClassNotFoundException | NoSuchFieldException | SecurityException e) {
				logger.warn("CommentLocationHack initialization exception", e);
				enableHack = false;
			}
		}
		this.enabled = enableHack;
		this.enableFallbackForUnsupportedMethods = enableFallbackForUnsupportedMethods;
	}

	public IASTFileLocation getFileLocation(final IASTComment node, final ISourceDocument source) {
		if (enabled) {
			try {
				// Note that when ASTComment.fFilePath is null, getOffset() has already been
				// called on the instance, and the workaround cannot be applied anymore.
				// However, in such a case calling the original method again will not cause
				// significant overhead anymore.
				final String filePath = (String) ASTComment_fFilePath.get(node);
				if (filePath != null) {
					final int offset = (int) ASTNode_offset.get(node);
					final int length = (int) ASTNode_length.get(node);
					return new CommentHackASTFileLocation(offset, length, filePath, source,
							enableFallbackForUnsupportedMethods ? node : null);
				}
			} catch (IllegalArgumentException | IllegalAccessException e) {
				logger.warn("CommentLocationHack access exception", e);
			}
		}

		return node.getFileLocation();
	}

	public boolean isPartOfTranslationUnitFile(final IASTComment node, final String translationUnitFilePath) {
		if (enabled) {
			try {
				// Check if the comment is in the root source file, without calling
				// isPartOfTranslationUnitFile(), because that would call getOffset()
				final String filePath = (String) ASTComment_fFilePath.get(node);
				if (filePath != null) {
					return translationUnitFilePath.equals(filePath);
				}
			} catch (IllegalArgumentException | IllegalAccessException e) {
				logger.warn("CommentLocationHack access exception", e);
			}
		}
		return node.isPartOfTranslationUnitFile();
	}
}
