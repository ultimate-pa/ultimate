package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt;

import java.lang.reflect.Field;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * This is a reflection based workaround to prevent internal calls to ASTComment.getOffset() from
 * isPartOfTranslationUnitFile(), getFileLocation() and other methods performing location computations.
 *
 * A significant performance overhead occurs because a comments file offset is first converted into sequence number by
 * an expensive operation and then converted it back to file offset. The reason for this is unknown and this hack may
 * have negative side effects - but for now, it seems to work just fine.
 */
public class CommentLocationHack {
	private final ILogger mLogger;

	private final boolean mEnabled;
	private final boolean mEnableFallbackForUnsupportedMethods;
	
	private Field mASTCommentFilePath;
	private Field mASTNodeOffset;
	private Field mASTNodeLength;
	
	/**
	 * Create instance with default options
	 *
	 * @param logger
	 *            logger instance
	 */
	public CommentLocationHack(final ILogger logger) {
		this(logger, true, true);
	}

	/**
	 * @param logger
	 *            logger instance
	 * @param enableHack
	 *            Enable the hack
	 * @param enableFallbackForUnsupportedMethods
	 *            Call the original (potentially slow) getFileLocation() to properly implement
	 *            getContextInclusionStatement() and getStartingLineNumber()/getEndingLineNumber() in
	 *            {@link CommentHackASTFileLocation} instances
	 */
	public CommentLocationHack(final ILogger logger, final boolean enableHack,
			final boolean enableFallbackForUnsupportedMethods) {
		mLogger = logger;
		boolean enabled = enableHack;
		if (enabled) {
			try {
				final Class<?> classOfASTComment =
						Class.forName("org.eclipse.cdt.internal.core.parser.scanner.ASTComment");
				final Class<?> classOfASTNode = Class.forName("org.eclipse.cdt.internal.core.dom.parser.ASTNode");
				mASTCommentFilePath = classOfASTComment.getDeclaredField("fFilePath");
				mASTNodeOffset = classOfASTNode.getDeclaredField("offset");
				mASTNodeLength = classOfASTNode.getDeclaredField("length");
				mASTCommentFilePath.setAccessible(true);
				mASTNodeOffset.setAccessible(true);
				mASTNodeLength.setAccessible(true);
			} catch (ClassNotFoundException | NoSuchFieldException | SecurityException e) {
				mLogger.warn("CommentLocationHack initialization exception: " + e);
				enabled = false;
			}
		}
		mEnabled = enabled;
		mEnableFallbackForUnsupportedMethods = enableFallbackForUnsupportedMethods;
	}

	public IASTFileLocation getFileLocation(final IASTComment node, final ISourceDocument source) {
		if (mEnabled) {
			try {
				// Note that when ASTComment.fFilePath is null, getOffset() has already been
				// called on the instance, and the workaround cannot be applied anymore.
				// However, in such a case calling the original method again will not cause
				// significant overhead anymore.
				final String filePath = (String) mASTCommentFilePath.get(node);
				if (filePath != null) {
					final int offset = (int) mASTNodeOffset.get(node);
					final int length = (int) mASTNodeLength.get(node);
					return new CommentHackASTFileLocation(offset, length, filePath, source,
							mEnableFallbackForUnsupportedMethods ? node : null);
				}
			} catch (IllegalArgumentException | IllegalAccessException e) {
				mLogger.warn("CommentLocationHack access exception: " + e);
			}
		}

		return node.getFileLocation();
	}

	public boolean isPartOfTranslationUnitFile(final IASTComment node, final String translationUnitFilePath) {
		if (mEnabled) {
			try {
				// Check if the comment is in the root source file, without calling
				// isPartOfTranslationUnitFile(), because that would call getOffset()
				final String filePath = (String) mASTCommentFilePath.get(node);
				if (filePath != null) {
					return translationUnitFilePath.equals(filePath);
				}
			} catch (IllegalArgumentException | IllegalAccessException e) {
				mLogger.warn("CommentLocationHack access exception: " + e);
			}
		}
		return node.isPartOfTranslationUnitFile();
	}
}
