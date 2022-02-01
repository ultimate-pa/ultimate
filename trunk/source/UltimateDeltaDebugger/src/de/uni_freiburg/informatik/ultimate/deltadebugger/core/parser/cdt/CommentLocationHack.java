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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt;

import java.lang.reflect.Field;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * This is a reflection based workaround to prevent internal calls to ASTComment.getOffset() from
 * isPartOfTranslationUnitFile(), getFileLocation() and other methods performing location computations.
 * A significant performance overhead occurs because a comments file offset is first converted into sequence number by
 * an expensive operation and then converted it back to file offset. The reason for this is unknown and this hack may
 * have negative side effects - but for now, it seems to work just fine.
 */
public class CommentLocationHack {
	private final ILogger mLogger;
	
	private final boolean mEnabled;
	private final boolean mEnableFallbackForUnsupportedMethods;
	
	private Field mAstCommentFilePath;
	private Field mAstNodeOffset;
	private Field mAstNodeLength;
	
	/**
	 * Create instance with default options.
	 *
	 * @param logger
	 *            logger instance
	 */
	public CommentLocationHack(final ILogger logger) {
		this(logger, true, true);
	}
	
	/**
	 * @param logger
	 *            Logger instance.
	 * @param enableHack
	 *            Enable the hack
	 * @param enableFallbackForUnsupportedMethods
	 *            Call the original (potentially slow) getFileLocation() to properly implement
	 *            getContextInclusionStatement() and getStartingLineNumber()/getEndingLineNumber() in
	 *            {@link CommentHackAstFileLocation} instances
	 */
	public CommentLocationHack(final ILogger logger, final boolean enableHack,
			final boolean enableFallbackForUnsupportedMethods) {
		mLogger = logger;
		boolean enabled = enableHack;
		if (enabled) {
			try {
				final Class<?> classOfAstComment =
						Class.forName("org.eclipse.cdt.internal.core.parser.scanner.ASTComment");
				final Class<?> classOfAstNode = Class.forName("org.eclipse.cdt.internal.core.dom.parser.ASTNode");
				mAstCommentFilePath = classOfAstComment.getDeclaredField("fFilePath");
				mAstNodeOffset = classOfAstNode.getDeclaredField("offset");
				mAstNodeLength = classOfAstNode.getDeclaredField("length");
				mAstCommentFilePath.setAccessible(true);
				mAstNodeOffset.setAccessible(true);
				mAstNodeLength.setAccessible(true);
			} catch (ClassNotFoundException | NoSuchFieldException | SecurityException e) {
				mLogger.warn("CommentLocationHack initialization exception: " + e);
				enabled = false;
			}
		}
		mEnabled = enabled;
		mEnableFallbackForUnsupportedMethods = enableFallbackForUnsupportedMethods;
	}
	
	/**
	 * @param node
	 *            AST comment node.
	 * @param source
	 *            source document
	 * @return AST file location
	 */
	public IASTFileLocation getFileLocation(final IASTComment node, final ISourceDocument source) {
		if (mEnabled) {
			try {
				// Note that when ASTComment.fFilePath is null, getOffset() has already been
				// called on the instance, and the workaround cannot be applied anymore.
				// However, in such a case calling the original method again will not cause
				// significant overhead anymore.
				final String filePath = (String) mAstCommentFilePath.get(node);
				if (filePath != null) {
					final int offset = (int) mAstNodeOffset.get(node);
					final int length = (int) mAstNodeLength.get(node);
					return new CommentHackAstFileLocation(offset, length, filePath, source,
							mEnableFallbackForUnsupportedMethods ? node : null);
				}
			} catch (IllegalArgumentException | IllegalAccessException e) {
				mLogger.warn("CommentLocationHack access exception: " + e);
			}
		}
		
		return node.getFileLocation();
	}
	
	/**
	 * @param node
	 *            AST comment node.
	 * @param translationUnitFilePath
	 *            file path of the translation unit
	 * @return {@code true} iff the comment is part of the translation unit file
	 */
	public boolean isPartOfTranslationUnitFile(final IASTComment node, final String translationUnitFilePath) {
		if (mEnabled) {
			try {
				// Check if the comment is in the root source file, without calling
				// isPartOfTranslationUnitFile(), because that would call getOffset()
				final String filePath = (String) mAstCommentFilePath.get(node);
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
