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

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * This class implements the computation of the source location of existing AST nodes. It is a facade to hide the
 * complexity of the CDT API (IASTFileLocation) in favor of the delta debuggers simplified model that is limited to a
 * single source file (ISourceDocument, ISourceRange). It is currently used to transparently optimize the computation of
 * comment locations {@see CommentLocationHack}.
 */
public class LocationResolver {
	private final String mTranslationUnitFilePath;
	private final ISourceDocument mSourceDocument;
	private final CommentLocationHack mCommentHack;
	
	/**
	 * Default constructor uses a default constructed comment location hack instance.
	 * 
	 * @param translationUnitFilePath
	 *            source file path
	 * @param sourceDocument
	 *            source file contents
	 * @param logger
	 *            logger instance
	 */
	public LocationResolver(final String translationUnitFilePath, final ISourceDocument sourceDocument,
			final ILogger logger) {
		this(translationUnitFilePath, sourceDocument, new CommentLocationHack(logger));
	}
	
	/**
	 * @param translationUnitFilePath
	 *            File path of the translation unit.
	 * @param sourceDocument
	 *            source document
	 * @param commentHack
	 *            comment location hack
	 */
	public LocationResolver(final String translationUnitFilePath, final ISourceDocument sourceDocument,
			final CommentLocationHack commentHack) {
		mTranslationUnitFilePath = translationUnitFilePath;
		mSourceDocument = sourceDocument;
		mCommentHack = commentHack;
	}
	
	/**
	 * @param loc
	 *            AST file location.
	 * @return source range
	 */
	public ISourceRange asSourceRange(final IASTFileLocation loc) {
		final int offset = loc.getNodeOffset();
		final int length = loc.getNodeLength();
		return mSourceDocument.newSourceRange(offset, offset + length);
	}
	
	/**
	 * @param node
	 *            AST node.
	 * @return AST file location
	 */
	public IASTFileLocation getFileLocation(final IASTNode node) {
		if (node instanceof IASTComment) {
			return mCommentHack.getFileLocation((IASTComment) node, mSourceDocument);
		}
		return node.getFileLocation();
	}
	
	/**
	 * @param node
	 *            AST node.
	 * @return source range
	 */
	public ISourceRange getSourceRange(final IASTNode node) {
		return asSourceRange(getFileLocation(node));
	}
	
	/**
	 * Compute the location of a node in the translation unit file.
	 *
	 * @param node
	 *            AST node
	 * @return source range in the translation unit file or null if node is not part of it
	 */
	public ISourceRange getSourceRangeInTranslationUnitFile(final IASTNode node) {
		if (!isPartOfTranslationUnitFile(node)) {
			return null;
		}
		
		final IASTFileLocation loc = getFileLocation(node);
		if (loc == null) {
			return null;
		}
		
		return asSourceRange(loc);
	}
	
	/**
	 * Compute the source range of any node. If a node is located in an included file, the location of the outermost
	 * inclusion statement is returned.
	 *
	 * @param node
	 *            AST node
	 * @return source range of either the node itself or the originating inclusion statement. null if no location
	 *         information is available.
	 */
	public ISourceRange getSourceRangeMappedToInclusionStatement(final IASTNode node) {
		IASTNode current = node;
		for (;;) {
			final ISourceRange range = getSourceRangeInTranslationUnitFile(current);
			if (range != null) {
				return range;
			}
			
			final IASTFileLocation loc = getFileLocation(current);
			if (loc == null) {
				return null;
			}
			
			// map nodes inside external files to originating include
			final IASTPreprocessorIncludeStatement include = loc.getContextInclusionStatement();
			if (include == null) {
				// This should not happen, because getRangeInTranslationUnitFile() determined that
				// the current node is not inside the translation unit file, so it should either
				// have no file location or be part of an included file
				assert false : "should not happen!?!";
				return null;
			}
			
			current = include;
		}
	}
	
	/**
	 * Check if a node is located in the translation unit file. Note that in contrast to
	 * IASTNode.isPartOfTranslationUnitFile() it returns true for nodes that span over multiple files and only partly
	 * overlap the translation unit file.
	 *
	 * @param node
	 *            AST node
	 * @return true iff node is (partly) located in the translation unit file
	 */
	public boolean isPartOfTranslationUnitFile(final IASTNode node) {
		// Note that isPartOfTranslationUnitFile() only checks the begin-offset
		// and not the end-offset. This means it returns false for nodes
		// that start inside a header but span into the translation unit file.
		// To prevent false negative for nodes that do have a valid file location
		// (even though overlapping with preprocessor nodes) only use it for nodes
		// that cannot span over file boundaries, i.e. preprocessor nodes and check
		// the filename of the computed file location otherwise.
		if (node instanceof IASTComment) {
			return mCommentHack.isPartOfTranslationUnitFile((IASTComment) node, mTranslationUnitFilePath);
		}
		if (node instanceof IASTPreprocessorStatement || node instanceof IASTPreprocessorMacroExpansion) {
			return node.isPartOfTranslationUnitFile();
		}
		final IASTFileLocation loc = node.getFileLocation();
		return loc != null && mTranslationUnitFilePath.equals(loc.getFileName());
	}
	
}
