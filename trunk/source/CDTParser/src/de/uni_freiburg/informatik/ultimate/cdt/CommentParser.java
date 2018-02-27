/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * This class gets an array of Comments from the CDT-Parser.
 * It iterates over all comments and check if it is an ACSL
 * Comment, if so it starts the ACSL-Parser
 */
package de.uni_freiburg.informatik.ultimate.cdt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.cdt.parser.Activator;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 30.01.2012
 */
public class CommentParser {

	/**
	 * The list of comments.
	 */
	private final IASTComment[] mCommentList;
	/**
	 * Map startline numbers of a block to end line numbers.
	 */
	private final HashMap<Integer, Integer> mFunctionLineRange;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	/**
	 * The Constructor.
	 *
	 * @param comments
	 *            commentList
	 * @param lineRange
	 *            Map with line ranges of functions. Can be determined with FunctionLineVisitor.
	 */
	public CommentParser(final IASTComment[] comments, final HashMap<Integer, Integer> lineRange, final ILogger logger,
			final IUltimateServiceProvider services) {
		mCommentList = comments;
		mFunctionLineRange = lineRange;
		mLogger = logger;
		mServices = services;
	}

	/**
	 * Process all Comments we found in the C-File. We do in general the following steps.
	 *
	 * <ol>
	 * <li>determine whether it is a ACSL comment or not</li>
	 * <li>determine its position (local / global)</li>
	 * <li>remove comment symbols</li>
	 * <li>start the ACSL-Parser</li>
	 * <li>return list with ACSLNodes</li>
	 * </ol>
	 *
	 * @return <code>List&lt;ACSLNode&gt;</code> a list of ACSL ASTs
	 */
	public List<ACSLNode> processComments() {
		final ArrayList<ACSLNode> acslList = new ArrayList<>();
		for (final IASTComment comment : mCommentList) {
			final String text = new String(comment.getComment());
			// We check if the comment is a ACSL_Comment
			if (text.startsWith("//@") || text.startsWith("/*@")) {
				// We need to remove comment symbols
				final StringBuilder input = new StringBuilder();
				input.append(determineCodePosition(comment));
				input.append('\n');
				input.append(text, 2, text.length() - (text.endsWith("*/") ? 2 : 0));
				final int lineOffset = comment.getFileLocation().getStartingLineNumber();
				final int columnOffset = getColumnOffset(comment) + 2;
				// now we parse the ACSL thing
				try {
					ACSLNode acslNode;
					try {
						acslNode = Parser.parseComment(input.toString(), lineOffset, columnOffset, mLogger);
					} catch (final ExceptionInInitializerError e) { // ignore
					} catch (final NoClassDefFoundError e) { // ignore
					} finally {
						// Is parsing every comment twice actually intended?
						acslNode = Parser.parseComment(input.toString(), lineOffset, columnOffset, mLogger);
					}
					if (acslNode != null) {
						acslNode.setFileName(comment.getContainingFilename());
						acslList.add(acslNode);
					}
				} catch (final ACSLSyntaxErrorException e) {
					final ACSLNode node = e.getLocation();
					node.setFileName(comment.getFileLocation().getFileName());
					reportSyntaxError(node, e.getMessageText());
				} catch (final Exception e) {
					throw new RuntimeException(e);
				}
			}
		}
		return acslList;
	}

	/**
	 * Compute the column number of the first comment character.
	 *
	 * @param comment
	 *            comment
	 * @return column offset
	 */
	private static int getColumnOffset(final IASTComment comment) {
		final IASTFileLocation loc = comment.getFileLocation();
		if (!comment.isPartOfTranslationUnitFile()) {
			// No idea how to get header source text
			return 0;
		}
		final String sourceText = comment.getTranslationUnit().getRawSignature();
		final int commentOffset = loc.getNodeOffset();
		for (int i = commentOffset - 1; i >= 0; --i) {
			final char c = sourceText.charAt(i);
			if (c == '\n' || c == '\r') {
				return commentOffset - i - 1;
			}
		}
		return commentOffset;
	}

	/**
	 * For the ACSL-Parser we need to know, whether it is a local or a global comment. We get this with the line numbers
	 * of all functions inside the c-code.
	 *
	 * @param comment
	 *            the CDT-Comment
	 * @return "lstart" or "gstart" depending on the position
	 */
	private String determineCodePosition(final IASTComment comment) {
		final int start = comment.getFileLocation().getStartingLineNumber();
		final int end = comment.getFileLocation().getEndingLineNumber();
		for (final Integer lineStart : mFunctionLineRange.keySet()) {
			if (start >= lineStart && end <= mFunctionLineRange.get(lineStart)) {
				return "lstart";
			}
		}
		return "gstart";
	}

	private void reportSyntaxError(final ACSLNode node, final String msg) {
		final ILocation loc = new SimpleAcslLocation(node);
		final SyntaxErrorResult result = new SyntaxErrorResult(Activator.PLUGIN_NAME, loc, msg);
		mLogger.warn(msg);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}

	private static final class SimpleAcslLocation implements ILocation {

		private static final long serialVersionUID = 1L;

		private final ACSLNode mNode;

		private SimpleAcslLocation(final ACSLNode node) {
			mNode = node;
		}

		@Override
		public Map<String, Object> getAnnotationsAsMap() {
			return Collections.emptyMap();
		}

		@Override
		public int getStartLine() {
			return mNode.getStartingLineNumber();
		}

		@Override
		public int getStartColumn() {
			return mNode.getLocation().getStartColumn();
		}

		@Override
		public String getFileName() {
			return mNode.getFileName();
		}

		@Override
		public int getEndLine() {
			return mNode.getEndingLineNumber();
		}

		@Override
		public int getEndColumn() {
			return mNode.getLocation().getEndColumn();
		}

		@Override
		public IAnnotations getCheck() {
			return null;
		}
	}
}
