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
import java.util.HashMap;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;
import org.eclipse.cdt.core.dom.ast.IASTComment;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.models.ILocation;

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
	private IASTComment[] commentList;
	/**
	 * Map startline numbers of a block to end line numbers.
	 */
	private HashMap<Integer, Integer> functionLineRange;
	/**
	 * Pattern which recognizes ACSL comments.
	 */
	private final String ACSL_PATTERN = "(/\\*@.*@\\*/)|(//@.*)";
	/**
	 * Pattern which recognizes ACSL comments.
	 */
	private final String COMMENT_PATTERN = "(/\\*@)|(@\\*/)|(@[^\\*])";
	/**
	 * The compiled pattern to use.
	 */
	private Pattern pattern;
	private ILogger mLogger;
	private Dispatcher mDispatcher;

	/**
	 * The Constructor.
	 * 
	 * @param comments
	 *            commentList
	 * @param lineRange
	 *            Map with line ranges of functions. Can be determined with
	 *            FunctionLineVisitor.
	 */
	public CommentParser(IASTComment[] comments, HashMap<Integer, Integer> lineRange, ILogger logger,
			Dispatcher dispatch) {
		this.commentList = comments;
		this.functionLineRange = lineRange;
		this.pattern = Pattern.compile(ACSL_PATTERN, Pattern.DOTALL);
		mLogger = logger;
		mDispatcher = dispatch;
	}

	/**
	 * Process all Comments we found in the C-File. We do in general the
	 * following steps.
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
		StringBuilder sb = new StringBuilder();
		ArrayList<ACSLNode> acslList = new ArrayList<ACSLNode>();
		for (IASTComment comment : commentList) {
			sb.append(comment.getComment());
			// We check if the comment is a ACSL_Comment
			Matcher matcher = this.pattern.matcher(sb);
			if (matcher.matches()) {
				// We need to remove comment symbols
				StringBuilder input = new StringBuilder();
				input.append(determineCodePosition(comment));
				input.append('\n');
				input.append(removeCommentSymbols(sb.toString()));
				// System.out.println(input.toString());
				// now we parse the ACSL thing
				try {
					ACSLNode acslNode;
					try {
						acslNode = Parser.parseComment(input.toString(),
								comment.getFileLocation().getStartingLineNumber(),
								comment.getFileLocation().getEndingLineNumber(), mLogger);
					} catch (ExceptionInInitializerError e) { // ignore
					} catch (NoClassDefFoundError e) { // ignore
					} finally {
						acslNode = Parser.parseComment(input.toString(),
								comment.getFileLocation().getStartingLineNumber(),
								comment.getFileLocation().getEndingLineNumber(), mLogger);
					}
					if (acslNode != null) {
						acslNode.setFileName(comment.getContainingFilename());
						acslList.add(acslNode);
					}
				} catch (ACSLSyntaxErrorException e) {
					ACSLNode node = e.getLocation();
					node.setFileName(comment.getFileLocation().getFileName());
					ILocation loc = LocationFactory.createACSLLocation(node);
					mDispatcher.syntaxError(loc, e.getMessageText());
				} catch (Exception e) {
					throw new IllegalArgumentException("Exception should be cached: " + e.getMessage());
				}
			}
			sb.delete(0, sb.length());
		}
		return acslList;
	}

	/**
	 * Uses a regular expression pattern to remove all comment symbols.
	 * 
	 * @param input
	 *            the comment
	 * @return ACSL without comment symbols
	 */
	private String removeCommentSymbols(String input) {
		// the easy case, only a one line comment
		if (input.startsWith("//@")) {
			return input.replaceFirst("//@", "");
		}
		// so this is difficult block comment
		return input.replaceAll(COMMENT_PATTERN, "");
	}

	/**
	 * For the ACSL-Parser we need to know, whether it is a local or a global
	 * comment. We get this with the line numbers of all functions inside the
	 * c-code.
	 * 
	 * @param comment
	 *            the CDT-Comment
	 * @return "lstart" or "gstart" depending on the position
	 */
	private String determineCodePosition(IASTComment comment) {
		int start = comment.getFileLocation().getStartingLineNumber();
		int end = comment.getFileLocation().getEndingLineNumber();
		for (Integer lineStart : this.functionLineRange.keySet()) {
			if (start >= lineStart && end <= this.functionLineRange.get(lineStart)) {
				return "lstart";
			}
		}
		return "gstart";
	}
}
