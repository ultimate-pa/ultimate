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

import org.eclipse.cdt.core.dom.ast.IASTComment;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieTranslator;

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

    /**
     * The Constructor.
     * 
     * @param comments
     *            commentList
     * @param lineRange
     *            Map with line ranges of functions. Can be determined with
     *            FunctionLineVisitor.
     */
    public CommentParser(IASTComment[] comments,
            HashMap<Integer, Integer> lineRange) {
        this.commentList = comments;
        this.functionLineRange = lineRange;
        this.pattern = Pattern.compile(ACSL_PATTERN, Pattern.DOTALL);
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
                        if (CACSL2BoogieTranslator.s_Logger != null) {
                            // might throw an exception
                        }
                        acslNode = Parser.parseComment(input.toString(),
                                comment.getFileLocation()
                                        .getStartingLineNumber(), comment
                                        .getFileLocation()
                                        .getEndingLineNumber(),
                                CACSL2BoogieTranslator.s_Logger);
                    } catch (ExceptionInInitializerError e) { // ignore
                    } catch (NoClassDefFoundError e) { // ignore
                    } finally {
                        acslNode = Parser.parseComment(input.toString(),
                                comment.getFileLocation()
                                        .getStartingLineNumber(), comment
                                        .getFileLocation()
                                        .getEndingLineNumber());
                    }
                    if (acslNode != null) {
                        acslNode.setFileName(comment.getContainingFilename());
                        acslList.add(acslNode);
                    }
                } catch (ACSLSyntaxErrorException e) {
                    ACSLNode node = e.getLocation();
                    node.setFileName(comment.getFileLocation().getFileName());
                    ILocation loc = new CACSLLocation(node);
                    Dispatcher.syntaxError(loc, e.getMessageText());
                } catch (Exception e) {
                    throw new IllegalArgumentException(
                            "Exception should be cached: " + e.getMessage());
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
            if (start >= lineStart
                    && end <= this.functionLineRange.get(lineStart)) {
                return "lstart";
            }
        }
        return "gstart";
    }
}
