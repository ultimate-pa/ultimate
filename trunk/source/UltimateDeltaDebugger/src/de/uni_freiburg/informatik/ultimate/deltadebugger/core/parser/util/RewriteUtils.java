package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.ToolFactory;
import org.eclipse.cdt.core.formatter.CodeFormatter;
import org.eclipse.cdt.core.formatter.DefaultCodeFormatterConstants;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;

/**
 * Contains
 *
 */
public final class RewriteUtils {
	private static final int MAX_PRETTY_PRINTED_LENGTH = 10_000; 

	private RewriteUtils() {
	}
	
	/**
	 * Pretty print source code using the CDT code formatter. Seems to work without workspace and/or OSGi, but can cause
	 * extreme lags/freezes for larger inputs.
	 *
	 * Maybe this should be removed by something that removes redundant whitespace.
	 *
	 * @param input
	 *            source code
	 * @return pretty printed source code
	 */
	public static String debugPrettyPrintSourceCode(final String input) {
		// The formatter can be ridiculously slow for large inputs (possible
		// related to deeply nested expressions).
		// This is just a hack that reduces the chance to freeze.
		if (input.length() > MAX_PRETTY_PRINTED_LENGTH) {
			return removeMultipleEmptyLines(input);
		}

		final Map<String, String> options = DefaultCodeFormatterConstants.getDefaultSettings();
		final CodeFormatter formatter = ToolFactory.createDefaultCodeFormatter(options);
		final TextEdit edits = formatter.format(CodeFormatter.K_TRANSLATION_UNIT, input, 0, input.length(), 0, null);
		final IDocument doc = new Document(input);
		try {
			edits.apply(doc);
			return doc.get().replace("\t", "    ");
		} catch (MalformedTreeException | BadLocationException e) {
			return input;
		}
	}

	/**
	 * Deleting certain nodes from the source text may require a replacement with a whitespace to ensure that no
	 * enclosing tokens are joined.
	 *
	 * @param node
	 * @return
	 */
	public static String getDeletionStringWithWhitespaces(final IPSTNode node) {
		// Deleteing comments and (function style) macro expansions
		// completely can cause problems if there are no whitespaces
		// to the left or right and tokens are joined.
		if (node instanceof IPSTComment || node instanceof IPSTMacroExpansion) {
			return " ";
		}
		// Not sure if there are other cases where a whitespace is required,
		// just use a space anywhere for now.
		return " ";
	}

	public static String removeMultipleEmptyLines(final String input) {
		return input.replaceAll("(?m)^(\\s*\r?\n){2,}", "\n");
	}

	/**
	 * Checks if the given replacement string is the same as the existing source text and would not have any effect.
	 *
	 * @param node node
	 * @param replacementString replacementString
	 * @return if replacement by the given string should be skipped
	 */
	public static boolean skipEquivalentReplacement(final IPSTNode node, final String replacementString) {
		// Do not replace something by itself
		// It would be better to compare tokens, but we can at least ignore
		// differences in whitespaces
		final String lhs = node.getSourceText().replaceAll("\\s+", " ");
		final String rhs = replacementString.replaceAll("\\s+", " ");
		return lhs.equals(rhs);
	}

	/**
	 * If any replacement already matches the current source text, skip ALL the other alternatives, not just the one
	 * that matches. This is important to not endlessly switch between two alternatives that are both possible in
	 * repeated HDD aplications.
	 * 
	 * @param node
	 *            PST node to be replacement
	 * @param replacementStrings
	 *            list of replacements to be tested in the given order
	 * @return list of valid replacement strings
	 */
	public static List<String> removeEquivalentReplacements(final IPSTNode node, final List<String> replacementStrings) {
		final List<String> validReplacements = new ArrayList<>();
		for (String replacement : replacementStrings) {
			if (RewriteUtils.skipEquivalentReplacement(node, replacement)) {
				break;
			}
			validReplacements.add(replacement);
		}
		return validReplacements;
	}

}
