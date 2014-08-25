/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util.ExpectedResult;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationTestResultDecider extends
		SafetyCheckTestResultDecider {
	
	private final boolean m_logAsLaTeXTable;

	/**
	 * @param inputFile
	 */
	public AbstractInterpretationTestResultDecider(File inputFile, boolean logAsLaTeXTable) {
		super(inputFile);
		m_logAsLaTeXTable = logAsLaTeXTable;
	}

	/**
	 * Message: Symbol for the LaTeX table denoting the expected result.
	 */
	protected void generateResultMessageAndCategory(SafetyCheckerResult safetyCheckerResult) {
		if (m_logAsLaTeXTable) {
			if (safetyCheckerResult == null) {
				setResultMessage("--");
				setResultCategory("Null");
				return;
			}
			if ((safetyCheckerResult.getAutomizerResultType() == SafetyCheckerResultType.EXCEPTION_OR_ERROR)
					|| (getExpectedResult() == ExpectedResult.NOANNOTATION)) {
				setResultMessage("--");
			} else {
				setResultMessage(expectedResultTag(getExpectedResult()));
			}
	
			setResultCategory(automizerResultCategoryTag(safetyCheckerResult.getAutomizerResultType()));
		} else {
			super.generateResultMessageAndCategory(safetyCheckerResult);
		}
	}

	
	private String automizerResultCategoryTag(SafetyCheckerResultType result) {
		switch (result) {
		case SAFE :
			return "Safe";
		case UNKNOWN :
			return "Unknown";
		case UNSAFE :
			return "Unsafe";
		case SYNTAX_ERROR :
			return "Syntax error";
		case TIMEOUT :
			return "Timeout";
		case UNSUPPORTED_SYNTAX :
			return "Unsupported syntax";
		case EXCEPTION_OR_ERROR :
			return "Exception or error";
		case NO_RESULT :
			return "No result";
		default :
			return "---";
		}
	}
	
	private String expectedResultTag(ExpectedResult result) {
		switch (result) {
		case SAFE :
			return "$\\checkmark$";
		case UNSAFE :
		case SYNTAXERROR :
			return "$\\times$";
		case NOANNOTATION :
			return "?";
		default :
			return "--";
		}
	}

}
