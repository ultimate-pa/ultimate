package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.TestFileInterpreter.LoggerSeverity;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

interface IMessagePrinter {
	/**
	 * Reports the given string to the logger and to Ultimate as a
	 * GenericResult.
	 * 
	 * @param sev
	 *            the Severity
	 * @param longDescr
	 *            the string to be reported
	 * @param node
	 *            AtsASTNode for which this String is reported
	 */
	public void printMessage(Severity severityForResult, LoggerSeverity severityForLogger, String longDescr,
			String shortDescr, AtsASTNode node);
}
