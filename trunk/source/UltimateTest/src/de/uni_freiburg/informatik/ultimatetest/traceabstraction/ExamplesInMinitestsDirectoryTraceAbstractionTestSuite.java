/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import org.junit.Ignore;
import org.junit.rules.Timeout;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */

public class ExamplesInMinitestsDirectoryTraceAbstractionTestSuite extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = { "examples/programs/regression//" };
	// private static final String m_excludeFilesFromDir = "examples/programs/minitests/openbugs/";
	
	private static final boolean m_TraceAbstractionWithBackwardPredicates = !false;
	private static final boolean m_TraceAbstractionWithForwardPredicates = !false;
	private static final boolean m_TraceAbstractionCWithBackwardPredicates = true;
	private static final boolean m_TraceAbstractionCWithForwardPredicates = true;		
	// Time out for each test case in milliseconds
	private final static int m_Timeout = 10000;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_TraceAbstractionWithForwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"traceAbstractionTestSuite/settingsForwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    "Trace Abstraction",
				    "BoogieFilesForwardPredicates",
				    m_Timeout);
		} 
		if (m_TraceAbstractionWithBackwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"traceAbstractionTestSuite/settingsBackwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"},
				    "Trace Abstraction",
				    "BoogieFilesBackwardPredicates",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithForwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"traceAbstractionTestSuite/settingsForwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    "Trace Abstraction",
				    "CFilesForwardPredicates",
				    m_Timeout);
		}
		if (m_TraceAbstractionCWithBackwardPredicates) {
			addTestCases(
					"AutomizerC.xml",
					"traceAbstractionTestSuite/settingsBackwardPredicates.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
				    "Trace Abstraction",
				    "CFilesBackwardPredicates",
				    m_Timeout);
		}
		return super.createTestCases();
	}

	
}
