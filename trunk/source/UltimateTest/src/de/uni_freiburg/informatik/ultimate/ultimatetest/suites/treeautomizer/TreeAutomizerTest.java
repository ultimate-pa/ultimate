package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.treeautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;

public class TreeAutomizerTest extends UltimateTestSuite {


//	private static final String[] ULTIMATE_EXAMPLES = {
//		"examples/smtlib/horn",
//	};
//
//	/**
//	 * List of path to setting files.
//	 * Ultimate will run on each program with each setting that is defined here.
//	 * The path are defined relative to the folder "trunk/examples/settings/",
//	 * because we assume that all settings files are in this folder.
//	 *
//	 */
//	private static final String[] SETTINGS = {
//		"EmptySettings.epf",
//	};
//
//
//	private static final String[] ATS_TOOLCHAINS = {
//		"TreeAutomizer.xml",
//	};


//	@Override
//	protected ColumnDefinition[] getColumnDefinitions() {
//		return new ColumnDefinition[0];
//	}
//	@Override
//	protected long getTimeout() {
//		return 10 * 1000;
//	}

//	@Override
//	public Collection<UltimateTestCase> createTestCases() {
//		for (final String setting : SETTINGS) {
//			for (final String toolchain : ATS_TOOLCHAINS) {
//				addTestCase(toolchain, setting, ULTIMATE_EXAMPLES, new String[] { ".smt2" });
//			}
//		}
//		return super.createTestCases();
//	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	protected Collection<UltimateTestCase> createTestCases() {
		// TODO Auto-generated method stub
		return null;
	}
}
