/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * Test for the different versions of incremental inclusion.
 * Run this as a "JUnit Plug-in Test".
 * The results will be written to the following folder.
 * trunk/source/UltimateTest/target/surefire-reports/de.uni_freiburg.informatik.ultimatetest.traceabstraction.IncrementalInclusionTest
 * 
 * Please remember to use "-ea" as VM argument for testing (because bugs will be
 * found earlier).
 * Please do not use "-ea" as VM argument for benchmarking (because settings with
 * a lot of assert statements will have a disadvantage)
 * @author heizmanninformatik.uni-freiburg.de
 *
 */

public class IncrementalInclusionTest extends
		AbstractTraceAbstractionTestSuite {
	/**
	 * List of path. Ultimate will be run for each program that you find in
	 * one of there paths.
	 */
	private static final String[] m_Programs = {
//		"examples/programs/regression",
//		"examples/programs/quantifier/",
//		"examples/programs/quantifier/regression",
//		"examples/programs/toy",
		"examples/programs/random",
//		"examples/programs/scaleable",
//		"examples/programs/real-life",
	};
	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] m_Settings = {
//		"automizer/incrementalInclusion/Difference.epf",
//		"automizer/incrementalInclusion/IncrementalInclusionViaDifference.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion2.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion3.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion3_2.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion4.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion4_2.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion5.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion5_2.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/Difference.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/IncrementalInclusionViaDifference.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/IncrementalInclusion2.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/IncrementalInclusion3.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/IncrementalInclusion3_2.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/IncrementalInclusion4.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/IncrementalInclusion4_2.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/IncrementalInclusion5.epf",
		"automizer/incrementalInclusion/noDeadEndsRemoval/IncrementalInclusion5_2.epf",
	};
	
	/**
	 * If set to true, files with the ending .bpl are taken into account,
	 * otherwise files with this ending are ignored.
	 */
	private static final boolean m_Boogie = true;
	/**
	 * If set to true, files with the ending .c and .i are taken into account,
	 * otherwise files with this ending are ignored.
	 */
	private static final boolean m_C = !true;

	/**
	 * Time out for each test case in milliseconds.
	 * This will override the timeout that is specified in the settings files.
	 */
	private final static int m_Timeout = 10 * 1000;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			if (m_Boogie) {
				addTestCases(
						"AutomizerBpl.xml",
						setting,
						m_Programs,
						new String[] {".bpl"},
						m_Timeout);
			}
			if (m_C) {
				addTestCases(
						"AutomizerC.xml",
						setting,
						m_Programs,
						new String[] {".c", ".i"},
						m_Timeout);
			}
		}
		return super.createTestCases();
	}

	
}
