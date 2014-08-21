package de.uni_freiburg.informatik.ultimatetest.lassoranker;

import java.io.File;
import java.util.*;

import de.uni_freiburg.informatik.junit_helper.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.lassoranker.LassoRankerTestResultDecider.ExpectedResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;


/**
 * Test Suite for the LassoRanker plugin
 * 
 * The Test Suite calls the LassoRanker on all '.bpl'-files found in the
 * directory specified by s_test_files_dir and uses the toolchain s_toolchain.
 * 
 * The files in the test file directory as assumed to be annotated with an
 * expected result value in their first line. The annotation has the form
 * 
 * <pre>
 * // #rExpectedResult
 * </pre>
 * 
 * where ExpectedResult can be one of the following.
 * 
 * <ul>
 * <li>"Ignore" -- do not use this as a test file
 * <li>"Termination" -- example terminates, but LassoRanker may not prove it
 * <li>"TerminationDerivable" -- LassoRanker should prove that this example
 * terminates
 * <li>"NonTermination" -- example does not terminate, but LassoRanker may not
 * prove it
 * <li>"NonTerminationDerivable" -- LassoRanker should prove that this example
 * does not terminate
 * <li>"Unknown" -- termination is unspecified
 * <li>"Error" -- LassoRanker should throw an error when processing this example
 * </ul>
 * 
 * @see LassoRankerTestResultDecider.ExpectedResult
 * 
 * @author Jan Leike
 */
public class LassoRankerTestSuite extends UltimateTestSuite {
	public static final String s_test_files_dir = "examples/lassos/";
	public static final String s_toolchain = "examples/toolchains/LassoRanker.xml";
//  Workaround by Matthias: Use following line for linear constraints
//	public static final String s_settings_file = "examples/settings/LassoRankerTestLinearSMTInterpol.epf";
//  Workaround by Matthias: Use following line for non-linear constraints
	public static final String s_settings_file = "examples/settings/LassoRankerTest.epf";
	public static final boolean s_produceLogFiles = false;

	public static final long s_deadline = 5 * 1000; // in ms

	@Override
	@TestFactory
	public Collection<UltimateTestCase> createTestCases() {
		ArrayList<UltimateTestCase> rtr = new ArrayList<UltimateTestCase>();
		ArrayList<File> inputFiles = new ArrayList<File>(getInputFiles());
		Collections.sort(inputFiles);
		
		File toolchainFile = new File(Util.getPathFromTrunk(s_toolchain));
		File settingsFile = new File(Util.getPathFromTrunk(s_settings_file));
		String logPattern = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN);
		for (File inputFile : inputFiles) {
			UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, toolchainFile);
			UltimateStarter starter = new UltimateStarter(
					urd,
					s_deadline,
					s_produceLogFiles ? new File(Util.generateLogFilename(
							inputFile, "LassoRanker")) : null,
					s_produceLogFiles ? logPattern : null);
			LassoRankerTestResultDecider decider = new LassoRankerTestResultDecider(
					inputFile);
			if (decider.getExpectedResult() == ExpectedResult.IGNORE) {
				continue;
			}
			rtr.add(new UltimateTestCase(starter, decider, null, inputFile.getName(), urd));
		}

		return rtr;
	}

	public Collection<File> getInputFiles() {
		return Util.getFiles(new File(Util.getPathFromTrunk(s_test_files_dir)),
				new String[] { ".bpl" });
	}
}