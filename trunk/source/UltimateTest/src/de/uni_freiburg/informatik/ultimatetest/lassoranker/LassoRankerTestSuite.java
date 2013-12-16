package de.uni_freiburg.informatik.ultimatetest.lassoranker;

import java.io.File;
import java.util.*;

import org.junit.Ignore;

import de.uni_freiburg.informatik.junit_helper.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.Util;
import de.uni_freiburg.informatik.ultimatetest.lassoranker.LassoRankerTestResultDecider.ExpectedResult;


/**
 * Test Suite for the LassoRanker plugin
 * 
 * The Test Suite calls the LassoRanker on all '.bpl'-files found in the
 * directory specified by s_test_files_dir and uses the toolchain
 * s_toolchain.
 * 
 * The files in the test file directory as assumed to be annotated with
 * an expected result value in their first line. The annotation has the
 * form
 * 
 * <pre>
 * //#rExpectedResult
 * </pre>
 * 
 * where ExpectedResult can be one of the following.
 * 
 * <ul>
 * <li> "Ignore" -- do not use this as a test file
 * <li> "Termination" -- example terminates, but LassoRanker may not prove it
 * <li> "TerminationDerivable" -- LassoRanker should prove that this example
 *      terminates
 * <li> "NonTermination" -- example does not terminate, but LassoRanker may
 *      not prove it
 * <li> "NonTerminationDerivable" -- LassoRanker should prove that this example
 *      does not terminate
 * <li> "Unknown" -- termination is unspecified
 * <li> "Error" -- LassoRanker should throw an error when processing this
 *      example
 * </ul>
 * 
 * @see LassoRankerTestResultDecider.ExpectedResult
 * 
 * @author Jan Leike
 */
@Ignore
public class LassoRankerTestSuite extends UltimateTestSuite {
	public static final String s_test_files_dir = "examples/lassos";
	public static final String s_toolchain =
			"examples/toolchains/LassoRanker.xml";
	
	public static final long s_deadline = 100000;
	
	@Override
	@TestFactory
	public Collection<UltimateTestCase> createTestCases() {
		ArrayList<UltimateTestCase> rtr = new ArrayList<UltimateTestCase>();
		ArrayList<File> inputFiles = new ArrayList<File>(getInputFiles());
		Collections.sort(inputFiles);
		
		File toolchainFile = new File(Util.getPathFromTrunk(s_toolchain));
		
		for (File inputFile : inputFiles) {
			UltimateStarter starter = new UltimateStarter(inputFile, null,
					toolchainFile, s_deadline, null, null);
			LassoRankerTestResultDecider decider =
					new LassoRankerTestResultDecider(inputFile);
			if (decider.getExpectedResult() == ExpectedResult.IGNORE) {
				continue;
			}
			rtr.add(new UltimateTestCase(starter, decider,
					inputFile.getName()));
		}
		
		return rtr;
	}
	
	public Collection<File> getInputFiles() {
		return Util.getFiles(
				new File(Util.getPathFromTrunk(s_test_files_dir)),
				new String[] { ".bpl" }
		);
	}
}