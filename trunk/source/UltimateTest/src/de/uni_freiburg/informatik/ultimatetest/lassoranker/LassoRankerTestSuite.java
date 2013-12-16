package de.uni_freiburg.informatik.ultimatetest.lassoranker;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.junit_helper.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.Util;


/**
 * Test Suite for the LassoRanker plugin
 * 
 * @author Jan Leike
 */
public class LassoRankerTestSuite extends UltimateTestSuite {
	public static final String s_test_files_dir = "examples/lassos";
	public static final String s_toolchain = "examples/toolchains/LassoRanker.xml";
	
	public static final long s_deadline = 100;
	
	@Override
	@TestFactory
	public Collection<UltimateTestCase> createTestCases() {
		ArrayList<UltimateTestCase> rtr = new ArrayList<UltimateTestCase>();
		
		Collection<File> inputFiles = getInputFiles();
		
		File toolchainFile = new File(Util.getPathFromTrunk(s_toolchain));
		
		for (File inputFile : inputFiles) {
			UltimateStarter starter = new UltimateStarter(inputFile, null,
					toolchainFile, s_deadline, null, null);
			rtr.add(new UltimateTestCase(starter,
					new LassoRankerTestResultDecider(inputFile),
					inputFile.getName()
			));
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