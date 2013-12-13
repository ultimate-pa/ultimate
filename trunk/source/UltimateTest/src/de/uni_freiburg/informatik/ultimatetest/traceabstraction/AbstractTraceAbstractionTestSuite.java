package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.Util;

public abstract class AbstractTraceAbstractionTestSuite extends UltimateTestSuite {

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		ArrayList<UltimateTestCase> rtr = new ArrayList<UltimateTestCase>();

		// get a set of input files
		Collection<File> inputFiles = getInputFiles();

		File toolchainFile = new File(
				Util.getPathFromTrunk("examples/toolchains/TraceAbstraction.xml"));
		// (musab): It seems to be that the deadline is not respected.
		long deadline = 1;

		for (File inputFile : inputFiles) {

			UltimateStarter starter = new UltimateStarter(inputFile, null,
					toolchainFile, deadline, null, null);
			rtr.add(new UltimateTestCase(starter,
					new TraceAbstractionTestResultDecider(inputFile.getAbsolutePath()), inputFile
							.getAbsolutePath()));
		}

		return rtr;

	}
	
	public abstract Collection<File> getInputFiles();
}
