package de.uni_freiburg.informatik.ultimatetest.suites.translation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.TranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.TranslationTestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

public abstract class AbstractCTranslationTestSuite extends UltimateTestSuite {

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		ArrayList<UltimateTestCase> rtr = new ArrayList<UltimateTestCase>();

		// get a set of input files

		Collection<File> inputFiles = getInputFiles();
		File settingsFile = getSettings();

		File toolchainFile = new File(TestUtil.getPathFromTrunk("examples/toolchains/CTranslationTest.xml"));
		long deadline = 10000;

		for (File inputFile : inputFiles) {
			UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, toolchainFile);
			UltimateStarter starter = new UltimateStarter(urd, deadline, null, null);
			rtr.add(new UltimateTestCase(inputFile.getAbsolutePath(), new TranslationTestResultDecider(inputFile
					.getAbsolutePath()), starter, urd, super.getSummaries(), null));
		}

		return rtr;
	}

	public abstract Collection<File> getInputFiles();

	public File getSettings() {
		return null;
	}
	
	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] {
				new TranslationTestSummary(this.getClass())
		};
	}
	
	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[0];
	}
}
