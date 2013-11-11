package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;

import org.apache.log4j.Logger;
import org.junit.After;
import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.junit_helper.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.junit_helper.testfactory.TestFactory;

@RunWith(FactoryTestRunner.class)
public abstract class UltimateTestSuite {

	private static Collection<ITestSummary> sSummaries;
	protected Logger mLogger;
	private static int sNumberOfTestCasesAlreadyRun;

	public UltimateTestSuite() {
		sSummaries = getSummaries();
		mLogger = Logger.getLogger(UltimateStarter.class);
		sNumberOfTestCasesAlreadyRun = 0;
	}

	@TestFactory
	public abstract Collection<UltimateTestCase> createTestCases();

	/**
	 * Provides a collection of ITestSummary instances. 
	 *  
	 * @return A collection containing ITestSummary instances. They will be
	 *         accessed at the end of this test suite and their content written
	 *         in a file.
	 */
	protected Collection<ITestSummary> getSummaries(){
		if(sSummaries == null){
			sSummaries = new ArrayList<ITestSummary>();
		}
		return sSummaries;
	}

	protected abstract int getTotalNumerOfTestCases();

	@After
	public final void writeSummaries() {
		sNumberOfTestCasesAlreadyRun++;
		if (sNumberOfTestCasesAlreadyRun < getTotalNumerOfTestCases()) {
			return;
		}
		
		if (sSummaries == null || sSummaries.size() == 0) {
			return;
		}

		for (ITestSummary summary : sSummaries) {
			writeSummary(summary);
		}
		
		sNumberOfTestCasesAlreadyRun = 0;
		sSummaries = null;
	}

	private void writeSummary(ITestSummary summary) {
		File summaryLogFile = summary.getSummaryLogFile();

		File logFile = new File(Util.getPathFromSurefire(summaryLogFile
				.getName()));

		if (!logFile.isDirectory()) {
			logFile.getParentFile().mkdirs();
		}

		String summaryLog = summary.getSummaryLog();
		if (summaryLog == null || summaryLog.isEmpty()) {
			return;
		}

		try {
			FileWriter fw = new FileWriter(logFile);
			mLogger.info("Writing summary for "
					+ this.getClass().getCanonicalName() + " to "
					+ logFile.getAbsolutePath());
			fw.write(summaryLog);
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

}
