/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.buchiautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TimingBenchmark;
import de.uni_freiburg.informatik.ultimatetest.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.summary.CsvConcatenator;
import de.uni_freiburg.informatik.ultimatetest.summary.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.traceabstraction.TestSummaryWithBenchmarkResults;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiAutomizerTemplateBenchmarkMode extends
		AbstractBuchiAutomizerTestSuite {
	private static final String[] m_Directories = {
//		"examples/lassos",
//		"examples/termination/TermCompOfficialBenchmarkSet",
		"examples/termination/TermCompOfficialBenchmarkSet/ultimate",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
//		"examples/termination/AProVE"
	};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 120 * 1000;

	private static String s_LargeBlockEncoding = "buchiAutomizer/templateBenchmarkLBE.epf";
	private static String s_MediumBlockEncoding = "buchiAutomizer/templateBenchmarkBE.epf";
	
	private static String s_Setting = s_LargeBlockEncoding;
	
	
	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] {
				new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TerminationAnalysisBenchmark.class),
				new CsvConcatenator(this.getClass(), TimingBenchmark.class),
		};
	}
	
	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { new TestSummaryWithBenchmarkResults(this.getClass()) };
	}
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCases(
			"BuchiAutomizerBplWithBlockEncoding.xml",
			s_Setting,
		    m_Directories,
		    new String[] {".bpl"},
		    m_Timeout);
		addTestCases(
			"BuchiAutomizerCWithBlockEncoding.xml",
			s_Setting,
			m_Directories,
			new String[] {".c"},
			m_Timeout);
		return super.createTestCases();
	}
}
