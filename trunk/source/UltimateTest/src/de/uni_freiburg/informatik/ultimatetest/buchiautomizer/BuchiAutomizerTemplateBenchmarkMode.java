/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.buchiautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.LassoTerminationAnalysisBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TimingBenchmark;
import de.uni_freiburg.informatik.ultimatetest.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.summary.CsvConcatenator;
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
		"examples/termination/TermCompOfficialBenchmarkSet/ultimate"
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
//		"examples/termination/AProVE"
	};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 120000;

//	private static final boolean s_Boogie_TreeInterpolants = true;
//	private static final boolean s_C_TreeInterpolants = true;
	
	
	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] {
				new TestSummaryWithBenchmarkResults(this.getClass()),
				new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), LassoTerminationAnalysisBenchmarks.class),
				new CsvConcatenator(this.getClass(), TimingBenchmark.class),
		};
	}
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCases(
			"BuchiAutomizerBplWithBlockEncoding.xml",
			"buchiAutomizer/templateBenchmarkLBE.epf",
		    m_Directories,
		    new String[] {".bpl"},
		    m_Timeout);
		addTestCases(
				"BuchiAutomizerCWithBlockEncoding.xml",
				"buchiAutomizer/templateBenchmarkLBE.epf",
			    m_Directories,
			    new String[] {".c"},
			    m_Timeout);
		return super.createTestCases();
	}
}
