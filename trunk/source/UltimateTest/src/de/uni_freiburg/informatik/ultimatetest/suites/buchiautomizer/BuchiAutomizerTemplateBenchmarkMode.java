/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.buchiautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.reporting.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.logs.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimatetest.summaries.TraceAbstractionTestSummary;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiAutomizerTemplateBenchmarkMode extends
		AbstractBuchiAutomizerTestSuite {
	private static final String[] mDirectories = {
//		"examples/lassos",
//		"examples/termination/TermCompOfficialBenchmarkSet",
		"examples/termination/TermCompOfficialBenchmarkSet/ultimate",
//		"examples/programs/quantifier",
//		"examples/programs/recursive/regression",
//		"examples/programs/toy"
//		"examples/termination/AProVE"
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 120 * 1000;
	}


	private static String s_LargeBlockEncoding = "buchiAutomizer/templateBenchmarkLBE.epf";
	private static String s_MediumBlockEncoding = "buchiAutomizer/templateBenchmarkBE.epf";
	
	private static String s_Setting = s_LargeBlockEncoding;
	
	
	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] {
				new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TerminationAnalysisBenchmark.class),
				new CsvConcatenator(this.getClass(), BuchiAutomizerTimingBenchmark.class),
		};
	}
	
	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { new IncrementalLogWithBenchmarkResults(this.getClass()) };
	}
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCase(
			"BuchiAutomizerBplWithBlockEncoding.xml",
			s_Setting,
		    mDirectories,
		    new String[] {".bpl"});
		addTestCase(
			"BuchiAutomizerCWithBlockEncoding.xml",
			s_Setting,
			mDirectories,
			new String[] {".c"});
		return super.createTestCases();
	}
}
