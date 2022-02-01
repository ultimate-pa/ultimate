/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.reporting;

import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;

/**
 * This interface describes test summaries that can be used to create a summary log file of the results of a whole test
 * suite.
 * 
 * As our test suites have typically a lot of tests, it can be convenient to write a summary file to see which test
 * failed why and group the tests according to some criteria. This interface describes classes that can be used to do
 * this.
 * 
 * Note that summaries are only written <b>after</b> a whole test suite completed. This means it may take several hours
 * before you can have a look at the summary. If you want information after each test case, consider
 * {@link IIncrementalLog}.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public interface ITestSummary extends INonIncrementalLog {

	/**
	 * This method is called after the execution of each {@link UltimateTestCase} and reports the result to the
	 * {@link ITestSummary} instance of the active {@link UltimateTestSuite test suite}.
	 * 
	 * @param ultimateRunDefinition
	 *            Input file, settings file and toolchain file.
	 * @param threeValuedResult
	 *            The actual result of the test case.
	 * @param category
	 *            The category of this test result as specified by {@link ITestResultDecider#getResultCategory()}
	 * @param message
	 *            A message for this specific result and this specific input file as specified by
	 *            {@link ITestResultDecider#getResultMessage()}
	 * @param testname
	 *            Name of the test for which the result was produced
	 * @param resultService
	 *            All IResults produced during the run of Ultimate. The results are given as a map which maps plugin IDs
	 *            to a the list of results produced by that plugin. May be null if Ultimate failed early.
	 * 
	 */
	void addResult(UltimateRunDefinition ultimateRunDefinition, TestResult threeValuedResult, String category,
			String message, String testname, IResultService resultService);
}
