/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import org.junit.AfterClass;
import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.INonIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.IPreTestLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestLogfile;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
@RunWith(FactoryTestRunner.class)
public abstract class UltimateTestSuite {

	private List<ITestLogfile> mLogs;
	private ILogger mLogger;

	private Collection<UltimateTestCase> mTestCases;

	/**
	 * Default constructor.
	 */
	public UltimateTestSuite() {
		mLogger = new ConsoleLogger();
		mLogs = new ArrayList<>();
		mLogs.addAll(sanitizeList(this::constructIncrementalLog));
		mLogs.addAll(sanitizeList(this::constructTestSummaries));
		mLogs.addAll(sanitizeList(this::constructPreTestLogs));
	}

	private static <T> List<T> sanitizeList(final Supplier<T[]> funSup) {
		final T[] elems = funSup.get();
		if (elems == null || elems.length == 0) {
			return Collections.emptyList();
		}
		return Arrays.asList(elems).stream().filter(Objects::nonNull).collect(Collectors.toList());
	}

	protected abstract Collection<UltimateTestCase> createTestCases();

	/**
	 * Returns the {@link ITestSummary} instances that produce summaries while running the {@link UltimateTestSuite}.
	 * This method is called only once during each run of an {@link UltimateTestSuite}.
	 */
	protected abstract ITestSummary[] constructTestSummaries();

	protected abstract IIncrementalLog[] constructIncrementalLog();

	protected IPreTestLog[] constructPreTestLogs() {
		return new IPreTestLog[0];
	}

	protected UltimateTestCase buildTestCase(final UltimateRunDefinition urd, final ITestResultDecider decider) {
		return buildTestCase(urd, decider, urd.generateShortStringRepresentation());
	}

	protected UltimateTestCase buildTestCase(final UltimateRunDefinition urd, final ITestResultDecider decider,
			final String name) {
		final UltimateStarter starter = new UltimateStarter(urd);
		return new UltimateTestCase(name, decider, starter, urd, mLogs);
	}

	@TestFactory
	public Collection<UltimateTestCase> getTestCases() {
		if (mTestCases == null) {
			mTestCases = createTestCases();
			writePrelogs();
		}
		return mTestCases;
	}

	@AfterClass
	public final void afterTestSuite() {
		mLogger.info("Writing summaries");
		mLogs.stream().filter(a -> a instanceof ITestSummary).map(a -> (ITestSummary) a)
				.forEach(this::writeNonIncrementalLog);
		mLogs = null;
		mTestCases = null;
		mLogger = null;
	}

	private final void writeNonIncrementalLog(final INonIncrementalLog nonIncrementalLog) {
		try {
			TestUtil.writeNonIncrementalLog(nonIncrementalLog, mLogger);
		} catch (final Throwable ex) {
			mLogger.fatal(String.format("There was an exception during the writing of a summary: %s%n%s%n%s",
					nonIncrementalLog.getClass(), ex, CoreUtil.getStackTrace(ex)));
		}
	}

	private void writePrelogs() {
		mLogger.info("Writing Prelogs");
		final List<IPreTestLog> prelogs = mLogs.stream().filter(a -> a instanceof IPreTestLog).map(a -> (IPreTestLog) a)
				.collect(Collectors.toList());
		final List<UltimateRunDefinition> urds =
				mTestCases.stream().map(UltimateTestCase::getUltimateRunDefinition).collect(Collectors.toList());
		for (final IPreTestLog preLog : prelogs) {
			preLog.addAllTests(urds);
			writeNonIncrementalLog(preLog);
		}
		mLogs.removeAll(prelogs);
		mLogger.info("Finished writing Prelogs");
	}

	public ILogger getLogger() {
		return mLogger;
	}
}
