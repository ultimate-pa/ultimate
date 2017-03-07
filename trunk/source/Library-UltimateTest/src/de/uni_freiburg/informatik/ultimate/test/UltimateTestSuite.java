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
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
@RunWith(FactoryTestRunner.class)
public abstract class UltimateTestSuite {

	private List<ITestSummary> mSummaries;
	private final List<IIncrementalLog> mLogFiles;
	private final ILogger mLogger;

	/**
	 * Default constructor.
	 */
	public UltimateTestSuite() {
		mLogger = new ConsoleLogger();
		mSummaries = sanitizeList(this::constructTestSummaries);
		mLogFiles = sanitizeList(this::constructIncrementalLog);
	}

	private static <T> List<T> sanitizeList(final Supplier<T[]> funSup) {
		final T[] summaries = funSup.get();
		if (summaries == null) {
			return Collections.emptyList();
		}
		return Arrays.asList(summaries).stream().filter(Objects::nonNull).collect(Collectors.toList());
	}

	@TestFactory
	public abstract Collection<UltimateTestCase> createTestCases();

	/**
	 * Returns the ITestSummaries instances that produce summaries while running the UltimateTestSuite. This method is
	 * called only once during each run of an UltimateTestSuite.
	 */
	protected abstract ITestSummary[] constructTestSummaries();

	protected abstract IIncrementalLog[] constructIncrementalLog();

	/**
	 * Provides a collection of ITestSummary instances.
	 * 
	 * @return A collection containing ITestSummary instances. They will be accessed at the end of this test suite and
	 *         their content written in a file.
	 */
	protected List<ITestSummary> getSummaries() {
		return Collections.unmodifiableList(mSummaries);
	}

	protected List<IIncrementalLog> getIncrementalLogs() {
		return Collections.unmodifiableList(mLogFiles);
	}

	@AfterClass
	public final void writeSummaries() {
		final ILogger log = new ConsoleLogger();
		if (mSummaries == null || mSummaries.isEmpty()) {
			log.info("No test summaries available");
			return;
		}

		for (final ITestSummary summary : mSummaries) {
			try {
				TestUtil.writeSummary(summary, log);
			} catch (final Exception ex) {
				ex.printStackTrace();
			}
		}
		mSummaries = null;
	}

	public ILogger getLogger() {
		return mLogger;
	}
}
