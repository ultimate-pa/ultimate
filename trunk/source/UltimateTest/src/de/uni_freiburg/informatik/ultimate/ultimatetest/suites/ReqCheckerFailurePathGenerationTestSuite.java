/*
 * Copyright (C) 2020 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Regression Test Library.
 *
 * The ULTIMATE Regression Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Regression Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Regression Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Regression Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Regression Test Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.Formatter;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.srparse.PatternUtil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.NoErrorTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Regression tests for Requirements Checker.
 *
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class ReqCheckerFailurePathGenerationTestSuite extends AbstractEvalTestSuite {

	@Override
	protected long getTimeout() {
		return 10_000;
	}

	private static final String[] REQ = new String[] { ".req" };

	private static final String TOOLCHAIN = "ReqCheckFailurePathGeneration.xml";
	private static final String SETTINGS = "ReqCheckFailurePathGeneration.epf";
	private static final String REQ_DIR = "examples/Requirements/regression/failure-paths";

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new NoErrorTestResultDecider(ultimateRunDefinition);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		createReqFiles(PatternUtil.createAllPatterns().getFirst());
		final DirectoryFileEndingsPair[] pairs =
				new DirectoryFileEndingsPair[] { new DirectoryFileEndingsPair(REQ_DIR, REQ) };

		addTestCase(TOOLCHAIN, SETTINGS, pairs);
		return super.createTestCases();
	}

	private static void createReqFiles(final List<PatternType> patterns) {
		for (final PatternType pattern : patterns) {
			final String scopeName = pattern.getScope().getClass().getSimpleName()
					.replace(pattern.getScope().getClass().getSuperclass().getSimpleName(), "");
			final String patternName = pattern.getClass().getSimpleName();
			final String patternString = pattern.toString().replace(pattern.getId() + ": ", "");

			final StringBuilder sb = new StringBuilder();
			final Formatter fmt = new Formatter(sb);
			fmt.format("// %s %s%s", patternName, scopeName, CoreUtil.getPlatformLineSeparator());
			for (int i = 0; i < 10; ++i) {
				fmt.format("INPUT %s is bool%s", BooleanDecision.create(CoreUtil.alphabeticalSequence(i + 16)),
						CoreUtil.getPlatformLineSeparator());
			}
			fmt.format("req1: %s%s", patternString, CoreUtil.getPlatformLineSeparator());
			fmt.close();

			final File file =
					new File(TestUtil.getPathFromTrunk(REQ_DIR) + "/" + patternName + "_" + scopeName + ".req");
			try {
				final BufferedWriter writer = new BufferedWriter(new FileWriter(file, false));
				writer.write(sb.toString());
				writer.close();
			} catch (final IOException e) {
				throw new RuntimeException("Unable to write file '" + file + "'.");
			}
		}
	}

}
