/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.regressiontest.translation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.regressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.TranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

public class LTLTranslationRegressionTestSuite extends AbstractRegressionTestSuite {

	private static final int TIMEOUT = 10_000;

	public LTLTranslationRegressionTestSuite() {
		mTimeout = TIMEOUT;
		mFiletypesToConsider = new String[] { ".c" };
	}

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition runDefinition) {
		return new TranslationTestResultDecider(runDefinition.selectPrimaryInputFile());
	}

	@Override
	protected Collection<Pair> getRunConfiguration(final Predicate<File> regexFilter) {
		final List<Pair> rtr = new ArrayList<>();

		rtr.add(getPair("examples/toolchains/LtlTranslationC.xml", "examples/settings/ltlAutomizer/Default.epf"));

		return rtr;
	}

	@Override
	protected Collection<File> getInputFiles(final Predicate<File> regexFilter, final Pair runConfiguration) {
		return TestUtil.getFiles(getPathFromTrunk("examples/LTL/rers2012/"), mFiletypesToConsider);
	}

	private static Pair getPair(final String toolchain, final String setting) {
		return new Pair(getPathFromTrunk(toolchain), getPathFromTrunk(setting));
	}

	private static File getPathFromTrunk(final String path) {
		return new File(TestUtil.getPathFromTrunk(path));
	}

}
