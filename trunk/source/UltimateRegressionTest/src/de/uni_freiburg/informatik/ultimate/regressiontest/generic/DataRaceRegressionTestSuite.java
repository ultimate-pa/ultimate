/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.regressiontest.generic;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.regressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class DataRaceRegressionTestSuite extends AbstractRegressionTestSuite {

	private static final int TIMEOUT = 20_000;
	private static final String ROOT_DIR = TestUtil.getPathFromTrunk("examples/concurrent/pthreads/races");
	private static final String FILE_ENDING = ".c";

	private final Map<Pair<String, String>, Long> mSpecialTimeouts = new HashMap<>();

	public DataRaceRegressionTestSuite() {
		super();
		mTimeout = TIMEOUT;
		mRootFolder = ROOT_DIR;
		mFiletypesToConsider = new String[] { FILE_ENDING };

		mSpecialTimeouts.put(new Pair<>("DataRace-32bit-Automizer_Bitvector.epf", "static-array-copy3.c"), 250_000L);
		mSpecialTimeouts.put(new Pair<>("DataRace-32bit-Automizer_Default.epf", "static-array-copy3.c"), 40_000L);
	}

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition runDefinition) {
		return new SafetyCheckTestResultDecider(runDefinition, false);
	}

	@Override
	protected long getTimeout(final Config config, final File file) {
		final var pair = new Pair<>(config.getSettingsFile().getName(), file.getName());
		final var timeout = mSpecialTimeouts.get(pair);
		if (timeout != null) {
			return timeout;
		}
		return super.getTimeout(config, file);
	}
}
