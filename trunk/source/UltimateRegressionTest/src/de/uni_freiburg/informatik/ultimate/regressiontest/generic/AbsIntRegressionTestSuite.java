/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.regressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.OverapproximatingSafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * This test suite tests the AbstractInterpretation plugin of Ultimate.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntRegressionTestSuite extends AbstractRegressionTestSuite {

	private static final long DEFAULT_TIMEOUT = 20 * 1000L;

	public AbsIntRegressionTestSuite() {
		super();
		mTimeout = DEFAULT_TIMEOUT;
		mRootFolder = TestUtil.getPathFromTrunk("examples/programs/abstractInterpretation/");
		mFiletypesToConsider = new String[] { ".bpl" };
		// mExcludeFilterRegex = ".*((open)|(oct)|(non_taipan)|(non_con)|(all)).*";
	}

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition runDefinition) {
		return new OverapproximatingSafetyCheckTestResultDecider(runDefinition, true);
	}
}
