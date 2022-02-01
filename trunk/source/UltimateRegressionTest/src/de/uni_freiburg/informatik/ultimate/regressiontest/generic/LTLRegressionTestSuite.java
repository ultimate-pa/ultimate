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
import de.uni_freiburg.informatik.ultimate.test.decider.LTLCheckerTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * Regression tests for LTL Automizer.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public class LTLRegressionTestSuite extends AbstractRegressionTestSuite {

	private static final int TIMEOUT = 60_000;

	public LTLRegressionTestSuite() {
		super();
		mTimeout = TIMEOUT;
		mRootFolder = TestUtil.getPathFromTrunk("examples/LTL/");
	}

	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition runDefinition) {
		return new LTLCheckerTestResultDecider(runDefinition, false);
	}

}
