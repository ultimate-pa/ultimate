/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitSubSet;

public class VariableAbstractionTest extends AbstractAbstractionTestSuite<BitSubSet<IProgramVar>> {

	private BitSubSet.Factory<IProgramVar> mFactory;

	@Override
	protected IAbstraction<BitSubSet<IProgramVar>, BasicInternalAction> createAbstraction() {
		final Set<IProgramVar> allVariables = new HashSet<>(mSymbolTable.getGlobals());
		mFactory = new BitSubSet.Factory<>(allVariables);
		return new VariableAbstraction<>(this::copyAction, mMgdScript, null, null, mFactory);
	}

	/*
	 * ****************************************************************************************************************
	 * Actual test cases
	 * ****************************************************************************************************************
	 */

	@Test
	public void sharedInOutVar() {
		testAbstraction(yIsXPlusY(), set(y));
	}

	@Test
	public void rightSideAbstracted() {
		// abstract variable on right side, but not left side
		testAbstraction(yIsXTimesTwo(), set(y));
	}

	@Test
	public void leftSideAbstraction() {
		testAbstraction(yIsXTimesTwo(), set(x));
	}

	@Test
	public void bothSidesDifferentVariablesEmptyConstrVars() {
		testAbstraction(yIsXTimesTwo(), set());
	}

	@Test
	public void doNothingFullConstrVars() {
		testAbstractionDoesNothing(yIsXTimesTwo(), set(x, y));
		testAbstractionDoesNothing(xIsXPlusOne(), set(x, y));
	}

	@Test
	public void bothSidesSameVariable() {
		testAbstraction(xIsXPlusOne(), set());
	}

	@Test
	public void withAuxVar() {
		testAbstraction(jointHavocXandY(), set(x));
	}

	private BitSubSet<IProgramVar> set(final IProgramVar... vars) {
		return mFactory.valueOf(Set.of(vars));
	}
}
