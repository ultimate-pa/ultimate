/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.FakeBoogieVar;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;

public class IntervalDomainSubsetTest {

	@Test
	public void TestSubsetRelatedToBug() {
		final FakeBoogieVar varA = new FakeBoogieVar(BoogieType.TYPE_INT, "a");

		IntervalDomainState state1 = new IntervalDomainState(new ConsoleLogger(), false);
		state1 = state1.addVariable(varA);
		state1 = state1.setValue(varA, new IntervalDomainValue(new IntervalValue(), new IntervalValue(8)));

		IntervalDomainState state2 = new IntervalDomainState(new ConsoleLogger(), false);
		state2 = state2.addVariable(varA);
		state2 = state2.setValue(varA, new IntervalDomainValue(1, 8));

		System.out.println("State1:\n" + state1);
		System.out.println("State2:\n" + state2);

		final SubsetResult subsetResult = state1.isSubsetOf(state2);
		System.out.println("Subset result: " + subsetResult);

		assertTrue(subsetResult == SubsetResult.NONE);
	}

	@Test
	public void TestContainment() {
		final FakeBoogieVar varA = new FakeBoogieVar(BoogieType.TYPE_INT, "a");

		IntervalDomainState s1 = new IntervalDomainState(new ConsoleLogger(), false);
		s1 = s1.addVariable(varA);
		s1 = s1.setValue(varA, new IntervalDomainValue(2, 4));

		IntervalDomainState s2 = new IntervalDomainState(new ConsoleLogger(), false);
		s2 = s2.addVariable(varA);
		s2 = s2.setValue(varA, new IntervalDomainValue(0, 5));

		System.out.println("State 1: " + s1);
		System.out.println("State 2: " + s2);

		final SubsetResult subsetResult = s1.isSubsetOf(s2);
		System.out.println("Subset result: " + subsetResult);

		assertTrue(subsetResult != SubsetResult.NONE);
	}
}
