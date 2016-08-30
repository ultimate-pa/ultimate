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

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.test.ConsoleLogger;

public class IntervalDomainSubsetTest {

	@Test
	public void TestSubsetRelatedToBug() {
		final BoogieVarMockup varA = new BoogieVarMockup("a");

		IntervalDomainState state1 = new IntervalDomainState(new ConsoleLogger());
		state1 = state1.addVariable(varA);
		state1 = state1.setValue(varA, new IntervalDomainValue(new IntervalValue(), new IntervalValue(8)));

		IntervalDomainState state2 = new IntervalDomainState(new ConsoleLogger());
		state2 = state2.addVariable(varA);
		state2 = state2.setValue(varA, new IntervalDomainValue(1, 8));

		System.out.println("State1:\n" + state1);
		System.out.println("State2:\n" + state2);

		final SubsetResult subsetResult = state1.isSubsetOf(state2);
		System.out.println("Subset result: " + subsetResult);

		assertTrue(subsetResult == SubsetResult.NONE);
	}

	private class BoogieVarMockup implements IBoogieVar {

		private final String mName;
		private final IBoogieType mBoogieType;

		private BoogieVarMockup(final String name) {
			mName = name;
			mBoogieType = PrimitiveType.TYPE_INT;
		}

		@Override
		public String getIdentifier() {
			return mName;
		}

		@Override
		public IBoogieType getIType() {
			return mBoogieType;
		}

		@Override
		public ApplicationTerm getDefaultConstant() {
			return null;
		}

		@Override
		public String toString() {
			return mName;
		}
	}
}
