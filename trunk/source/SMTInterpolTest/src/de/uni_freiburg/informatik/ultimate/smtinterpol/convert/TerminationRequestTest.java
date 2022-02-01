/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

@RunWith(JUnit4.class)
public class TerminationRequestTest {
	public class MyTerminationRequest implements TerminationRequest {

		public int mRequestCtr;

		public MyTerminationRequest(final int deadline) {
			mRequestCtr = deadline;
		}

		@Override
		public boolean isTerminationRequested() {
			return mRequestCtr-- <= 0;
		}
	}

	@Test
	public void test() {
		final TerminationRequest cancel = new MyTerminationRequest(0);
		final SMTInterpol smtinterpol = new SMTInterpol(cancel);
		smtinterpol.setOption(":verbosity", 3);
		smtinterpol.setLogic(Logics.QF_UF);
		smtinterpol.assertTerm(smtinterpol.term("false"));
		final LBool status = smtinterpol.checkSat();
		Assert.assertEquals(LBool.UNKNOWN, status);
		Assert.assertEquals(ReasonUnknown.CANCELLED, smtinterpol.getInfo(":reason-unknown"));
	}
}
