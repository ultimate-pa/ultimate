/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Represents a literal on the decide stack that was set because of a decision of the epr
 * solver (in contrast to a propagation..).
 *
 * @author Alexander Nutz
 */
public class DecideStackDecisionLiteral extends DecideStackLiteral {

	public DecideStackDecisionLiteral(final EprPredicate eprPredicate,
			final DawgState<ApplicationTerm, EprTheory.TriBool> dawg) {
		super(eprPredicate, dawg);
	}

	@Override
	public String toString() {
		return String.format("(DSDec: %s %s)", mPred, mDawg);
	}
}
