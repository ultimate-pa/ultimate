/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Factory for construction of {@link IPredicate}s with unique serial numbers. Sometimes we need different
 * {@link IPredicate} objects with the same formulas. The serial number ensures that {@link IPredicate}s can be
 * different, can be used as a hash code and ease debugging.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class SmtFreePredicateFactory {

	/**
	 * Serial numbers for predicates start with 1, because 0 is reserved for the axioms.
	 */
	protected int mSerialNumberCounter = 1;

	protected final Term mDontCareTerm;
	protected final Term mEmptyStackTerm;

	public SmtFreePredicateFactory() {
		mDontCareTerm = new AuxiliaryTerm("don't care");
		mEmptyStackTerm = new AuxiliaryTerm("emptyStack");
	}

	final protected Term getDontCareTerm() {
		return mDontCareTerm;
	}

	final protected int constructFreshSerialNumber() {
		return mSerialNumberCounter++;
	}

	final public boolean isDontCare(final IPredicate pred) {
		return pred.getFormula() == mDontCareTerm;
	}

	final public boolean isDontCare(final Term term) {
		return term == mDontCareTerm;
	}

	final public DebugPredicate newDebugPredicate(final String debugMessage) {
		return new DebugPredicate(debugMessage, constructFreshSerialNumber(), mDontCareTerm);
	}

	public UnknownState newDontCarePredicate(final IcfgLocation pp) {
		final UnknownState pred = new UnknownState(pp, constructFreshSerialNumber(), mDontCareTerm);
		return pred;
	}

	private static final class AuxiliaryTerm extends Term {

		private final String mName;

		private AuxiliaryTerm(final String name) {
			super(0);
			mName = name;
		}

		@Override
		public Sort getSort() {
			throw new UnsupportedOperationException("Auxiliary term has no sort");
		}

		@Override
		public void toStringHelper(final ArrayDeque<Object> todo) {
			throw new UnsupportedOperationException("Auxiliary term must not be subterm of other terms");
		}

		@Override
		public TermVariable[] getFreeVars() {
			throw new UnsupportedOperationException("Auxiliary term has no vars");
		}

		@Override
		public Theory getTheory() {
			throw new UnsupportedOperationException("Auxiliary term has no theory");
		}

		@Override
		public String toString() {
			return mName;
		}

		@Override
		public String toStringDirect() {
			return mName;
		}

		@Override
		public int hashCode() {
			throw new UnsupportedOperationException("Auxiliary term must not be contained in any collection");
		}
	}

}