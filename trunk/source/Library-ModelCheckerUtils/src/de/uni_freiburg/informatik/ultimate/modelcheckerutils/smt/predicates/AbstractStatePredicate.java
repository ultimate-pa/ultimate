/*
 * Copyright (C) 2013-2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2016 University of Freiburg
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Representation of an abstract state predicate that contains an abstract state from abstract interpretation.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <ACTION>
 * @param <VARDECL>
 */
public class AbstractStatePredicate<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL>
		extends BasicPredicate {
	
	private static final long serialVersionUID = 1L;
	
	private final STATE mAbstractState;

	/**
	 * Default constructor of an abstract state predicate, constructed from an abstract state.
	 *
	 * @param serialNumber
	 * @param procedures
	 * @param term
	 * @param vars
	 * @param closedFormula
	 * @param abstractState
	 */
	public AbstractStatePredicate(final int serialNumber, final String[] procedures, final Term term,
			final Set<IProgramVar> vars, final Term closedFormula, final STATE abstractState) {
		super(serialNumber, procedures, term, vars, closedFormula);

		mAbstractState = abstractState;
	}
	
	@Visualizable
	public STATE getAbstractState() {
		return mAbstractState;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(mSerialNumber).append("#");
		sb.append(mFormula.toStringDirect());
		return sb.toString();
	}

	@Override
	public int hashCode() {
		return mSerialNumber;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null) {
			return false;
		}
		if (this == obj) {
			return true;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		
		@SuppressWarnings("rawtypes")
		final AbstractStatePredicate other = (AbstractStatePredicate) obj;

		return mSerialNumber == other.mSerialNumber;
	}
}

