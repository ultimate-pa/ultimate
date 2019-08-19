/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BasicPredicate extends ModernAnnotations implements IPredicate {
	private static final long serialVersionUID = -2257982001512157622L;
	protected final String[] mProcedures;
	protected Term mFormula;
	protected final Term mClosedFormula;
	protected final Set<IProgramVar> mVars;
	protected final int mSerialNumber;

	public BasicPredicate(final int serialNumber, final String[] procedures, final Term term,
			final Set<IProgramVar> vars, final Term closedFormula) {
		mFormula = term;
		mClosedFormula = closedFormula;
		mProcedures = procedures;
		mVars = vars;
		mSerialNumber = serialNumber;
	}

	@Override
	@Visualizable
	public String[] getProcedures() {
		return mProcedures;
	}

	/**
	 * @return the mAssertion
	 */
	@Override
	@Visualizable
	public Term getFormula() {
		return mFormula;
	}

	@Override
	public Term getClosedFormula() {
		return mClosedFormula;
	}

	@Override
	@Visualizable
	public Set<IProgramVar> getVars() {
		return mVars;
	}

	@Override
	public String toString() {
		return mSerialNumber + "#" + mFormula.toStringDirect();
	}

	public boolean isUnknown() {
		return false;
	}

	@Override
	public final int hashCode() {
		return mSerialNumber;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof BasicPredicate)) {
			return false;
		}
		final BasicPredicate other = (BasicPredicate) obj;
		return mSerialNumber == other.mSerialNumber;
	}

}
