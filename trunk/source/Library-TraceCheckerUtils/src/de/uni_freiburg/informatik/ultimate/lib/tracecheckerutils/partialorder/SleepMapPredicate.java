/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMap;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class SleepMapPredicate<L> implements IMLPredicate {
	private final IMLPredicate mUnderlying;
	private final SleepMap<L, IPredicate> mSleepMap;
	private final int mBudget;

	public SleepMapPredicate(final IMLPredicate underlying, final SleepMap<L, IPredicate> sleepMap, final int budget) {
		mUnderlying = underlying;
		mSleepMap = sleepMap;
		mBudget = budget;
	}

	@Override
	public Term getFormula() {
		return mUnderlying.getFormula();
	}

	@Override
	public Term getClosedFormula() {
		return mUnderlying.getClosedFormula();
	}

	@Override
	public String[] getProcedures() {
		return mUnderlying.getProcedures();
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mUnderlying.getVars();
	}

	@Override
	public IcfgLocation[] getProgramPoints() {
		return mUnderlying.getProgramPoints();
	}

	public IMLPredicate getUnderlying() {
		return mUnderlying;
	}

	public SleepMap<L, IPredicate> getSleepMap() {
		return mSleepMap;
	}

	public int getBudget() {
		return mBudget;
	}

	@Override
	public int hashCode() {
		return Objects.hash(mBudget, mSleepMap, mUnderlying);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final SleepMapPredicate<?> other = (SleepMapPredicate<?>) obj;
		return mBudget == other.mBudget && Objects.equals(mSleepMap, other.mSleepMap)
				&& Objects.equals(mUnderlying, other.mUnderlying);
	}

	@Override
	public String toString() {
		return "SleepMapPredicate [underlying: " + mUnderlying + ", budget: " + mBudget + ", map: " + mSleepMap + "]";
	}
}
