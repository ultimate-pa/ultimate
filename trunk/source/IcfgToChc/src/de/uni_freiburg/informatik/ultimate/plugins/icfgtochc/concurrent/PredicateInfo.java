/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IcfgToChcConcurrent.IHcReplacementVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

public class PredicateInfo {
	private final HcPredicateSymbol mPredicate;
	private final BidirectionalMap<IHcReplacementVar, Integer> mVariable2Index;

	public PredicateInfo(final HcPredicateSymbol predicate,
			final BidirectionalMap<IHcReplacementVar, Integer> variable2Index) {
		mPredicate = predicate;
		mVariable2Index = variable2Index;
	}

	public HcPredicateSymbol getPredicate() {
		return mPredicate;
	}

	public boolean hasParameter(final IHcReplacementVar variable) {
		return mVariable2Index.containsKey(variable);
	}

	public int getIndex(final IHcReplacementVar variable) {
		assert mVariable2Index.containsKey(variable);
		return mVariable2Index.get(variable);
	}

	public IHcReplacementVar getParameter(final int index) {
		final var result = mVariable2Index.inverse().get(index);
		assert result != null : "No parameter at index " + index + " (out of " + mPredicate.getArity() + ")";
		return result;
	}

	public int getParamCount() {
		return mVariable2Index.size();
	}

	@Override
	public int hashCode() {
		return Objects.hash(mPredicate, mVariable2Index);
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
		final PredicateInfo other = (PredicateInfo) obj;
		return Objects.equals(mPredicate, other.mPredicate) && Objects.equals(mVariable2Index, other.mVariable2Index);
	}
}
