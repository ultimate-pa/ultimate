/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * A budget function that caches the budgets assigned by a given underlying budget function.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 * @param <R>
 */
public class CachedBudget<L, R> implements IBudgetFunction<L, R> {

	private final IBudgetFunction<L, R> mUnderlying;
	private final NestedMap2<R, L, Integer> mCache = new NestedMap2<>();

	public CachedBudget(final IBudgetFunction<L, R> underlying) {
		mUnderlying = underlying;
	}

	@Override
	public int computeBudget(final R state, final L letter) {
		final Integer cached = mCache.get(state, letter);
		if (cached != null) {
			return cached;
		}

		final int result = mUnderlying.computeBudget(state, letter);
		mCache.put(state, letter, result);
		return result;
	}
}
