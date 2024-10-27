/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalRule.Quantifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalRule.Range;

public class ConditionalBroadcast<S> implements IRule<Configuration<S>> {
	private final S mSource;
	private final S mTarget;
	private final Range mRange;
	private final Quantifier mQuantifier;
	private final Predicate<S> mCondition;
	private final UnaryOperator<S> mBroadcast;

	public ConditionalBroadcast(final S source, final S target, final Range range, final Quantifier quantifier,
			final Predicate<S> condition, final UnaryOperator<S> broadcast) {
		mSource = source;
		mTarget = target;
		mRange = range;
		mQuantifier = quantifier;
		mCondition = condition;
		mBroadcast = broadcast;
	}

	@Override
	public boolean isApplicable(final Configuration<S> config) {
		for (int i = 0; i < config.numberOfThreads(); ++i) {
			final var state = config.getThread(i);
			if (state.equals(mSource)) {
				final boolean conditionSatisfied = checkCondition(config, i);
				if (conditionSatisfied) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean checkCondition(final Configuration<S> config, final int index) {
		boolean result = mQuantifier.defaultValue();
		for (int i = 0; i < config.numberOfThreads(); ++i) {
			if (mRange.satisfies(i, index)) {
				final var state = config.getThread(i);
				result = mQuantifier.combine(result, mCondition.test(state));
			}
		}
		return result;
	}

	@Override
	public List<Configuration<S>> successors(final Configuration<S> config) {
		assert isApplicable(config);

		final var result = new ArrayList<Configuration<S>>();
		for (int i = 0; i < config.numberOfThreads(); ++i) {
			final var state = config.getThread(i);
			if (state.equals(mSource) && checkCondition(config, i)) {
				result.add(successor(config, i));
			}

		}
		return result;
	}

	private Configuration<S> successor(final Configuration<S> config, final int index) {
		final var subst = new HashMap<Integer, S>();
		subst.put(index, mTarget);

		for (int i = 0; i < config.numberOfThreads(); ++i) {
			final var state = config.getThread(i);
			final var newState = mBroadcast.apply(state);
			if (i != index && newState != null) {
				subst.put(i, newState);
			}
		}

		return config.replace(subst);
	}

	@Override
	public int extensionSize() {
		return mQuantifier == Quantifier.EXISTS ? 1 : 0;
	}
}