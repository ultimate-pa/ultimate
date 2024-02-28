/*
 * Copyright (C) 2023 Marcel Ebbinghaus
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.List;
import java.util.Random;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Random criterion for conditional commutativity checking.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class RandomCriterion<L> implements IConditionalCommutativityCriterion<L> {

	private final double mProbability;
	private final Random mRandomGenerator;

	/**
	 * Constructs a new random criterion.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param probability
	 *            The probability.
	 * @param seed
	 *            The random seed.
	 */
	public RandomCriterion(final double probability, final long seed) {
		mProbability = probability;
		mRandomGenerator = new Random(seed);
	}

	@Override
	public boolean decide(final IPredicate state, final IRun<L, IPredicate> run, final L letter1, final L letter2) {
		return (mRandomGenerator.nextInt(100) < (100 * mProbability));
	}

	@Override
	public boolean decide(final IPredicate condition) {
		return condition != null;
	}

	@Override
	public void updateCondition(IPredicate condition) {
		// TODO Auto-generated method stub
		
	}

}
