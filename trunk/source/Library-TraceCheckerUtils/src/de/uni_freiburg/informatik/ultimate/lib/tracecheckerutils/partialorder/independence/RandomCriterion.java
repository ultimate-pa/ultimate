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

import java.util.Objects;
import java.util.Random;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Random criterion for conditional commutativity checking.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class RandomCriterion<L> implements IConditionalCommutativityCriterion<L> {

	private final int mProbability;
	private long mSeed;
	//private final Random mRandomGenerator;

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
	public RandomCriterion(final int probability, final long seed) {
		mProbability = probability;
		mSeed = seed;
	}

	@Override
	public boolean decide(final IPredicate state, final L letter1, final L letter2) {
		Pair<IPredicate, Pair<L,L>> normalized = normalize(state, letter1, letter2);
		Random random = new Random(mSeed * Objects.hashCode(normalized));
		return (random.nextInt(100) < mProbability);
	}

	@Override
	public boolean decide(final IPredicate condition) {
		return condition != null;
	}
	
	private Pair<IPredicate, Pair<L,L>> normalize(final IPredicate state, final L letter1, final L letter2) {
		return new Pair<IPredicate, Pair<L,L>>(state, new Pair<>(letter1, letter2));
	}

	@Override
	public void updateCriterion(IPredicate state, L letter1, L letter2) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void updateAbstraction(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
		// TODO Auto-generated method stub
		
	}

}
