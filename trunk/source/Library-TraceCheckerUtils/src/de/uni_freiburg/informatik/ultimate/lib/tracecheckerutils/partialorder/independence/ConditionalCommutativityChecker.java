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

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;

public class ConditionalCommutativityChecker<L extends IIcfgTransition<?>>
		implements IConditionalCommutativityChecker<L> {

	private final IConditionalCommutativityCriterion<L> mCriterion;
	private final SemanticIndependenceConditionGenerator mGenerator;
	private final ITraceChecker<L> mTraceChecker;

	public ConditionalCommutativityChecker(final IConditionalCommutativityCriterion<L> criterion,
			final IIndependenceRelation<IPredicate, L> independenceRelation,
			final SemanticIndependenceConditionGenerator generator, final IAutomaton<L, IPredicate> abstraction,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final ITraceChecker<L> traceChecker) {
		mCriterion = criterion;
		mGenerator = generator;
		mTraceChecker = traceChecker;

	}

	@Override
	public List<IPredicate> checkConditionalCommutativity(final IRun<L, IPredicate> run, final IPredicate state,
			final L a, final L b) {

		if (mCriterion.decide(state, a, b)) {
			final IPredicate condition = mGenerator.generateCondition(state, a.getTransformula(), b.getTransformula());
			if (mCriterion.decide(condition)) {
				return mTraceChecker.checkTrace(run, null, condition);
			}
		}
		return null;
	}
}
