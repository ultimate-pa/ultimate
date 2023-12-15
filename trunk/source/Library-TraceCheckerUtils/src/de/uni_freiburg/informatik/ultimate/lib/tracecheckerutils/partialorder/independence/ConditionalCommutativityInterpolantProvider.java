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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;

public class ConditionalCommutativityInterpolantProvider<L extends IIcfgTransition<?>> {

	private ConditionalCommutativityChecker<L> mChecker;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mReduction;

	public ConditionalCommutativityInterpolantProvider(IConditionalCommutativityCriterion<L> criterion,
			IIndependenceRelation<IPredicate, L> independenceRelation, SemanticIndependenceConditionGenerator generator,
			final IAutomaton<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> reduction,
			IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, ITraceChecker<L> traceChecker) {
		mReduction = reduction;
		mChecker = new ConditionalCommutativityChecker<>(criterion, independenceRelation, generator, abstraction,
				emptyStackStateFactory, traceChecker);
	}

	// TODO: takes the interpolantAutomaton instead of the predicates,
	// constructs a copy and includes paths and states for conditional commutativity proofs
	public List<IPredicate> getInterpolants(IRun<L, IPredicate> run, List<IPredicate> predicates,
			NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		NestedWordAutomaton<L, IPredicate> copy = copy(interpolantAutomaton);
		// TODO: copy interpolantAutomaton
		for (IPredicate state : run.getStateSequence()) {
			Iterator<OutgoingInternalTransition<L, IPredicate>> iterator =
					mReduction.internalSuccessors(state).iterator();

			List<OutgoingInternalTransition<L, IPredicate>> transitions = new ArrayList<>();
			while (iterator.hasNext()) {
				transitions.add(iterator.next());
			}

			for (int j = 0; j < transitions.size(); j++) {
				OutgoingInternalTransition<L, IPredicate> transition1 = transitions.get(j);
				for (int k = j + 1; k < transitions.size(); k++) {
					OutgoingInternalTransition<L, IPredicate> transition2 = transitions.get(k);
					List<IPredicate> conPredicates = mChecker.checkConditionalCommutativity(run, state,
							transition1.getLetter(), transition2.getLetter());
					if (conPredicates != null) {
						// TODO: add states and transitions to copy
						predicates.addAll(conPredicates);
					}
				}
			}
		}
		// TODO: return copy
		return predicates;
	}

	private NestedWordAutomaton<L, IPredicate> copy(NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		
		return null;
	}

}
