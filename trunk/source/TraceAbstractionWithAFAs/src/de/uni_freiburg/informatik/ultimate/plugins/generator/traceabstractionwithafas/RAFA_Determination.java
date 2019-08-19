/*
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionWithAFAs plug-in.
 *
 * The ULTIMATE TraceAbstractionWithAFAs plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionWithAFAs plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionWithAFAs plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionWithAFAs plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionWithAFAs plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.BitSet;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;

public class RAFA_Determination<LETTER> extends GeneralOperation<LETTER, IPredicate, IStateFactory<IPredicate>> {
	private final AlternatingAutomaton<LETTER, IPredicate> mAlternatingAutomaton;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateUnifier mPredicateUnifier;
	private final NestedWordAutomaton<LETTER, IPredicate> mResultAutomaton;

	public RAFA_Determination(final AutomataLibraryServices services,
			final AlternatingAutomaton<LETTER, IPredicate> alternatingAutomaton, final CfgSmtToolkit csToolkit,
			final PredicateUnifier predicateUnifier, final IEmptyStackStateFactory<IPredicate> stateFactory) {
		super(services);
		assert alternatingAutomaton.isReversed();
		mAlternatingAutomaton = alternatingAutomaton;
		mCsToolkit = csToolkit;
		mPredicateUnifier = predicateUnifier;
		mResultAutomaton = new NestedWordAutomaton<>(services,
				new VpAlphabet<>(alternatingAutomaton.getAlphabet()),
				stateFactory);
		final LinkedList<BitSet> newStates = new LinkedList<>();
		newStates.add(alternatingAutomaton.getFinalStatesBitVector());
		mResultAutomaton.addState(true,
				alternatingAutomaton.getAcceptingFunction().getResult(alternatingAutomaton.getFinalStatesBitVector()),
				getPredicate(alternatingAutomaton.getFinalStatesBitVector()));
		while (!newStates.isEmpty()) {
			final BitSet state = newStates.removeFirst();
			final IPredicate predicate = getPredicate(state);
			for (final LETTER letter : alternatingAutomaton.getAlphabet()) {
				final BitSet nextState = (BitSet) state.clone();
				alternatingAutomaton.resolveLetter(letter, nextState);
				if (!nextState.isEmpty()) {
					final IPredicate nextPredicate = getPredicate(nextState);
					if (!mResultAutomaton.getStates().contains(nextPredicate)) {
						mResultAutomaton.addState(false,
								alternatingAutomaton.getAcceptingFunction().getResult(nextState), nextPredicate);
						newStates.add(nextState);
					}
					mResultAutomaton.addInternalTransition(predicate, letter, nextPredicate);
				}
			}
		}
	}

	private IPredicate getPredicate(final BitSet state) {
		IPredicate predicate = mPredicateUnifier.getTruePredicate();
		int setBitIndex = getNextSetBit(state, 0);
		while (setBitIndex != -1) {
			predicate = mPredicateUnifier.getOrConstructPredicate(mPredicateUnifier.getPredicateFactory().and(predicate,
					mAlternatingAutomaton.getStates().get(setBitIndex)));
			setBitIndex = getNextSetBit(state, setBitIndex + 1);
		}
		return predicate;
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mResultAutomaton;
	}

	@Override
	public boolean checkResult(final IStateFactory<IPredicate> stateFactory) throws AutomataLibraryException {
		return true;
	}

	private static int getNextSetBit(final BitSet bitSet, final int offset) {
		for (int i = offset; i < bitSet.size(); i++) {
			if (bitSet.get(i)) {
				return i;
			}
		}
		return -1;
	}
}
