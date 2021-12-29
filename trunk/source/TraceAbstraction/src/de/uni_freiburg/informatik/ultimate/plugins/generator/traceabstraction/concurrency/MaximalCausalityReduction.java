/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Implementation of Maximal Causality Reduction.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of letters of the input automaton.
 */
public class MaximalCausalityReduction<L extends IIcfgTransition<?>>
		implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate> {
	private final ILogger mLogger;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mOperand;
	private final McrStateFactory<L> mStateFactory;
	private final McrState<L, IPredicate> mInitial;
	private final IPredicate mInitialPredicate;
	private final BidirectionalMap<IPredicate, McrState<L, IPredicate>> mStateMap;

	/**
	 * Constructor.
	 *
	 * @param loggingService
	 *            A logging service.
	 * @param operand
	 *            The automaton to apply MCR on.
	 * @param stateFactory
	 *            An McrStateFactory.
	 */
	public MaximalCausalityReduction(final ILoggingService loggingService,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> operand,
			final McrStateFactory<L> stateFactory) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "MCR supports only finite automata";

		mLogger = loggingService.getLogger(MaximalCausalityReduction.class);
		mOperand = operand;
		final IPredicate oldInitial = DataStructureUtils.getOneAndOnly(operand.getInitialStates(), "initial state");
		mInitial = new McrState<>(oldInitial);
		mStateMap = new BidirectionalMap<>();
		mStateFactory = stateFactory;
		mInitialPredicate = mStateFactory.createState(oldInitial, mInitial);
		mStateMap.put(mInitialPredicate, mInitial);
	}

	@Override
	public IStateFactory<IPredicate> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public IPredicate getEmptyStackState() {
		return mStateFactory.createEmptyStackState();
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		return Set.of(mInitialPredicate);
	}

	@Override
	public boolean isInitial(final IPredicate state) {
		return mInitialPredicate.equals(state);
	}

	@Override
	public boolean isFinal(final IPredicate state) {
		// TODO: Change this when we implement the left-right split.
		return mOperand.isFinal(mStateMap.get(state).getOldState());
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "currently " + size() + " states, but on-demand construction may add more states";
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, IPredicate>> internalSuccessors(final IPredicate state,
			final L letter) {
		final McrState<L, IPredicate> mcrState = mStateMap.get(state);

		final var transition = DataStructureUtils.getOnly(mOperand.internalSuccessors(mcrState.getOldState(), letter),
				"must be deterministic");
		if (transition.isEmpty()) {
			return Collections.emptySet();
		}
		final IPredicate successorState = transition.get().getSucc();

		final McrState<L, IPredicate> newState = mcrState.execute(letter, successorState);
		if (newState == null) {
			mLogger.debug("discard " + state + ": " + letter);
			return Collections.emptySet();
		}
		IPredicate newPredicate;
		if (mStateMap.containsValue(newState)) {
			newPredicate = mStateMap.inverse().get(newState);
		} else {
			newPredicate = mStateFactory.createState(successorState, newState);
			mStateMap.put(newPredicate, newState);
		}
		return Set.of(new OutgoingInternalTransition<>(letter, newPredicate));
	}

	@Override
	public Iterable<OutgoingCallTransition<L, IPredicate>> callSuccessors(final IPredicate state, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, IPredicate>> returnSuccessors(final IPredicate state,
			final IPredicate hier, final L letter) {
		return Collections.emptySet();
	}
}
