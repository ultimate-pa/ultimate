/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class BestApproximationDeterminizer implements IStateDeterminizer<IIcfgTransition<?>, IPredicate> {
	private final IHoareTripleChecker mHoareTriplechecker;
	private final TAPreferences mTaPreferences;
	private final IDeterminizeStateFactory<IPredicate> mStateFactory;
	private final NestedWordAutomaton<IIcfgTransition<?>, IPredicate> mNwa;
	private int mAnswerInternalSolver;
	private int mAnswerInternalAutomaton;
	private int mAnswerInternalCache;
	private int mAnswerCallSolver;
	private int mAnswerCallAutomaton;
	private int mAnswerCallCache;
	private int mAnswerReturnSolver;
	private int mAnswerReturnAutomaton;
	private int mAnswerReturnCache;

	Map<IPredicate, Map<IIcfgTransition<?>, Set<IPredicate>>> mInductiveSuccsCache = new HashMap<>();

	Map<IPredicate, Map<IIcfgTransition<?>, Set<IPredicate>>> mInductiveCallSuccsCache = new HashMap<>();

	Map<IPredicate, Map<IPredicate, Map<IIcfgTransition<?>, Set<IPredicate>>>> mInductiveReturnSuccsCache =
			new HashMap<>();

	public BestApproximationDeterminizer(final CfgSmtToolkit mCsToolkit, final TAPreferences taPreferences,
			final NestedWordAutomaton<IIcfgTransition<?>, IPredicate> nwa,
			final IDeterminizeStateFactory<IPredicate> stateFactory) {
		mHoareTriplechecker = new MonolithicHoareTripleChecker(mCsToolkit);
		mTaPreferences = taPreferences;
		mStateFactory = stateFactory;
		mNwa = nwa;
	}

	public int getmAnswerInternalSolver() {
		return mAnswerInternalSolver;
	}

	public int getmAnswerInternalAutomaton() {
		return mAnswerInternalAutomaton;
	}

	public int getmAnswerInternalCache() {
		return mAnswerInternalCache;
	}

	public int getmAnswerCallSolver() {
		return mAnswerCallSolver;
	}

	public int getmAnswerCallAutomaton() {
		return mAnswerCallAutomaton;
	}

	public int getmAnswerCallCache() {
		return mAnswerCallCache;
	}

	public int getmAnswerReturnSolver() {
		return mAnswerReturnSolver;
	}

	public int getmAnswerReturnAutomaton() {
		return mAnswerReturnAutomaton;
	}

	public int getmAnswerReturnCache() {
		return mAnswerReturnCache;
	}

	@Override
	public DeterminizedState<IIcfgTransition<?>, IPredicate> initialState() {
		final DeterminizedState<IIcfgTransition<?>, IPredicate> detState = new DeterminizedState<>(mNwa);
		// FIXME add all at once
		for (final IPredicate initialState : mNwa.getInitialStates()) {
			detState.addPair(mNwa.getEmptyStackState(), initialState, mNwa);
		}
		return detState;
	}

	@Override
	public DeterminizedState<IIcfgTransition<?>, IPredicate> internalSuccessor(
			final DeterminizedState<IIcfgTransition<?>, IPredicate> detState, final IIcfgTransition<?> symbol) {
		final DeterminizedState<IIcfgTransition<?>, IPredicate> succDetState = new DeterminizedState<>(mNwa);
		for (final IPredicate downState : detState.getDownStates()) {
			for (final IPredicate upState : detState.getUpStates(downState)) {
				for (final IPredicate upSucc : getInternalSuccs(upState, symbol)) {
					succDetState.addPair(downState, upSucc, mNwa);
				}
			}
		}
		if (mTaPreferences.computeHoareAnnotation()) {
			assert mHoareTriplechecker.checkInternal(getState(detState), (IInternalAction) symbol,
					getState(succDetState)) == Validity.VALID
					|| mHoareTriplechecker.checkInternal(detState.getContent(mStateFactory), (IInternalAction) symbol,
							getState(succDetState)) == Validity.UNKNOWN;
		}
		return succDetState;
	}

	@Override
	public DeterminizedState<IIcfgTransition<?>, IPredicate> callSuccessor(
			final DeterminizedState<IIcfgTransition<?>, IPredicate> detState, final IIcfgTransition<?> symbol) {
		final DeterminizedState<IIcfgTransition<?>, IPredicate> succDetState = new DeterminizedState<>(mNwa);
		for (final IPredicate downState : detState.getDownStates()) {
			for (final IPredicate upState : detState.getUpStates(downState)) {
				for (final IPredicate upSucc : getCallSuccs(upState, (IIcfgCallTransition<?>) symbol)) {
					succDetState.addPair(upState, upSucc, mNwa);
				}
			}
		}
		if (mTaPreferences.computeHoareAnnotation()) {
			assert mHoareTriplechecker.checkCall(getState(detState), (IIcfgCallTransition<?>) symbol,
					getState(succDetState)) == Validity.VALID
					|| mHoareTriplechecker.checkCall(getState(detState), (IIcfgCallTransition<?>) symbol,
							getState(succDetState)) == Validity.UNKNOWN;
		}
		return succDetState;
	}

	@Override
	public DeterminizedState<IIcfgTransition<?>, IPredicate> returnSuccessor(
			final DeterminizedState<IIcfgTransition<?>, IPredicate> detState,
			final DeterminizedState<IIcfgTransition<?>, IPredicate> detLinPred, final IIcfgTransition<?> symbol) {
		final DeterminizedState<IIcfgTransition<?>, IPredicate> succDetState = new DeterminizedState<>(mNwa);

		for (final IPredicate downLinPred : detLinPred.getDownStates()) {
			for (final IPredicate upLinPred : detLinPred.getUpStates(downLinPred)) {
				final Set<IPredicate> upStates = detState.getUpStates(upLinPred);
				if (upStates == null) {
					continue;
				}
				for (final IPredicate upState : upStates) {
					final IIcfgReturnTransition<?, ?> returnSymbol = (IIcfgReturnTransition<?, ?>) symbol;
					for (final IPredicate upSucc : getReturnSuccs(upState, upLinPred, returnSymbol)) {
						succDetState.addPair(downLinPred, upSucc, mNwa);
					}
				}
			}
		}

		if (mTaPreferences.computeHoareAnnotation()) {
			assert mHoareTriplechecker.checkReturn(getState(detState), getState(detLinPred),
					(IIcfgReturnTransition<?, ?>) symbol, getState(succDetState)) == Validity.VALID
					|| mHoareTriplechecker.checkReturn(getState(detState), getState(detLinPred),
							(IIcfgReturnTransition<?, ?>) symbol, getState(succDetState)) == Validity.UNKNOWN;
		}

		return succDetState;
	}

	/**
	 * IIcfgReturnTransition<?, ?> all states succ such that (state, symbol, succ) is inductive.
	 */
	private Set<IPredicate> getInternalSuccs(final IPredicate state, final IIcfgTransition<?> symbol) {
		Set<IPredicate> succs = getInternalSuccsCache(state, symbol);
		if (succs == null) {
			succs = new HashSet<>();
			for (final IPredicate succCandidate : mNwa.getStates()) {
				if (isInductiveInternalSuccessor(state, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
			putInternalSuccsCache(state, symbol, succs);
		} else {
			mAnswerInternalCache++;
		}
		return succs;
	}

	/**
	 * Store in the cache that succs is the set of all states succ such that (state, symbol, succ) is inductive.
	 */
	private void putInternalSuccsCache(final IPredicate state, final IIcfgTransition<?> symbol,
			final Set<IPredicate> succs) {
		Map<IIcfgTransition<?>, Set<IPredicate>> symbol2succs = mInductiveSuccsCache.get(state);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<>();
			mInductiveSuccsCache.put(state, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that (state, symbol, succ) is inductive. If the cache knows this
	 * result succs is returned, otherwise null is returned.
	 */
	@SuppressWarnings("squid:S1168")
	private Set<IPredicate> getInternalSuccsCache(final IPredicate state, final IIcfgTransition<?> symbol) {
		final Map<IIcfgTransition<?>, Set<IPredicate>> symbol2succs = mInductiveSuccsCache.get(state);
		if (symbol2succs == null) {
			return null;
		}
		final Set<IPredicate> succs = symbol2succs.get(symbol);
		if (succs == null) {
			return null;
		}
		return succs;
	}

	/**
	 * IIcfgReturnTransition<?, ?> all states succ such that (state, symbol, succ) is inductive.
	 */
	private Set<IPredicate> getCallSuccs(final IPredicate state, final IIcfgCallTransition<?> symbol) {
		Set<IPredicate> succs = getCallSuccsCache(state, symbol);
		if (succs == null) {
			succs = new HashSet<>();
			for (final IPredicate succCandidate : mNwa.getStates()) {
				if (inductiveCallSuccessor(state, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
			putCallSuccsCache(state, symbol, succs);
		} else {
			mAnswerCallCache++;
		}
		return succs;
	}

	/**
	 * Store in the cache that succs is the set of all states succ such that (state, symbol, succ) is inductive.
	 */
	private void putCallSuccsCache(final IPredicate state, final IIcfgTransition<?> symbol,
			final Set<IPredicate> succs) {
		Map<IIcfgTransition<?>, Set<IPredicate>> symbol2succs = mInductiveCallSuccsCache.get(state);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<>();
			mInductiveCallSuccsCache.put(state, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that (state, symbol, succ) is inductive. If the cache knows this
	 * result succs is returned, otherwise null is returned.
	 */
	@SuppressWarnings("squid:S1168")
	private Set<IPredicate> getCallSuccsCache(final IPredicate state, final IIcfgTransition<?> symbol) {
		final Map<IIcfgTransition<?>, Set<IPredicate>> symbol2succs = mInductiveCallSuccsCache.get(state);
		if (symbol2succs == null) {
			return null;
		}
		final Set<IPredicate> succs = symbol2succs.get(symbol);
		if (succs == null) {
			return null;
		}
		return succs;
	}

	/**
	 * Returns true iff (state,symbol,succ) is inductive. First the interpolant automaton is queried for a yes-answer,
	 * afterwards the solver is queried for a yes/no/unknown-answer. We query the interpolant automaton for two reasons:
	 * <ul>
	 * <li>a query to the solver is expensive
	 * <li>if we do not compute interpolants for every location we have unknown-labeled states for which the solver can
	 * not give a yes/no-answer.
	 * </ul>
	 */
	private boolean isInductiveInternalSuccessor(final IPredicate state, final IIcfgTransition<?> symbol,
			final IPredicate succ) {
		for (final OutgoingInternalTransition<IIcfgTransition<?>, IPredicate> trans : mNwa.internalSuccessors(state,
				symbol)) {
			if (trans.getSucc().equals(succ)) {
				mAnswerInternalAutomaton++;
				return true;
			}
		}
		final IPredicate presentPs = state;
		final IPredicate succPs = succ;
		final Validity sat = mHoareTriplechecker.checkInternal(presentPs, (IInternalAction) symbol, succPs);
		mAnswerInternalSolver++;
		if (sat == Validity.VALID) {
			mNwa.addInternalTransition(state, symbol, succ);
			return true;
		}
		return false;
	}

	/**
	 * Returns true iff (state,symbol,succ) is inductive. First the interpolant automaton is queried for a yes-answer,
	 * afterwards the solver is queried for a yes/no/unknown-answer. We query the interpolant automaton for two reasons:
	 * <ul>
	 * <li>a query to the solver is expensive
	 * <li>if we do not compute interpolants for every location we have unknown-labeled states for which the solver can
	 * not give a yes/no-answer.
	 * </ul>
	 */
	private boolean inductiveCallSuccessor(final IPredicate state, final IIcfgCallTransition<?> symbol,
			final IPredicate succ) {
		for (final OutgoingCallTransition<IIcfgTransition<?>, IPredicate> trans : mNwa.callSuccessors(state, symbol)) {
			if (trans.getSucc().equals(succ)) {
				mAnswerCallAutomaton++;
				return true;
			}
		}
		final IPredicate presentPs = state;
		final IPredicate succPs = succ;
		final Validity sat = mHoareTriplechecker.checkCall(presentPs, symbol, succPs);
		mAnswerCallSolver++;
		return sat == Validity.VALID;
	}

	/**
	 * IIcfgReturnTransition<?, ?> all states succ such that (state, linPred, symbol, succ) is inductive.
	 */
	private Set<IPredicate> getReturnSuccs(final IPredicate state, final IPredicate linPred,
			final IIcfgReturnTransition<?, ?> symbol) {
		Set<IPredicate> succs = getReturnSuccsCache(state, linPred, symbol);
		if (succs == null) {
			succs = new HashSet<>();
			for (final IPredicate succCandidate : mNwa.getStates()) {
				if (isInductiveReturnSuccessor(state, linPred, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
			putReturnSuccsCache(state, linPred, symbol, succs);
		} else {
			mAnswerReturnCache++;
		}
		return succs;
	}

	/**
	 * Store in the cache that succs is the set of all states succ such that (state, linPred, symbol, succ) is
	 * inductive.
	 */
	private void putReturnSuccsCache(final IPredicate state, final IPredicate linPred, final IIcfgTransition<?> symbol,
			final Set<IPredicate> succs) {
		Map<IPredicate, Map<IIcfgTransition<?>, Set<IPredicate>>> linPred2symbol2succs =
				mInductiveReturnSuccsCache.get(state);
		if (linPred2symbol2succs == null) {
			linPred2symbol2succs = new HashMap<>();
			mInductiveReturnSuccsCache.put(state, linPred2symbol2succs);
		}
		Map<IIcfgTransition<?>, Set<IPredicate>> symbol2succs = linPred2symbol2succs.get(linPred);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<>();
			linPred2symbol2succs.put(linPred, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that (state, linPred, symbol, succ) is inductive. If the cache knows
	 * this result succs is returned, otherwise null is returned.
	 */
	@SuppressWarnings("squid:S1168")
	private Set<IPredicate> getReturnSuccsCache(final IPredicate state, final IPredicate linPred,
			final IIcfgTransition<?> symbol) {
		final Map<IPredicate, Map<IIcfgTransition<?>, Set<IPredicate>>> linPred2symbol2succs =
				mInductiveReturnSuccsCache.get(state);
		if (linPred2symbol2succs == null) {
			return null;
		}
		final Map<IIcfgTransition<?>, Set<IPredicate>> symbol2succs = linPred2symbol2succs.get(linPred);
		if (symbol2succs == null) {
			return null;
		}
		final Set<IPredicate> succs = symbol2succs.get(symbol);
		if (succs == null) {
			return null;
		}
		return succs;
	}

	/**
	 * Returns true iff (state,callerState,symbol,succ) is inductive. First the interpolant automaton is queried for a
	 * yes-answer, afterwards the solver is queried for a yes/no/unknown-answer. We query the interpolant automaton for
	 * two reasons:
	 * <ul>
	 * <li>a query to the solver is expensive
	 * <li>if we do not compute interpolants for every location we have unknown-labeled states for which the solver can
	 * not give a yes/no-answer.
	 * </ul>
	 */
	private boolean isInductiveReturnSuccessor(final IPredicate state, final IPredicate callerState,
			final IIcfgReturnTransition<?, ?> symbol, final IPredicate succ) {
		for (final OutgoingReturnTransition<IIcfgTransition<?>, IPredicate> trans : mNwa.returnSuccessors(state,
				callerState, symbol)) {
			if (trans.getSucc().equals(succ)) {
				mAnswerReturnAutomaton++;
				return true;
			}
		}
		final IPredicate presentPs = state;
		final IPredicate callerPs = callerState;
		final IPredicate succPs = succ;
		final Validity sat = mHoareTriplechecker.checkReturn(presentPs, callerPs, symbol, succPs);
		mAnswerReturnSolver++;
		return sat == Validity.VALID;
	}

	@Override
	public int getMaxDegreeOfNondeterminism() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean useDoubleDeckers() {
		throw new AssertionError("Matthias has to check which result is correct");
	}

	@Override
	public IPredicate getState(final DeterminizedState<IIcfgTransition<?>, IPredicate> determinizedState) {
		return determinizedState.getContent(mStateFactory);
	}
}
