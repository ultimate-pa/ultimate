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

import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class BestApproximationDeterminizer 
		implements IStateDeterminizer<CodeBlock, IPredicate> {
	
	IHoareTripleChecker mHoareTriplechecker;
	TAPreferences mTaPreferences;
	StateFactory<IPredicate> mStateFactory;
	NestedWordAutomaton<CodeBlock, IPredicate> mNwa;
	public int mAnswerInternalSolver = 0;
	public int mAnswerInternalAutomaton = 0;
	public int mAnswerInternalCache = 0;
	public int mAnswerCallSolver = 0;
	public int mAnswerCallAutomaton = 0;
	public int mAnswerCallCache = 0;
	public int mAnswerReturnSolver = 0;
	public int mAnswerReturnAutomaton = 0;
	public int mAnswerReturnCache = 0;


	Map<IPredicate,Map<CodeBlock,Set<IPredicate>>>	mInductiveSuccsCache = 
		new HashMap<IPredicate,Map<CodeBlock,Set<IPredicate>>>();
	
	Map<IPredicate,Map<CodeBlock,Set<IPredicate>>>	mInductiveCallSuccsCache = 
		new HashMap<IPredicate,Map<CodeBlock,Set<IPredicate>>>();
	
	Map<IPredicate,Map<IPredicate,Map<CodeBlock,Set<IPredicate>>>> mInductiveReturnSuccsCache = 
		new HashMap<IPredicate,Map<IPredicate,Map<CodeBlock,Set<IPredicate>>>>();
	

	public BestApproximationDeterminizer(SmtManager mSmtManager,
			TAPreferences taPreferences,
			NestedWordAutomaton<CodeBlock, IPredicate> mNwa,
			StateFactory<IPredicate> stateFactory) {
		super();
		mHoareTriplechecker = new MonolithicHoareTripleChecker(
				mSmtManager.getManagedScript(), mSmtManager.getModifiableGlobals());
		mTaPreferences = taPreferences;
		mStateFactory = stateFactory;
		mNwa = mNwa;
	}
	
	@Override
	public DeterminizedState<CodeBlock, IPredicate> initialState() {
		final DeterminizedState<CodeBlock, IPredicate> detState = 
			new DeterminizedState<CodeBlock, IPredicate>(mNwa);
		//FIXME add all at once
		for (final IPredicate initialState : mNwa.getInitialStates()) {
			detState.addPair(mNwa.getEmptyStackState(), initialState, mNwa);
		}
		return detState;
	}

	@Override
	public DeterminizedState<CodeBlock, IPredicate>  internalSuccessor(
			DeterminizedState<CodeBlock, IPredicate>  detState,
			CodeBlock symbol) {
		
		final DeterminizedState<CodeBlock, IPredicate>  succDetState = 
			new DeterminizedState<CodeBlock, IPredicate> (mNwa);
		for (final IPredicate  downState : detState.getDownStates()) {
			for (final IPredicate  upState : detState.getUpStates(downState)) {
				for (final IPredicate  upSucc : getInternalSuccs(upState,symbol)) {
					succDetState.addPair(downState, upSucc, mNwa);
				}
			}
		}
		if (mTaPreferences.computeHoareAnnotation()) {
			assert(mHoareTriplechecker.checkInternal(getState(detState), 
						(IInternalAction) symbol, 
						getState(succDetState)) == Validity.VALID ||
				   mHoareTriplechecker.checkInternal(detState.getContent(mStateFactory), 
						(IInternalAction) symbol, 
						getState(succDetState)) == Validity.UNKNOWN);
		}
		return succDetState;	
	}
	
	@Override
	public DeterminizedState<CodeBlock, IPredicate>  callSuccessor(
			DeterminizedState<CodeBlock, IPredicate>  detState, 
			CodeBlock symbol) {
		
		final DeterminizedState<CodeBlock, IPredicate>  succDetState = 
				new DeterminizedState<CodeBlock, IPredicate> (mNwa);
		for (final IPredicate  downState : detState.getDownStates()) {
			for (final IPredicate  upState : detState.getUpStates(downState)) {
				for (final IPredicate  upSucc : getCallSuccs(upState,(Call) symbol)) {
					succDetState.addPair(upState, upSucc, mNwa);
				}
			}
		}
		if (mTaPreferences.computeHoareAnnotation()) {
			assert(mHoareTriplechecker.checkCall(
						getState(detState), 
						(Call) symbol, 
						getState(succDetState)) == Validity.VALID ||
				   mHoareTriplechecker.checkCall(getState(detState), 
						(Call) symbol, 
						getState(succDetState)) == Validity.UNKNOWN);
		}
		return succDetState;	
	}

	@Override
	public DeterminizedState<CodeBlock, IPredicate>  returnSuccessor(
			DeterminizedState<CodeBlock, IPredicate>  detState,
			DeterminizedState<CodeBlock, IPredicate>  detLinPred,
			CodeBlock symbol) {
		
		final DeterminizedState<CodeBlock, IPredicate>  succDetState = 
				new DeterminizedState<CodeBlock, IPredicate> (mNwa);
		
		for (final IPredicate  downLinPred : 
												detLinPred.getDownStates()) {
			for (final IPredicate  upLinPred : 
									detLinPred.getUpStates(downLinPred)) {
				final Set<IPredicate > upStates = 
										detState.getUpStates(upLinPred);
				if (upStates == null) {
					continue;
				}
				for (final IPredicate  upState : upStates) {
					final Return returnSymbol = (Return) symbol;
					for (final IPredicate  upSucc : 
							getReturnSuccs(upState,upLinPred, returnSymbol)) {
						succDetState.addPair(downLinPred, upSucc, mNwa);
					}
				}
			}
		}
		
		if (mTaPreferences.computeHoareAnnotation()) {
			assert(mHoareTriplechecker.checkReturn(
					getState(detState),
					getState(detLinPred),
					(Return) symbol, 
					getState(succDetState)) == Validity.VALID ||
							mHoareTriplechecker.checkReturn(getState(detState),
						getState(detLinPred),
						(Return) symbol, 
						getState(succDetState)) == Validity.UNKNOWN);
		}

		return succDetState;	
	}
	
	
	
	
	
	/**
	 * Return all states succ such that (state, symbol, succ) is inductive.
	 */
	private Set<IPredicate> getInternalSuccs(
			IPredicate state,
			CodeBlock symbol) {
		Set<IPredicate> succs = getInternalSuccsCache(state, symbol);
		if (succs == null) {
			succs = new HashSet<IPredicate>();
			for (final IPredicate succCandidate : mNwa.getStates()) {
				if (isInductiveInternalSuccessor(state, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
			putInternalSuccsCache(state, symbol, succs);
		}
		else {
			mAnswerInternalCache++;
		}
		return succs;
	}

	/**
	 * Store in the cache that succs is the set of all states succ such that
	 * (state, symbol, succ) is inductive.
	 */
	private void putInternalSuccsCache(
			IPredicate state,
			CodeBlock symbol,
			Set<IPredicate> succs) {
		Map<CodeBlock, Set<IPredicate>> symbol2succs = 
			mInductiveSuccsCache.get(state);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<CodeBlock, Set<IPredicate>>();
			mInductiveSuccsCache.put(state, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that (state, symbol, succ)
	 * is inductive. If the cache knows this result succs is returned, otherwise
	 * null is returned.
	 */
	private Set<IPredicate> getInternalSuccsCache(
			IPredicate state,
			CodeBlock symbol) {
		final Map<CodeBlock, Set<IPredicate>> symbol2succs = 
			mInductiveSuccsCache.get(state);
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
	 * Return all states succ such that (state, symbol, succ) is inductive.
	 */
	private Set<IPredicate> getCallSuccs(
			IPredicate state,
			Call symbol) {
		Set<IPredicate> succs = getCallSuccsCache(state, symbol);
		if (succs == null) {
			succs = new HashSet<IPredicate>();
			for (final IPredicate succCandidate : mNwa.getStates()) {
				if (inductiveCallSuccessor(state, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
			putCallSuccsCache(state, symbol, succs);
		}
		else {
			mAnswerCallCache++;
		}
		return succs;
	}

	
	/**
	 * Store in the cache that succs is the set of all states succ such that
	 * (state, symbol, succ) is inductive.
	 */
	private void putCallSuccsCache(
			IPredicate state,
			CodeBlock symbol,
			Set<IPredicate> succs) {
		Map<CodeBlock, Set<IPredicate>> symbol2succs = 
			mInductiveCallSuccsCache.get(state);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<CodeBlock, Set<IPredicate>>();
			mInductiveCallSuccsCache.put(state, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that (state, symbol, succ)
	 * is inductive. If the cache knows this result succs is returned, otherwise
	 * null is returned.
	 */
	private Set<IPredicate> getCallSuccsCache(
			IPredicate state,
			CodeBlock symbol) {
		final Map<CodeBlock, Set<IPredicate>> symbol2succs = 
			mInductiveCallSuccsCache.get(state);
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
	 * Returns true iff (state,symbol,succ) is inductive. Fist the interpolant
	 * automaton is queried for a yes-answer, afterwards the solver is
	 * queried for a yes/no/unknown-answer. We querying the interpolant
	 * automaton for two reasons:
	 * <ul>
	 * <li> a query to the solver is expensive
	 * <li> if we do not compute interpolants for every location we have 
	 * unknown-labeled states for which the solver can not give a yes/no-answer.
	 * </ul> 
	 */
	private boolean isInductiveInternalSuccessor(
			IPredicate  state,
			CodeBlock symbol,
			IPredicate  succ) {
		for (final IPredicate succInt : mNwa.succInternal(state, symbol)) {
			if (succInt.equals(succ)) {
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
		else {
			return false;	
		}
	}
	
	/**
	 * Returns true iff (state,symbol,succ) is inductive. Fist the interpolant
	 * automaton is queried for a yes-answer, afterwards the solver is
	 * queried for a yes/no/unknown-answer. We querying the interpolant
	 * automaton for two reasons:
	 * <ul>
	 * <li> a query to the solver is expensive
	 * <li> if we do not compute interpolants for every location we have 
	 * unknown-labeled states for which the solver can not give a yes/no-answer.
	 * </ul> 
	 */
	private boolean inductiveCallSuccessor(
			IPredicate  state,
			Call symbol,
			IPredicate  succ) {
		for (final IPredicate succCall : mNwa.succCall(state,symbol)) {
			if (succCall.equals(succ)) {
				mAnswerCallAutomaton++;
				return true;
			}
		}
		final IPredicate presentPs = state;
		final IPredicate succPs = succ;
		final Validity sat = mHoareTriplechecker.checkCall(presentPs, symbol, succPs);
		mAnswerCallSolver++;
		if (sat == Validity.VALID) {
			return true;
		}
		return false;
	}
	
	
	
	
	/**
	 * Return all states succ such that (state, linPred, symbol, succ) is
	 * inductive.
	 */
	private Set<IPredicate> getReturnSuccs(
			IPredicate state,
			IPredicate linPred, 
			Return symbol) {
		Set<IPredicate> succs = getReturnSuccsCache(state, linPred, symbol);
		if (succs == null) {
			succs = new HashSet<IPredicate>();
			for (final IPredicate succCandidate : mNwa.getStates()) {
				if (isInductiveReturnSuccessor(state, linPred, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
			putReturnSuccsCache(state, linPred, symbol, succs);
		}
		else {
			mAnswerReturnCache++;
		}
		return succs;
	}
	
	/**
	 * Store in the cache that succs is the set of all states succ such that
	 * (state, linPred, symbol, succ) is inductive.
	 */
	private void putReturnSuccsCache(
			IPredicate state,
			IPredicate linPred, 
			CodeBlock symbol,
			Set<IPredicate> succs) {
		Map<IPredicate, Map<CodeBlock, Set<IPredicate>>> linPred2symbol2succs = 
			mInductiveReturnSuccsCache.get(state);
		if (linPred2symbol2succs == null) {
			linPred2symbol2succs = 
				new HashMap<IPredicate, Map<CodeBlock, Set<IPredicate>>>();
			mInductiveReturnSuccsCache.put(state, linPred2symbol2succs);	
		}
		Map<CodeBlock, Set<IPredicate>> symbol2succs = 
			linPred2symbol2succs.get(linPred);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<CodeBlock, Set<IPredicate>>();
			linPred2symbol2succs.put(linPred, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that 
	 * (state, linPred, symbol, succ) is inductive. If the cache knows this 
	 * result succs is returned, otherwise
	 * null is returned.
	 */
	private Set<IPredicate> getReturnSuccsCache(
			IPredicate state,
			IPredicate linPred, 
			CodeBlock symbol) {
		final Map<IPredicate, Map<CodeBlock, Set<IPredicate>>> linPred2symbol2succs = 
			mInductiveReturnSuccsCache.get(state);
		if (linPred2symbol2succs == null) {
			return null;
		}
		final Map<CodeBlock, Set<IPredicate>> symbol2succs = 
			linPred2symbol2succs.get(linPred);
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
	 * Returns true iff (state,callerState,symbol,succ) is inductive.
	 * Fist the interpolant automaton is queried for a yes-answer, afterwards 
	 * the solver is queried for a yes/no/unknown-answer. We querying the 
	 * interpolant automaton for two reasons:
	 * <ul>
	 * <li> a query to the solver is expensive
	 * <li> if we do not compute interpolants for every location we have 
	 * unknown-labeled states for which the solver can not give a yes/no-answer.
	 * </ul> 
	 */
	private boolean isInductiveReturnSuccessor(
			IPredicate  state,
			IPredicate  callerState,
			Return symbol,
			IPredicate  succ) {
		for (final IPredicate succRet : mNwa.succReturn(state,callerState, symbol)) {
			if (succRet.equals(succ)) {
				mAnswerReturnAutomaton++;
				return true;
			}
		}
		final IPredicate presentPs = state;
		final IPredicate callerPs = callerState;
		final IPredicate succPs = succ;
		final Validity sat = 
			mHoareTriplechecker.checkReturn(presentPs, callerPs, symbol, succPs);
		mAnswerReturnSolver++;
		if (sat == Validity.VALID) {
			return true;
		}
		return false;
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
	public IPredicate getState(
			DeterminizedState<CodeBlock, IPredicate> determinizedState) {
		return determinizedState.getContent(mStateFactory);
	}


	


	








}
