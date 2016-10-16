/*
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IPartition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DoubleDeckerVisitor.ReachFinal;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This is the superclass of most minimization classes.
 * It provides a correctness check for all subclasses and an optional DFA check
 * for subclasses that only work for DFAs.
 * <p>
 * All subclasses must implement the
 * #{@link de.uni_freiburg.informatik.ultimate.automata.IOperation} interface
 * in order to be found by the <code>AutomataScriptInterpreter</code>.
 * 
 * @author Christian Schilling
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class AbstractMinimizeNwa<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE>
		implements IMinimizeNwa<LETTER, STATE> {
	/**
	 * The operand.
	 */
	protected final INestedWordAutomaton<LETTER, STATE> mOperand;
	/**
	 * The operation name.
	 */
	protected final String mName;
	
	/**
	 * StateFactory for the construction of states of the resulting automaton.
	 */
	protected final IStateFactory<STATE> mStateFactory;
	/**
	 * The result automaton.
	 */
	private INestedWordAutomaton<LETTER, STATE> mResult;
	/**
	 * A temporary automaton for result construction.
	 */
	private NestedWordAutomaton<LETTER, STATE> mTemporaryResult;
	/**
	 * A map 'old state -> new state'.
	 */
	private Map<STATE, STATE> mOldState2NewState;
	
	/**
	 * This constructor should be called by all subclasses and only by them.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param name
	 *            operation name
	 * @param operand
	 *            input automaton
	 */
	protected AbstractMinimizeNwa(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory, final String name,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services);
		mOperand = operand;
		mName = name;
		mResult = null;
		mTemporaryResult = null;
		mOldState2NewState = null;
		
		mStateFactory = (stateFactory == null)
				? operand.getStateFactory()
				: stateFactory;
		mLogger.info(startMessage());
	}
	
	/**
	 * This constructor should be called by all subclasses and only by them.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param name
	 *            operation name
	 * @param operand
	 *            input automaton
	 */
	protected AbstractMinimizeNwa(
			final AutomataLibraryServices services,
			final String name,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		this(services, operand.getStateFactory(), name, operand);
	}
	
	/* ------ interface methods ------ */
	
	@Override
	public final String operationName() {
		return mName;
	}
	
	@Override
	public final String exitMessage() {
		return "Finished " + operationName() + ". Reduced states from "
				+ mOperand.size() + " to " + getResult().size() + '.';
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		if (mResult == null) {
			throw new NoSuchElementException("The result is not ready yet.");
		}
		return mResult;
	}
	
	/**
	 * Subclasses which need to add specific data should call this method first and extend the result.
	 */
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics result = new AutomataOperationStatistics();
		
		final int inputSize = mOperand.size();
		final int outputSize = mResult.size();
		
		result.addKeyValuePair(StatisticsType.STATES_INPUT, inputSize);
		result.addKeyValuePair(StatisticsType.STATES_OUTPUT, outputSize);
		result.addDifferenceData(StatisticsType.STATES_INPUT, StatisticsType.STATES_OUTPUT,
				StatisticsType.STATES_REDUCTION_ABSOLUTE);
		result.addPercentageDataInverted(StatisticsType.STATES_INPUT, StatisticsType.STATES_OUTPUT,
				StatisticsType.STATES_REDUCTION_RELATIVE);
		
		/* TODO Christian 2016-10-12: make this optional, this has performance impact */
		if (true) {
			// Input automaton
			final Analyze<LETTER, STATE> inputAnalyzer = new Analyze<>(mServices, mOperand, true);
			final int inputTransitions = inputAnalyzer.getNumberOfTransitions(SymbolType.TOTAL);
			result.addKeyValuePair(StatisticsType.BUCHI_NONDETERMINISTIC_STATES,
					inputAnalyzer.getNumberOfNondeterministicStates());
			result.addKeyValuePair(StatisticsType.BUCHI_ALPHABET_SIZE,
					inputAnalyzer.getNumberOfSymbols(SymbolType.TOTAL));
			result.addKeyValuePair(StatisticsType.BUCHI_TRANSITIONS, inputTransitions);
			result.addKeyValuePair(StatisticsType.BUCHI_TRANSITION_DENSITY_MILLION,
					(int) Math.round(inputAnalyzer.getTransitionDensity(SymbolType.TOTAL) * 1_000_000));
			result.addKeyValuePair(StatisticsType.ALPHABET_SIZE_INTERNAL_INPUT,
					inputAnalyzer.getNumberOfSymbols(SymbolType.INTERNAL));
			result.addKeyValuePair(StatisticsType.ALPHABET_SIZE_CALL_INPUT,
					inputAnalyzer.getNumberOfSymbols(SymbolType.CALL));
			result.addKeyValuePair(StatisticsType.ALPHABET_SIZE_RETURN_INPUT,
					inputAnalyzer.getNumberOfSymbols(SymbolType.RETURN));
			result.addKeyValuePair(StatisticsType.TRANSITIONS_INTERNAL_INPUT,
					inputAnalyzer.getNumberOfTransitions(SymbolType.INTERNAL));
			result.addKeyValuePair(StatisticsType.TRANSITIONS_CALL_INPUT,
					inputAnalyzer.getNumberOfTransitions(SymbolType.CALL));
			result.addKeyValuePair(StatisticsType.TRANSITIONS_RETURN_INPUT,
					inputAnalyzer.getNumberOfTransitions(SymbolType.RETURN));
			
			// Output automaton
			final Analyze<LETTER, STATE> outputAnalyzer = new Analyze<>(mServices, mResult, true);
			final int outputTransitions = outputAnalyzer.getNumberOfTransitions(SymbolType.TOTAL);
			result.addKeyValuePair(StatisticsType.RESULT_NONDETERMINISTIC_STATES,
					outputAnalyzer.getNumberOfNondeterministicStates());
			result.addKeyValuePair(StatisticsType.RESULT_ALPHABET_SIZE,
					outputAnalyzer.getNumberOfSymbols(SymbolType.TOTAL));
			result.addKeyValuePair(StatisticsType.RESULT_TRANSITIONS, outputTransitions);
			result.addKeyValuePair(StatisticsType.RESULT_TRANSITION_DENSITY_MILLION,
					(int) Math.round(outputAnalyzer.getTransitionDensity(SymbolType.TOTAL) * 1_000_000));
			result.addKeyValuePair(StatisticsType.REMOVED_TRANSITIONS, inputTransitions - outputTransitions);
			result.addKeyValuePair(StatisticsType.ALPHABET_SIZE_INTERNAL_OUTPUT,
					inputAnalyzer.getNumberOfSymbols(SymbolType.INTERNAL));
			result.addKeyValuePair(StatisticsType.ALPHABET_SIZE_CALL_OUTPUT,
					inputAnalyzer.getNumberOfSymbols(SymbolType.CALL));
			result.addKeyValuePair(StatisticsType.ALPHABET_SIZE_RETURN_OUTPUT,
					inputAnalyzer.getNumberOfSymbols(SymbolType.RETURN));
			result.addKeyValuePair(StatisticsType.TRANSITIONS_INTERNAL_OUTPUT,
					inputAnalyzer.getNumberOfTransitions(SymbolType.INTERNAL));
			result.addKeyValuePair(StatisticsType.TRANSITIONS_CALL_OUTPUT,
					inputAnalyzer.getNumberOfTransitions(SymbolType.CALL));
			result.addKeyValuePair(StatisticsType.TRANSITIONS_RETURN_OUTPUT,
					inputAnalyzer.getNumberOfTransitions(SymbolType.RETURN));
		}
		
		return result;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + operationName());
		}
		
		// call submethod to enable overriding by subclasses
		final Pair<Boolean, String> equivalenceResult = checkResultHelper(stateFactory);
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + operationName());
		}
		if (!equivalenceResult.getFirst()) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, operationName() + "Failed",
					equivalenceResult.getSecond(), mOperand);
		}
		return equivalenceResult.getFirst();
	}
	
	/**
	 * Returns a Map from states of the input automaton to states of the output
	 * automaton. The output results from merging states. The image of a state
	 * <i>oldState</i> is the block of merged states containing <i>oldState</i>.
	 * This method can only be used when the minimization has finished.
	 * <p>
	 * NOTE: The map must be robust against queries for states which did not
	 * exist in the input automaton. The expected value is 'null', but
	 * not, e.g., a NullPointerException.
	 * 
	 * @return map from input automaton states to output automaton states
	 */
	public Map<STATE, STATE> getOldState2newState() {
		if (mOldState2NewState == null) {
			throw new NoSuchElementException(
					"No map from old states to new states was added.");
		}
		return mOldState2NewState;
	}
	
	/* ------ result construction ------ */
	
	/**
	 * Passes the result directly.
	 * 
	 * @param result
	 *            result automaton
	 */
	protected final void directResultConstruction(
			final INestedWordAutomaton<LETTER, STATE> result) {
		if (mResult != null) {
			throw new AssertionError(
					"The result has already been constructed.");
		} else if (mTemporaryResult != null) {
			throw new AssertionError(
					"The result construction has already been started.");
		}
		mResult = result;
	}
	
	/**
	 * Constructs the result from a partition.
	 * 
	 * @param partition
	 *            partition data structure
	 * @param addMapping
	 *            true iff mapping 'old state -> new state' is added
	 */
	protected void constructResultFromPartition(final IPartition<STATE> partition, final boolean addMapping) {
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
				new QuotientNwaConstructor<>(mServices, mStateFactory, mOperand, partition, addMapping);
		constructResultFromQuotientConstructor(quotientNwaConstructor);
	}
	
	/**
	 * Constructs the result from a partition.
	 * 
	 * @param unionFind
	 *            union-find data structure
	 * @param addMapping
	 *            true iff mapping 'old state -> new state' is added
	 */
	protected void constructResultFromUnionFind(final UnionFind<STATE> unionFind, final boolean addMapping) {
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
				new QuotientNwaConstructor<>(mServices, mStateFactory, mOperand, unionFind, addMapping);
		constructResultFromQuotientConstructor(quotientNwaConstructor);
	}
	
	/**
	 * Passes the result directly from a
	 * #{@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.QuotientNwaConstructor}
	 * .
	 * 
	 * @param constructor
	 *            quotient constructor
	 */
	private void constructResultFromQuotientConstructor(
			final QuotientNwaConstructor<LETTER, STATE> constructor) {
		directResultConstruction(constructor.getResult());
		final Map<STATE, STATE> map = constructor.getOldState2newState();
		if (map != null) {
			setOld2NewStateMap(map);
		}
	}
	
	/**
	 * Starts construction of result (must be called first).
	 */
	protected final void startResultConstruction() {
		if (mResult != null) {
			throw new AssertionError(
					"The result has already been constructed.");
		}
		mTemporaryResult = new DoubleDeckerAutomaton<>(
				mServices,
				mOperand.getInternalAlphabet(),
				mOperand.getCallAlphabet(),
				mOperand.getReturnAlphabet(),
				mStateFactory);
	}
	
	/**
	 * Adds a state.
	 * 
	 * @param isInitial
	 *            is the state initial?
	 * @param isFinal
	 *            is the state accepting?
	 * @param state
	 *            state
	 */
	protected final void addState(final boolean isInitial,
			final boolean isFinal, final STATE state) {
		mTemporaryResult.addState(isInitial, isFinal, state);
	}
	
	/**
	 * Adds a state from a collection of states.
	 * 
	 * @param isInitial
	 *            is the state initial?
	 * @param isFinal
	 *            is the state accepting?
	 * @param oldStates
	 *            collection of states
	 * @return new state (automatically added to the result)
	 */
	protected final STATE addState(final boolean isInitial,
			final boolean isFinal, final Collection<STATE> oldStates) {
		assert !oldStates.isEmpty();
		final STATE newState = mStateFactory.minimize(oldStates);
		mTemporaryResult.addState(isInitial, isFinal, newState);
		return newState;
	}
	
	/**
	 * Adds an internal transition.
	 * 
	 * @param pred
	 *            predecessor
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor
	 */
	protected final void addInternalTransition(final STATE pred,
			final LETTER letter, final STATE succ) {
		mTemporaryResult.addInternalTransition(pred, letter, succ);
	}
	
	/**
	 * Adds a call transition.
	 * 
	 * @param pred
	 *            predecessor
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor
	 */
	protected final void addCallTransition(final STATE pred,
			final LETTER letter, final STATE succ) {
		mTemporaryResult.addCallTransition(pred, letter, succ);
	}
	
	/**
	 * Adds a return transition.
	 * 
	 * @param pred
	 *            predecessor
	 * @param hier
	 *            hierarchical predecessor
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor
	 */
	protected final void addReturnTransition(final STATE pred,
			final STATE hier, final LETTER letter, final STATE succ) {
		mTemporaryResult.addReturnTransition(pred, hier, letter, succ);
	}
	
	/**
	 * Finishes construction of result (must be called last).
	 * 
	 * @param oldState2newState
	 *            map 'old state -> new state'
	 */
	protected final void finishResultConstruction(
			final Map<STATE, STATE> oldState2newState,
			final boolean constructDoubleDeckerInformation) {
		if (oldState2newState != null) {
			setOld2NewStateMap(oldState2newState);
			
			// double decker can only be constructed if mapping is provided
			if (constructDoubleDeckerInformation) {
				constructDoubleDeckerInformation();
			}
		}
		
		mResult = mTemporaryResult;
		mTemporaryResult = null;
	}
	
	/**
	 * Adds double decker information to the result.
	 */
	@SuppressWarnings("squid:S1698")
	private void constructDoubleDeckerInformation() {
		assert (mTemporaryResult instanceof DoubleDeckerAutomaton) : "The result must be a DoubleDeckerAutomaton.";
		final DoubleDeckerAutomaton<LETTER, STATE> result =
				(DoubleDeckerAutomaton<LETTER, STATE>) mTemporaryResult;
		assert (mOperand instanceof IDoubleDeckerAutomaton) : "The operand must be an IDoubleDeckerAutomaton.";
		final IDoubleDeckerAutomaton<LETTER, STATE> operand =
				(IDoubleDeckerAutomaton<LETTER, STATE>) mOperand;
		assert (!result.up2DownIsSet()) : "The down state map was already set.";
		assert (mOldState2NewState != null) : "Need the mapping for construction.";
		
		final Map<STATE, Map<STATE, ReachFinal>> up2Down = new HashMap<>();
		result.setUp2Down(up2Down);
		
		final STATE oldEmptyStackState = mOperand.getEmptyStackState();
		final STATE newEmptyStackState = mStateFactory.createEmptyStackState();
		
		for (final STATE oldState : mOperand.getStates()) {
			final STATE newState = mOldState2NewState.get(oldState);
			
			// get down state map
			Map<STATE, ReachFinal> downStateMap = up2Down.get(newState);
			if (downStateMap == null) {
				downStateMap = new HashMap<>();
				up2Down.put(newState, downStateMap);
			}
			
			// add down states
			for (final STATE oldDownState : operand.getDownStates(oldState)) {
				// new state
				final STATE resultDownState;
				
				// equals() not necessary here
				if (oldDownState == oldEmptyStackState) {
					// empty stack symbol
					resultDownState = newEmptyStackState;
				} else {
					// "normal" stack symbol
					resultDownState = mOldState2NewState.get(oldDownState);
				}
				
				// update map
				downStateMap.put(resultDownState, ReachFinal.UNKNOWN);
			}
		}
	}
	
	/**
	 * Setter for map 'old state -> new state'.
	 * 
	 * @param oldState2newState
	 *            map 'old state -> new state'
	 */
	protected final void setOld2NewStateMap(
			final Map<STATE, STATE> oldState2newState) {
		if (oldState2newState == null) {
			throw new AssertionError(
					"The map must not be set to null.");
		} else if (mOldState2NewState != null) {
			throw new AssertionError(
					"The map has already been set.");
		}
		mOldState2NewState = Collections.unmodifiableMap(oldState2newState);
	}
	
	/* ------ other helper methods ------ */
	
	/**
	 * This method checks whether the input automaton is a DFA.
	 * <p>
	 * That means the automaton must be deterministic and must not contain
	 * any call and return transitions.
	 * 
	 * @return true iff input automaton is a DFA
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	protected final boolean isDfa() throws AutomataOperationCanceledException {
		return (isDeterministic() && isFiniteAutomaton());
	}
	
	/**
	 * This method checks whether the input automaton is deterministic.
	 * 
	 * @return true iff automaton is deterministic
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	protected final boolean isDeterministic()
			throws AutomataOperationCanceledException {
		return new IsDeterministic<>(mServices, mOperand).getResult();
	}
	
	/**
	 * This method checks whether the automaton is a finite automaton.
	 * That means it must not contain any call and return letter.
	 * <p>
	 * NOTE: Return transitions would not do any harm when no call
	 * transitions exist, but they are considered bad nevertheless.
	 * <p>
	 * NOTE: The method checks something stronger, namely that the respective
	 * alphabets are empty.
	 * 
	 * @return true iff automaton contains no call and return letters
	 */
	protected final boolean isFiniteAutomaton() {
		return ((mOperand.getCallAlphabet().size() == 0)
				&& (mOperand.getReturnAlphabet().size() == 0));
	}
	
	/**
	 * This method throws an exception iff the operation should be terminated.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             thrown to enforce termination.
	 */
	protected final void checkForContinuation()
			throws AutomataOperationCanceledException {
		if (isCancellationRequested()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}
	}
	
	/**
	 * Performs the real {@link #checkResult(IStateFactory) result check}.
	 * <p>
	 * Subclasses can override this method for more specific result checks.<br>
	 * By default language equivalence between operand and result is checked.
	 * 
	 * @param stateFactory
	 *            state factory
	 * @return pair <tt>(b, m)</tt> where <tt>b = true</tt> iff result check succeeded, otherwise <tt>m</tt> contains an
	 *         error message
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	protected Pair<Boolean, String> checkResultHelper(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// by default only check language equivalence
		return checkLanguageEquivalence(stateFactory);
	}
	
	/**
	 * This method computes the capacity size for hash sets and hash maps given
	 * the expected number of elements to avoid resizing.
	 * 
	 * @param size
	 *            expected number of elements before resizing
	 * @return the parameter for initializing the hash structure
	 */
	@SuppressWarnings("squid:S2164")
	protected final int computeHashCap(final int size) {
		final float inverseOfPointSevenFive = 1.34f;
		return (int) (size * inverseOfPointSevenFive + 1);
	}
}
