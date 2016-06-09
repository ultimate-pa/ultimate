/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Senwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.StateDeterminizerCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceSadd;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.SenwaWalker.ISuccessorVisitor;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class DifferenceSenwa<LETTER, STATE> implements 
								ISuccessorVisitor<LETTER, STATE>,
								IOperation<LETTER, STATE>,
								IOpWithDelayedDeadEndRemoval<LETTER, STATE>{
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
		
	private final INestedWordAutomatonOldApi<LETTER,STATE> minuend;
	private final INestedWordAutomatonOldApi<LETTER,STATE> subtrahend;
	
	private final IStateDeterminizer<LETTER,STATE> stateDeterminizer;
	
	private final StateFactory<STATE> contentFactory;

	private final Senwa<LETTER, STATE> mSenwa;
	
	private final SenwaWalker<LETTER, STATE> mSenwaWalker;
	
	
	
	
	
	/**
	 * Maps a state in resulting automaton to the DifferenceState for which it
	 * was created.
	 */
	Map<STATE,DifferenceState<LETTER,STATE>> mResult2Operand = 
			new HashMap<STATE,DifferenceState<LETTER,STATE>>();
	
	/**
	 * Maps a DifferenceState and an entry state to its representative in the
	 * resulting automaton.
	 */
	Map<DifferenceState<LETTER,STATE>,Map<DifferenceState<LETTER,STATE>,STATE>> mEntry2Operand2Result = 
			new HashMap<DifferenceState<LETTER,STATE>,Map<DifferenceState<LETTER,STATE>,STATE>>();
	
	
	
	
	@Override
	public String operationName() {
		return "differenceSenwa";
	}
	
	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Minuend " + 
			minuend.sizeInformation() + ". Subtrahend " + 
			subtrahend.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
		mSenwa.sizeInformation() + ". Max degree of Nondeterminism is " + 
		stateDeterminizer.getMaxDegreeOfNondeterminism();
	}
	
	
	
	
	public DifferenceSenwa(AutomataLibraryServices services,
			INestedWordAutomatonOldApi<LETTER,STATE> minuend,
			INestedWordAutomatonOldApi<LETTER,STATE> subtrahend)
					throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		contentFactory = minuend.getStateFactory();
		this.minuend = minuend;
		this.subtrahend = subtrahend;
		mLogger.info(startMessage());
		
		
		this.stateDeterminizer = new StateDeterminizerCache<LETTER, STATE>(
							new PowersetDeterminizer<LETTER,STATE>(subtrahend, true, contentFactory)); 
		
		mSenwa = new Senwa<LETTER, STATE>(mServices, 
				minuend.getInternalAlphabet(), minuend.getCallAlphabet(), 
				minuend.getReturnAlphabet(), minuend.getStateFactory());
		mSenwaWalker = new SenwaWalker<LETTER, STATE>(mServices, mSenwa, this, true);
		mLogger.info(exitMessage());
	}
	
	
	public DifferenceSenwa(
			AutomataLibraryServices services,
			INestedWordAutomaton<LETTER,STATE> minuend,
			INestedWordAutomaton<LETTER,STATE> subtrahend,
			IStateDeterminizer<LETTER,STATE> stateDeterminizer,
			boolean removeDeadEndsImmediately)
					throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		contentFactory = minuend.getStateFactory();
		if (minuend instanceof INestedWordAutomatonOldApi) {
			this.minuend = (INestedWordAutomatonOldApi<LETTER, STATE>) minuend;
		} else {
			this.minuend = (new RemoveUnreachable<LETTER,STATE>(mServices, minuend)).getResult();
		}
		if (subtrahend instanceof INestedWordAutomatonOldApi) {
			this.subtrahend = (INestedWordAutomatonOldApi<LETTER, STATE>) minuend;
		} else {
			this.subtrahend = (new RemoveUnreachable<LETTER,STATE>(mServices, minuend)).getResult();
		}
		mLogger.info(startMessage());
		
		
		this.stateDeterminizer = new StateDeterminizerCache<LETTER, STATE>(
				stateDeterminizer); 
		
		mSenwa = new Senwa<LETTER, STATE>(mServices,
				minuend.getInternalAlphabet(), minuend.getCallAlphabet(), 
				minuend.getReturnAlphabet(), minuend.getStateFactory());
		mSenwaWalker = new SenwaWalker<LETTER, STATE>(mServices, mSenwa, this, removeDeadEndsImmediately);
		mLogger.info(exitMessage());
	}
	
	
	
	
	
	private STATE getOrConstructResultState(
			DifferenceState<LETTER,STATE> diffEntry, 
			DifferenceState<LETTER,STATE> diffState, boolean isInitial) {
		assert minuend.getStates().contains(diffState.getMinuendState());
		assert minuend.getStates().contains(diffEntry.getMinuendState());
		Map<DifferenceState<LETTER,STATE>, STATE> op2res = mEntry2Operand2Result.get(diffEntry);
		if (op2res == null) {
			op2res = new HashMap<DifferenceState<LETTER,STATE>, STATE>();
			mEntry2Operand2Result.put(diffEntry, op2res);
		}
		STATE resState = op2res.get(diffState);
		if (resState == null) {
			
			resState = contentFactory.senwa(
					diffEntry.getState(contentFactory, stateDeterminizer), 
					diffState.getState(contentFactory, stateDeterminizer));
			op2res.put(diffState, resState);
			mResult2Operand.put(resState, diffState);
			final STATE resEntry = op2res.get(diffEntry);
			assert resEntry != null;
			mSenwa.addState(resState, isInitial, diffState.isFinal(), resEntry);
		}
		return resState;
	}
	
	private DifferenceState<LETTER,STATE> getOperandState(STATE resState) {
		assert mSenwa.getStates().contains(resState);
		final DifferenceState<LETTER,STATE> opState = mResult2Operand.get(resState);
		assert opState != null;
		return opState;
	}
	

	@Override
	public Iterable<STATE> getInitialStates() {
		
		final ArrayList<STATE> resInitials = 
				new ArrayList<STATE>(subtrahend.getInitialStates().size());
		final DeterminizedState<LETTER,STATE> detState = stateDeterminizer.initialState();
		for (final STATE minuState : minuend.getInitialStates()) {
			final boolean isFinal = minuend.isFinal(minuState) &&
											!detState.containsFinal();
			final DifferenceState<LETTER,STATE> diffState = 
				new DifferenceState<LETTER,STATE>(minuState, detState, isFinal);
			final STATE resState = getOrConstructResultState(diffState, diffState, true); 
			resInitials.add(resState);
		}
		return resInitials;
	}

	@Override
	public Iterable<STATE> visitAndGetInternalSuccessors(STATE resState) {
		final STATE resEntry = mSenwa.getEntry(resState);
		final DifferenceState<LETTER,STATE> diffEntry = getOperandState(resEntry);
		final Set<STATE> resSuccs = new HashSet<STATE>();
		final DifferenceState<LETTER,STATE> diffState = getOperandState(resState);
		final STATE minuState = diffState.getMinuendState();
		final DeterminizedState<LETTER,STATE> subtrState = diffState.getSubtrahendDeterminizedState();
		for (final LETTER letter : minuend.lettersInternal(minuState)) {
			for (final STATE minuSucc : minuend.succInternal(minuState, letter)) {
				final DeterminizedState<LETTER, STATE> subtrSucc = stateDeterminizer.internalSuccessor(subtrState, letter);
				final boolean isFinal = minuend.isFinal(minuSucc) &&
						!subtrSucc.containsFinal();
				final DifferenceState<LETTER, STATE> diffSucc = new DifferenceState<LETTER,STATE>(minuSucc, subtrSucc, isFinal);		
				
				final STATE resSucc = getOrConstructResultState(diffEntry, diffSucc, false);
				resSuccs.add(resSucc);
				mSenwa.addInternalTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetCallSuccessors(STATE resState) {
		final Set<STATE> resSuccs = new HashSet<STATE>();
		final DifferenceState<LETTER,STATE> diffState = getOperandState(resState);
		final STATE minuState = diffState.getMinuendState();
		final DeterminizedState<LETTER,STATE> subtrState = 
									diffState.getSubtrahendDeterminizedState();
		for (final LETTER letter : minuend.lettersCall(minuState)) {
			for (final STATE minuSucc : minuend.succCall(minuState, letter)) {
				final DeterminizedState<LETTER, STATE> subtrSucc = 
						stateDeterminizer.callSuccessor(subtrState, letter);
				final boolean isFinal = minuend.isFinal(minuSucc) &&
						!subtrSucc.containsFinal();
				final DifferenceState<LETTER, STATE> diffSucc = new 
						DifferenceState<LETTER,STATE>(minuSucc, subtrSucc, isFinal);		
				final STATE resSucc = getOrConstructResultState(diffSucc, diffSucc, false);
				resSuccs.add(resSucc);
				mSenwa.addCallTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetReturnSuccessors(STATE resState,
			STATE resHier) {
		final Set<STATE> resSuccs = new HashSet<STATE>();
		final DifferenceState<LETTER,STATE> diffState = getOperandState(resState);
		final STATE minuState = diffState.getMinuendState();
		final DeterminizedState<LETTER,STATE> subtrState = 
									diffState.getSubtrahendDeterminizedState();
		final DifferenceState<LETTER,STATE> diffHier = getOperandState(resHier);
		final STATE minuHier = diffHier.getMinuendState();
		final DeterminizedState<LETTER,STATE> subtrHier = 
									diffHier.getSubtrahendDeterminizedState();
		final STATE resHierEntry = mSenwa.getEntry(resHier);
		final DifferenceState<LETTER,STATE> diffHierEntry = getOperandState(resHierEntry);

		for (final LETTER letter : minuend.lettersReturn(minuState)) {
			for (final STATE minuSucc : minuend.succReturn(minuState, minuHier, letter)) {
				final DeterminizedState<LETTER, STATE> subtrSucc = 
						stateDeterminizer.returnSuccessor(subtrState, subtrHier, letter);
				final boolean isFinal = minuend.isFinal(minuSucc) &&
						!subtrSucc.containsFinal();
				final DifferenceState<LETTER, STATE> diffSucc = new 
						DifferenceState<LETTER,STATE>(minuSucc, subtrSucc, isFinal);		
				final STATE resSucc = getOrConstructResultState(diffHierEntry, diffSucc, false);
				resSuccs.add(resSucc);
				mSenwa.addReturnTransition(resState, resHier, letter, resSucc);
			}
		}
		return resSuccs;
	}
	
	@Override
	public Senwa<LETTER,STATE> getResult() throws AutomataOperationCanceledException {
		return mSenwa;
	}
	
	
//FIXME: Remove this
	public boolean removeStatesThatCanNotReachFinal(
			boolean computeRemovedDoubleDeckersAndCallSuccessors) {
		return mSenwaWalker.removeStatesThatCanNotReachFinal(
								computeRemovedDoubleDeckersAndCallSuccessors);
	}

	
	@Override
	public long getDeadEndRemovalTime() {
		return mSenwaWalker.getDeadEndRemovalTime();
	}

	@Override
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean removeDeadEnds() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean correct = true;
		if (stateDeterminizer instanceof PowersetDeterminizer) {
			mLogger.info("Start testing correctness of " + operationName());

			final INestedWordAutomatonOldApi<LETTER,STATE> resultSadd = (new DifferenceSadd<LETTER,STATE>(mServices, stateFactory, minuend, subtrahend)).getResult();
			correct &= (ResultChecker.nwaLanguageInclusion(mServices, resultSadd, mSenwa, stateFactory) == null);
			correct &= (ResultChecker.nwaLanguageInclusion(mServices, mSenwa, resultSadd, stateFactory) == null);
			if (!correct) {
			ResultChecker.writeToFileIfPreferred(mServices, operationName() + "Failed", "", minuend,subtrahend);
			}
			mLogger.info("Finished testing correctness of " + operationName());
		} else {
			mLogger.warn("Unable to test correctness if state determinzier is not the PowersetDeterminizer.");
		}
		return correct;
	}

}
