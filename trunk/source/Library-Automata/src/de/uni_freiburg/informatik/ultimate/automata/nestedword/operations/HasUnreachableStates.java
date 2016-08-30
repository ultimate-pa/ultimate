/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DoubleDeckerVisitor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;


/**
 * Check if an NWA contains states which are not reachable in any run.
 * Does not change the input automaton.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class HasUnreachableStates<LETTER,STATE>
		extends DoubleDeckerVisitor<LETTER,STATE>
		implements IOperation<LETTER,STATE> {
	private final Set<STATE> mVisitedStates = new HashSet<STATE>();
	private int mUnreachalbeStates = 0;

	/**
	 * @param services Ultimate services
	 * @param operand operand
	 * @throws AutomataOperationCanceledException if timeout exceeds
	 */
	public HasUnreachableStates(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER,STATE> operand)
					throws AutomataOperationCanceledException  {
		super(services);
		mTraversedNwa = operand;
		mLogger.info(startMessage());
		traverseDoubleDeckerGraph();
		for (final STATE state : mTraversedNwa.getStates()) {
			if (!mVisitedStates.contains(state)) {
				mUnreachalbeStates++;
				mLogger.warn("Unreachalbe state: " + state);
			}
		}
		mLogger.info(exitMessage());
	}

	@Override
	protected Collection<STATE> getInitialStates() {
		mVisitedStates.addAll(mTraversedNwa.getInitialStates());
		return mTraversedNwa.getInitialStates();
	}

	@Override
	protected Collection<STATE> visitAndGetInternalSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final STATE state = doubleDecker.getUp();
		final Set<STATE> succs = new HashSet<STATE>();
		for (final LETTER letter : mTraversedNwa.lettersInternal(state)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans :
					mTraversedNwa.internalSuccessors(state, letter)) {
				succs.add(trans.getSucc());
			}
		}
		mVisitedStates.addAll(succs);
		return succs;
	}
	
	

	@Override
	protected Collection<STATE> visitAndGetCallSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final STATE state = doubleDecker.getUp();
		final Set<STATE> succs = new HashSet<STATE>();
		for (final LETTER letter : mTraversedNwa.lettersCall(state)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans :
					mTraversedNwa.callSuccessors(state, letter)) {
				succs.add(trans.getSucc());
			}
		}
		mVisitedStates.addAll(succs);
		return succs;
	}
	
	

	@Override
	protected Collection<STATE> visitAndGetReturnSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final STATE state = doubleDecker.getUp();
		final STATE hier = doubleDecker.getDown();
		final Set<STATE> succs = new HashSet<STATE>();
		for (final LETTER letter : mTraversedNwa.lettersReturn(state)) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans :
					mTraversedNwa.returnSuccessors(state, hier, letter)) {
				succs.add(trans.getSucc());
			}
		}
		mVisitedStates.addAll(succs);
		return succs;
	}

	@Override
	public String operationName() {
		return "detectUnreachableStates";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand "
			+ mTraversedNwa.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand has "
			+ mUnreachalbeStates + " unreachalbe states";
	}
	
	public boolean result() {
		return mUnreachalbeStates != 0;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}
}
