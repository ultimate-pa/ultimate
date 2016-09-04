/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 Daniel Tischner
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizeDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;


public class Determinize<LETTER,STATE> extends UnaryNwaOperation<LETTER, STATE> {
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	private final DeterminizeNwa<LETTER, STATE> mDeterminized;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> mResult;
	private final IStateDeterminizer<LETTER,STATE> mStateDeterminizer;
	private final IStateFactory<STATE> mStateFactory;
	
	/**
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param operand operand
	 * @throws AutomataOperationCanceledException if timeout exceeds
	 */
	public Determinize(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER,STATE> operand)
					throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mStateDeterminizer =
				new PowersetDeterminizer<LETTER, STATE>(mOperand, true, stateFactory);
		mStateFactory = stateFactory;
		mLogger.info(startMessage());
		mDeterminized = new DeterminizeNwa<LETTER, STATE>(
				mServices, mOperand, mStateDeterminizer, mStateFactory);
		mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mDeterminized);
		mLogger.info(exitMessage());
	}
	
	/**
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param operand operand
	 * @param predefinedInitials predefined initial states
	 * @throws AutomataOperationCanceledException if timeout exceeds
	 */
	public Determinize(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER,STATE> operand,
			final Set<STATE> predefinedInitials)
					throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mStateDeterminizer =
				new PowersetDeterminizer<LETTER, STATE>(mOperand, true, stateFactory);
		mStateFactory = stateFactory;
		mLogger.info(startMessage());
		mDeterminized = new DeterminizeNwa<LETTER, STATE>(
				mServices, mOperand, mStateDeterminizer, mStateFactory,
				predefinedInitials, false);
		mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mDeterminized);
		mLogger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "determinize";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Result "
				+ mResult.sizeInformation();
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}


	@Override
	public boolean checkResult(final IStateFactory<STATE> sf) throws AutomataLibraryException {
		boolean correct = true;
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			mLogger.info("Start testing correctness of " + operationName());

			final INestedWordAutomaton<LETTER, STATE> resultDD =
					(new DeterminizeDD<LETTER, STATE>(mServices, sf, mOperand)).getResult();
			// should recognize same language as old computation
			correct &= new IsIncluded<>(mServices, sf, resultDD, mResult).getResult();
			correct &= new IsIncluded<>(mServices, sf, mResult, resultDD).getResult();
			mLogger.info("Finished testing correctness of " + operationName());
		} else {
			mLogger.warn("result was not tested");
		}
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices,
					operationName() + "Failed", "language is different",
					mOperand);
		}
		return correct;
	}
}
