/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;


public class Complement<LETTER,STATE>
		extends UnaryNwaOperation<LETTER, STATE>
		implements IOperation<LETTER,STATE> {

	private DeterminizeNwa<LETTER,STATE> mDeterminized;
	private ComplementDeterministicNwa<LETTER,STATE> mComplement;
	private NestedWordAutomatonReachableStates<LETTER,STATE> mResult;
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	private final StateFactory<STATE> mStateFactory;
	
	
	/**
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param stateDeterminizer state determinizer
	 * @param operand operand
	 * @throws AutomataLibraryException if construction fails
	 */
	public Complement(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER,STATE> operand,
			final IStateDeterminizer<LETTER,STATE> stateDeterminizer,
			final StateFactory<STATE> stateFactory)
					throws AutomataLibraryException {
		super(services, operand);
		mStateDeterminizer = stateDeterminizer;
		mStateFactory = stateFactory;
		mLogger.info(startMessage());
		computeComplement();
		mLogger.info(exitMessage());
	}
	
	/**
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param operand operand
	 * @throws AutomataLibraryException if construction fails
	 */
	public Complement(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER,STATE> operand)
					throws AutomataLibraryException {
		this(services, operand,
				new PowersetDeterminizer<LETTER, STATE>(operand, true, stateFactory),
				stateFactory);
	}
	
	private void computeComplement() throws AutomataLibraryException {
		if (mOperand instanceof DeterminizeNwa) {
			mDeterminized = (DeterminizeNwa<LETTER, STATE>) mOperand;
			mComplement = new ComplementDeterministicNwa<LETTER, STATE>(mDeterminized);
			mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mComplement);
			return;
		}
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			final boolean success = tryWithoutDeterminization();
			if (success) {
				return;
			}
		}
		mDeterminized = new DeterminizeNwa<LETTER, STATE>(mServices, mOperand,
				mStateDeterminizer, mStateFactory, null, true);
		mComplement = new ComplementDeterministicNwa<LETTER, STATE>(mDeterminized);
		mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(
				mServices, mComplement);
	}
	
	private boolean tryWithoutDeterminization() throws AutomataLibraryException {
		assert (mStateDeterminizer instanceof PowersetDeterminizer);
		final TotalizeNwa<LETTER, STATE> totalized =
				new TotalizeNwa<LETTER, STATE>(mOperand, mStateFactory);
		final ComplementDeterministicNwa<LETTER,STATE> complemented =
				new ComplementDeterministicNwa<LETTER, STATE>(totalized);
		final NestedWordAutomatonReachableStates<LETTER, STATE> result =
				new NestedWordAutomatonReachableStates<LETTER, STATE>(
						mServices, complemented);
		if (!totalized.nonDeterminismInInputDetected()) {
			mComplement = complemented;
			mResult = result;
			mLogger.info(
					"Operand was deterministic. Have not used determinization.");
			return true;
		} else {
			mLogger.info(
					"Operand was not deterministic. Recomputing result with determinization.");
			return false;
		}
	}
	

	@Override
	public String operationName() {
		return "complement";
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Result "
				+ mResult.sizeInformation();
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
	
	
	@Override
	public boolean checkResult(final StateFactory<STATE> sf) throws AutomataLibraryException {
		boolean correct = true;
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			mLogger.info("Start testing correctness of " + operationName());

			// intersection of operand and result should be empty
			final INestedWordAutomatonSimple<LETTER, STATE> intersectionOperandResult =
					(new IntersectDD<LETTER, STATE>(mServices, mOperand, mResult)).getResult();
			correct &= (new IsEmpty<LETTER, STATE>(mServices, intersectionOperandResult)).getResult();
			final INestedWordAutomatonSimple<LETTER, STATE> resultDD =
					(new ComplementDD<LETTER, STATE>(mServices, sf, mOperand)).getResult();
			
			// should have same number of states as old complementation
			// does not hold, resultDD sometimes has additional sink state
			//		correct &= (resultDD.size() == mResult.size());
			
			// should recognize same language as old computation
			correct &= new IsIncluded<>(mServices, sf, resultDD, mResult).getResult();
			correct &= new IsIncluded<>(mServices, sf, mResult, resultDD).getResult();
			mLogger.info("Finished testing correctness of " + operationName());
		} else {
			mLogger.warn("operation not tested");
		}
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices,
					operationName() + "Failed", "language is different",
					mOperand);
		}
		return correct;
	}
	
}
