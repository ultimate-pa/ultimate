/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Check if the languages of a given {@link IPetriNet} and a given
 * {@link INestedWordAutomaton} are identical.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class IsEquivalent<LETTER, STATE>
		extends GeneralOperation<LETTER, STATE, IPetriNet2FiniteAutomatonStateFactory<STATE>> {
	private final IPetriNet<LETTER, STATE> mPetriNet;
	private final INestedWordAutomaton<LETTER, STATE> mAutomaton;
	private final IPetriNet2FiniteAutomatonStateFactory<STATE> mPetriNet2FiniteAutomatonStateFactory;
	private final INwaInclusionStateFactory mNwaInclusionStateFactory;
	private final boolean mResult;

	public IsEquivalent(final AutomataLibraryServices services,
			IPetriNet2FiniteAutomatonStateFactory<STATE> petriNet2FiniteAutomatonStateFactory,
			INwaInclusionStateFactory nwaInclusionStateFactory, final IPetriNet<LETTER, STATE> petriNet,
			INestedWordAutomaton<LETTER, STATE> automaton) throws AutomataLibraryException {
		super(services);
		mPetriNet = petriNet;
		mAutomaton = automaton;
		mPetriNet2FiniteAutomatonStateFactory = petriNet2FiniteAutomatonStateFactory;
		mNwaInclusionStateFactory = nwaInclusionStateFactory;
		printStartMessage();
		final INestedWordAutomaton<LETTER, STATE> petriNetAsAutomaton = (new PetriNet2FiniteAutomaton<LETTER, STATE>(
				mServices, mPetriNet2FiniteAutomatonStateFactory, mPetriNet)).getResult();
		mResult = new de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent<LETTER, STATE>(
				mServices, mNwaInclusionStateFactory, petriNetAsAutomaton, mAutomaton).getResult();
		printExitMessage();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " language is " + (mResult ? "empty" : "not empty");
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		mLogger.warn("Not yet implemented: result check for " + this.getClass().getSimpleName());
		return true;
	}
}
