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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Emptiness check for Petri nets.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            place content type
 */
public final class IsEmpty<LETTER, STATE>
		extends UnaryNetOperation<LETTER, STATE, IPetriNet2FiniteAutomatonStateFactory<STATE>> {
	private final IPetriNet<LETTER, STATE> mOperand;
	private final boolean mResult;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 * @throws PetriNetNot1SafeException
	 */
	public IsEmpty(final AutomataLibraryServices services, final BoundedPetriNet<LETTER, STATE> operand)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());
		final PetriNetUnfolder<LETTER, STATE> unf =
				new PetriNetUnfolder<>(mServices, operand, EventOrderEnum.ERV, false, true);
		final PetriNetRun<LETTER, STATE> run = unf.getAcceptingRun();
		mResult = run == null;
		mLogger.info(exitMessage());
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " language is " + (mResult ? "empty" : "not empty");
	}

	@Override
	protected IPetriNet<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> finiteAutomaton =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mOperand)).getResult();
		final boolean automatonEmpty =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty<>(mServices,
						finiteAutomaton)).getResult();
		return mResult == automatonEmpty;
	}
}
