/*
 * Copyright (C) 2022-2023 Daniel Küchler (kuechlerdaniel33@gmail.com)
 * Copyright (C) 2022-2023 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiPetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Emptiness check for Buchi-Petri-Nets.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            place content type
 *
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
 */
public final class BuchiIsEmpty<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final IPetriNetTransitionProvider<LETTER, PLACE> mOperand;
	private PetriNetLassoRun<LETTER, PLACE> mRun;

	public BuchiIsEmpty(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, operand, EventOrderEnum.ERV, false, true);
	}

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
	public BuchiIsEmpty(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());
		final PetriNetUnfolderBuchi<LETTER, PLACE> unfolder =
				new PetriNetUnfolderBuchi<>(mServices, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
		mRun = unfolder.getAcceptingRun();
		mLogger.info(exitMessage());
	}

	public PetriNetLassoRun<LETTER, PLACE> getRun() {
		return mRun;
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " language is " + (getResult() ? "empty" : "not empty");
	}

	@Override
	protected IPetriNetTransitionProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mRun == null;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> finiteAutomaton =
				(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
						(IBlackWhiteStateFactory<PLACE>) stateFactory, mOperand, null)).getResult();
		final var automatonResult =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty<>(mServices,
						finiteAutomaton));
		if (getResult() != automatonResult.getResult()) {
			return false;
		}
		if (getResult()) {
			return true;
		}
		final NestedWord<LETTER> nestedstemWord = NestedWord.nestedWord(getRun().getStem().getWord());
		final NestedWord<LETTER> nestedloopWord = NestedWord.nestedWord(getRun().getLoop().getWord());
		final NestedLassoWord<LETTER> nestedLassoWord = new NestedLassoWord<>(nestedstemWord, nestedloopWord);
		return new BuchiAccepts<>(mServices, finiteAutomaton, nestedLassoWord).getResult();
	}
}
