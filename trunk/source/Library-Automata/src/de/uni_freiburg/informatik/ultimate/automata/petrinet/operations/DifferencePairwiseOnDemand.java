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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetAndAutomataInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author schaetzc@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in the alphabet of minuend Petri net, subtrahend DFA, and difference Petri net
 * @param <PLACE>
 *            Type of places in minuend and difference Petri net
 * @param <CRSF>
 *            Type of factory needed to check the result of this operation in {@link #checkResult(CRSF)}
 */
public final class DifferencePairwiseOnDemand
		<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNetAndAutomataInclusionStateFactory<PLACE>> {


	private final IPetriNet<LETTER, PLACE> mMinuend;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> mSubtrahend;
	private final IBlackWhiteStateFactory<PLACE> mContentFactory;

	private final BoundedPetriNet<LETTER, PLACE> mResult;



	public <SF extends IBlackWhiteStateFactory<PLACE> & ISinkStateFactory<PLACE>> DifferencePairwiseOnDemand(
			final AutomataLibraryServices services, final SF factory,
			final IPetriNet<LETTER, PLACE> minuendNet,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> subtrahendDfa) throws AutomataOperationCanceledException {
		super(services);
		mMinuend = minuendNet;
		mSubtrahend = subtrahendDfa;
		mContentFactory = factory;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final DifferencePetriNet<LETTER, PLACE> difference = new DifferencePetriNet<>(mServices, mMinuend, mSubtrahend);
		new FinitePrefix<LETTER, PLACE>(mServices, difference);
		mResult = difference.getYetConstructedPetriNet();

	}



	@Override
	public String startMessage() {
		return "Start " + getOperationName() + "First Operand " + mMinuend.sizeInformation() + "Second Operand "
				+ mSubtrahend.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}



	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();
		statistics.addKeyValuePair(
				StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_PLACES , mResult.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_FLOW, mResult.flowSize());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_MINUEND_PLACES, mMinuend.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_MINUEND_TRANSITIONS, mMinuend.getTransitions().size());
		if (mMinuend instanceof BoundedPetriNet) {
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_MINUEND_FLOW, ((BoundedPetriNet<LETTER, PLACE>) mMinuend).flowSize());
		}
		if (mSubtrahend instanceof INestedWordAutomaton) {
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_STATES, ((INestedWordAutomaton<LETTER, PLACE>) mSubtrahend).getStates().size());
		}
		return statistics;
	}



	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IPetriNetAndAutomataInclusionStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		INestedWordAutomaton<LETTER, PLACE> subtrahend;
		if (mSubtrahend instanceof INestedWordAutomaton) {
			subtrahend = (INestedWordAutomaton<LETTER, PLACE>) mSubtrahend;
		} else {
			subtrahend = new RemoveDeadEnds(mServices, mSubtrahend).getResult();
		}
		return doResultCheck(mServices, mLogger, stateFactory, mMinuend, subtrahend, mResult);

	}

	static <LETTER, PLACE> boolean doResultCheck(
			final AutomataLibraryServices services, final ILogger logger,
			final IPetriNetAndAutomataInclusionStateFactory<PLACE> stateFactory,
			final IPetriNet<LETTER, PLACE> minuend, final INestedWordAutomaton<LETTER, PLACE> subtrahend,
			final BoundedPetriNet<LETTER, PLACE> result) throws AutomataLibraryException {
		final INestedWordAutomaton<LETTER, PLACE> minuendAsAutoaton = new PetriNet2FiniteAutomaton<>(services,
				stateFactory, minuend).getResult();
		final INestedWordAutomaton<LETTER, PLACE> differenceAutomata = new DifferenceDD<>(services, stateFactory,
				minuendAsAutoaton, subtrahend).getResult();
		final boolean isCorrect;

		final IsIncluded<LETTER, PLACE> subsetCheck = new IsIncluded<LETTER, PLACE>(services, stateFactory, result,
				differenceAutomata);
		if (!subsetCheck.getResult()) {
			final Word<LETTER> ctx = subsetCheck.getCounterexample();
			logger.error("Should not be accepted: " + ctx);
		}

		final IsIncluded<LETTER, PLACE> supersetCheck = new IsIncluded<LETTER, PLACE>(services, stateFactory,
				differenceAutomata, result);
		if (!supersetCheck.getResult()) {
			final Word<LETTER> ctx = supersetCheck.getCounterexample();
			logger.error("Should be accepted: " + ctx);
		}

		return subsetCheck.getResult() && supersetCheck.getResult();
	}

}
