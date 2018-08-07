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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceDD;
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


	private final BoundedPetriNet<LETTER, PLACE> mMinuend;
	private final INestedWordAutomaton<LETTER, PLACE> mSubtrahend;
	private final IBlackWhiteStateFactory<PLACE> mContentFactory;

	private final BoundedPetriNet<LETTER, PLACE> mResult;



	public <SF extends IBlackWhiteStateFactory<PLACE> & ISinkStateFactory<PLACE>> DifferencePairwiseOnDemand(
			final AutomataLibraryServices services, final SF factory,
			final BoundedPetriNet<LETTER, PLACE> minuendNet,
			final INestedWordAutomaton<LETTER, PLACE> subtrahendDfa) throws AutomataOperationCanceledException {
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
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_MINUEND_FLOW, mMinuend.flowSize());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_STATES, mSubtrahend.getStates().size());
		return statistics;
	}



	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

}
