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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author schaetzc@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in the alphabet of minuend Petri net, subtrahend
 *            DFA, and difference Petri net
 * @param <PLACE>
 *            Type of places in minuend and difference Petri net
 * @param <CRSF>
 *            Type of factory needed to check the result of this operation in
 *            {@link #checkResult(CRSF)}
 */
public final class DifferencePairwiseOnDemand<LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends GeneralOperation<LETTER, PLACE, CRSF> {

	private final IPetriNet<LETTER, PLACE> mMinuend;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> mSubtrahend;

	private final FinitePrefix<LETTER, PLACE> mFinitePrefixOfDifference;
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	private final DifferenceSynchronizationInformation<LETTER, PLACE> mDifferenceSynchronizationInformation;
	private DifferencePetriNet mDifference;

	public <SF extends IBlackWhiteStateFactory<PLACE> & ISinkStateFactory<PLACE>> DifferencePairwiseOnDemand(
			final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> minuendNet,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> subtrahendDfa,
			final Set<LETTER> userProvidedUniversalSubtrahendLoopers)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mMinuend = minuendNet;
		mSubtrahend = subtrahendDfa;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final Set<LETTER> universalSubtrahendLoopers;
		if (userProvidedUniversalSubtrahendLoopers != null) {
			universalSubtrahendLoopers = userProvidedUniversalSubtrahendLoopers;
			if (mLogger.isInfoEnabled()) {
				final int numberLoopers = universalSubtrahendLoopers.size();
				final int allLetters = mSubtrahend.getAlphabet().size();
				mLogger.info("Universal subtrahend loopers provided by user.");
				mLogger.info("Number of universal subtrahend loopers: " + numberLoopers + " of " + allLetters);
			}
		} else {
			if (mSubtrahend instanceof INestedWordAutomaton) {
				universalSubtrahendLoopers = determineUniversalLoopers(
						(INestedWordAutomaton<LETTER, PLACE>) mSubtrahend);
				if (mLogger.isInfoEnabled()) {
					final int numberLoopers = universalSubtrahendLoopers.size();
					final int allLetters = mSubtrahend.getAlphabet().size();
					mLogger.info("Number of universal subtrahend loopers: " + numberLoopers + " of " + allLetters);
				}
			} else {
				universalSubtrahendLoopers = null;
				mLogger.info(
						"Subtrahend is not yet constructed. Will not use universal subtrahend loopers optimization.");
			}
		}
		mDifference = new DifferencePetriNet<>(mServices, mMinuend, mSubtrahend, universalSubtrahendLoopers);
		mFinitePrefixOfDifference = new FinitePrefix<LETTER, PLACE>(mServices, mDifference);
		mResult = mDifference.getYetConstructedPetriNet();

		final Set<ITransition<LETTER, PLACE>> vitalTransitionsOfDifference = mFinitePrefixOfDifference.getResult()
				.computeVitalTransitions();
		mDifferenceSynchronizationInformation = mDifference
				.computeDifferenceSynchronizationInformation(vitalTransitionsOfDifference, true);
		final int allTransitions = mDifference.getYetConstructedPetriNet().getTransitions().size();
		final int deadTransitions = allTransitions - vitalTransitionsOfDifference.size();
		{
			final int looperLetters = mMinuend.getAlphabet().size()
					- mDifferenceSynchronizationInformation.getChangerLetters().size();
			mLogger.info(looperLetters + "/" + mMinuend.getAlphabet().size() + " looper letters, "
					+ mDifferenceSynchronizationInformation.getSelfloops().size() + " selfloop transitions, "
					+ mDifferenceSynchronizationInformation.getStateChangers().size() + " changer transitions "
					+ deadTransitions + "/" + allTransitions + " dead transitions.");
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	public <SF extends IBlackWhiteStateFactory<PLACE> & ISinkStateFactory<PLACE>> DifferencePairwiseOnDemand(
			final AutomataLibraryServices services, final SF factory, final IPetriNet<LETTER, PLACE> minuendNet,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> subtrahendDfa)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, minuendNet, subtrahendDfa, null);
	}

	public Map<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> getTransitionBacktranslation() {
		return mDifference.getTransitionBacktranslation();
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". First operand " + mMinuend.sizeInformation() + ". Second operand "
				+ mSubtrahend.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();
		statistics.addAllStatistics(mFinitePrefixOfDifference.getAutomataOperationStatistics());
		statistics.addKeyValuePair(StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_PLACES, mResult.getPlaces().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_FLOW, mResult.flowSize());
		statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_PLACES, mMinuend.getPlaces().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_TRANSITIONS,
				mMinuend.getTransitions().size());
		if (mMinuend instanceof BoundedPetriNet) {
			statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_FLOW,
					((BoundedPetriNet<LETTER, PLACE>) mMinuend).flowSize());
		}
		if (mSubtrahend instanceof INestedWordAutomaton) {
			statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_STATES,
					((INestedWordAutomaton<LETTER, PLACE>) mSubtrahend).getStates().size());
		}
		return statistics;
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	public FinitePrefix<LETTER, PLACE> getFinitePrefixOfDifference() {
		return mFinitePrefixOfDifference;
	}

	public DifferenceSynchronizationInformation<LETTER, PLACE> getDifferenceSynchronizationInformation() {
		return mDifferenceSynchronizationInformation;
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of " + getOperationName());
		}
		INestedWordAutomaton<LETTER, PLACE> subtrahend;
		if (mSubtrahend instanceof INestedWordAutomaton) {
			subtrahend = (INestedWordAutomaton<LETTER, PLACE>) mSubtrahend;
		} else {
			subtrahend = new RemoveDeadEnds<LETTER, PLACE>(mServices, mSubtrahend).getResult();
		}

		if (!(mMinuend instanceof BoundedPetriNet)) {
			throw new UnsupportedOperationException("Convert minuend to fully constructed net");
		}
		final BoundedPetriNet<LETTER, PLACE> minuend = (BoundedPetriNet<LETTER, PLACE>) mMinuend;
		final boolean correct = PetriNetUtils.doDifferenceLanguageCheck(mServices, stateFactory, minuend, subtrahend,
				mResult);

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;

	}

	public static <LETTER, STATE> Set<LETTER> determineUniversalLoopers(final INestedWordAutomaton<LETTER, STATE> nwa) {
		if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
			throw new UnsupportedOperationException("call and return not implemented yet");
		}
		final Set<LETTER> result = new HashSet<>();
		for (final LETTER letter : nwa.getAlphabet()) {
			final boolean isUniversalLooper = isUniversalLooper(letter, nwa);
			if (isUniversalLooper) {
				result.add(letter);
			}
		}
		return result;
	}

	private static <LETTER, STATE> boolean isUniversalLooper(final LETTER letter,
			final INestedWordAutomaton<LETTER, STATE> nwa) {
		for (final STATE state : nwa.getStates()) {
			final boolean hasSelfloop = hasSelfloop(letter, state, nwa);
			if (!hasSelfloop) {
				return false;
			}
		}
		return true;
	}

	private static <LETTER, STATE> boolean hasSelfloop(final LETTER letter, final STATE state,
			final INestedWordAutomaton<LETTER, STATE> nwa) {
		final Iterator<OutgoingInternalTransition<LETTER, STATE>> it = nwa.internalSuccessors(state, letter).iterator();
		if (!it.hasNext()) {
			return false;
		} else {
			final OutgoingInternalTransition<LETTER, STATE> succTrans = it.next();
			final boolean hasSelfloop = (succTrans.getSucc().equals(state));
			if (it.hasNext()) {
				throw new IllegalArgumentException("automaton is nondeterministic");
			}
			return hasSelfloop;
		}
	}

}
