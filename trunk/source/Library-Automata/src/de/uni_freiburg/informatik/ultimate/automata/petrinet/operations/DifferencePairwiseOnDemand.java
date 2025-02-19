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

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

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
public final class DifferencePairwiseOnDemand<LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends GeneralOperation<LETTER, PLACE, CRSF> {

	/**
	 * If set, we add the statistics of the finite prefix to the statistics of this operation. This is helpful for
	 * debugging and analyzing the results. The statistics of the finite prefix are however computed on demand and this
	 * computation comes with minor costs. <br>
	 * If we want to evaluate the speed of this algorithm the generation of statistics can be switched off. The automata
	 * script interpreter calls the following method, which triggers the computation of the finite prefix's statistics.
	 * Applications, like our software verification, typically do not call this method.
	 * {@link DifferencePairwiseOnDemand#getAutomataOperationStatistics()} Hence, an evaluation without the finite
	 * prefix's statistics gives a better impression about the performance in practice. See
	 * https://github.com/ultimate-pa/ultimate/issues/448#issuecomment-603025477 and
	 * https://github.com/ultimate-pa/ultimate/issues/448#issuecomment-608669868
	 */
	private static final boolean ADD_FINITE_PREFIX_STATISTICS = true;
	private final IPetriNetSuccessorProvider<LETTER, PLACE> mMinuend;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> mSubtrahend;

	private final FinitePrefix<LETTER, PLACE> mFinitePrefixOfDifference;
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	private final DifferenceSynchronizationInformation<LETTER, PLACE> mDifferenceSynchronizationInformation;
	private Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> mTransitionBacktranslation;

	public DifferencePairwiseOnDemand(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> minuendNet,
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
		} else if (mSubtrahend instanceof INestedWordAutomaton) {
			universalSubtrahendLoopers = determineUniversalLoopers((INestedWordAutomaton<LETTER, PLACE>) mSubtrahend);
			if (mLogger.isInfoEnabled()) {
				final int numberLoopers = universalSubtrahendLoopers.size();
				final int allLetters = mSubtrahend.getAlphabet().size();
				mLogger.info("Number of universal subtrahend loopers: " + numberLoopers + " of " + allLetters);
			}
		} else {
			universalSubtrahendLoopers = null;
			mLogger.info("Subtrahend is not yet constructed. Will not use universal subtrahend loopers optimization.");
		}
		final DifferencePetriNet<LETTER, PLACE> difference =
				new DifferencePetriNet<>(mServices, mMinuend, mSubtrahend, universalSubtrahendLoopers);
		mFinitePrefixOfDifference = new FinitePrefix<>(mServices, difference);
		mResult = difference.getYetConstructedPetriNet();
		mTransitionBacktranslation = difference.getTransitionBacktranslation();

		final Set<Transition<LETTER, PLACE>> vitalTransitionsOfDifference =
				mFinitePrefixOfDifference.getResult().computeVitalTransitions();
		mDifferenceSynchronizationInformation =
				difference.computeDifferenceSynchronizationInformation(vitalTransitionsOfDifference, true);
		final int allTransitions = difference.getYetConstructedPetriNet().getTransitions().size();
		final int deadTransitions = allTransitions - vitalTransitionsOfDifference.size();
		final int looperLetters =
				mMinuend.getAlphabet().size() - mDifferenceSynchronizationInformation.getChangerLetters().size();
		mLogger.info(looperLetters + "/" + mMinuend.getAlphabet().size() + " looper letters, "
				+ mDifferenceSynchronizationInformation.getSelfloops().size() + " selfloop transitions, "
				+ mDifferenceSynchronizationInformation.getStateChangers().size() + " changer transitions "
				+ deadTransitions + "/" + allTransitions + " dead transitions.");
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	public DifferencePairwiseOnDemand(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> minuendNet,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> subtrahendDfa)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, minuendNet, subtrahendDfa, null);
	}

	public Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> getTransitionBacktranslation() {
		return mTransitionBacktranslation;
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
		if (ADD_FINITE_PREFIX_STATISTICS) {
			statistics.addAllStatistics(mFinitePrefixOfDifference.getAutomataOperationStatistics());
		}
		statistics.addKeyValuePair(StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_PLACES, mResult.getPlaces().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_FLOW, mResult.flowSize());
		if (mMinuend instanceof IPetriNet) {
			final IPetriNet<LETTER, PLACE> minuendPetriNet = (IPetriNet<LETTER, PLACE>) mMinuend;
			statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_PLACES,
					minuendPetriNet.getPlaces().size());
			statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_TRANSITIONS,
					minuendPetriNet.getTransitions().size());
			statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_FLOW, minuendPetriNet.flowSize());
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
			subtrahend = new RemoveDeadEnds<>(mServices, mSubtrahend).getResult();
		}

		if (!(mMinuend instanceof IPetriNetTransitionProvider)) {
			throw new UnsupportedOperationException("Convert minuend to fully constructed net");
		}
		final boolean correct = PetriNetUtils.doDifferenceLanguageCheck(mServices, stateFactory,
				(IPetriNetTransitionProvider<LETTER, PLACE>) mMinuend, subtrahend, mResult);

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;

	}

	private static <LETTER, STATE> Set<LETTER>
			determineUniversalLoopers(final INestedWordAutomaton<LETTER, STATE> nwa) {
		if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
			throw new UnsupportedOperationException("call and return not implemented yet");
		}
		return nwa.getAlphabet().stream().filter(letter -> isUniversalLooper(letter, nwa)).collect(Collectors.toSet());
	}

	private static <LETTER, STATE> boolean isUniversalLooper(final LETTER letter,
			final INestedWordAutomaton<LETTER, STATE> nwa) {
		return nwa.getStates().stream().allMatch(state -> hasSelfloop(letter, state, nwa));
	}

	private static <LETTER, STATE> boolean hasSelfloop(final LETTER letter, final STATE state,
			final INestedWordAutomaton<LETTER, STATE> nwa) {
		final Iterator<OutgoingInternalTransition<LETTER, STATE>> it = nwa.internalSuccessors(state, letter).iterator();
		if (!it.hasNext()) {
			return false;
		}
		final OutgoingInternalTransition<LETTER, STATE> succTrans = it.next();
		if (it.hasNext()) {
			throw new IllegalArgumentException("automaton is nondeterministic");
		}
		return succTrans.getSucc().equals(state);
	}

}
