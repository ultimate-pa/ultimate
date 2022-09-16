/*
 * Copyright (C) 2020 heizmann@informatik.uni-freiburg.de
 * Copyright (C) 2020 University of Freiburg
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

import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in alphabet of Petri net
 * @param <PLACE>
 *            Type of places in Petri net
 * @param <CRSF>
 *            Type of factory needed to check the result of this operation in {@link #checkResult(CRSF)}
 */
public class RemoveRedundantFlow<LETTER, PLACE, CRSF extends IStateFactory<PLACE> & IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends UnaryNetOperation<LETTER, PLACE, CRSF> {

	private static final boolean DEBUG_LOG_RESTRICTOR_INFORMATION = false;
	/**
	 * Idea: If true we only check if (p,p') is a restrictor-redundancy pair if the restrictor candidate p does not have
	 * more conditions than the redundancy candidate p'
	 */
	private static final boolean MOUNTAIN_COCK_HEURISTIC = false;
	private final IPetriNet<LETTER, PLACE> mOperand;
	private final FinitePrefix<LETTER, PLACE> mFinitePrefixOperation;
	private final BranchingProcess<LETTER, PLACE> mFinPre;
	private final HashRelation<Transition<LETTER, PLACE>, PLACE> mRedundantSelfloopFlow = new HashRelation<>();
	private final BoundedPetriNet<LETTER, PLACE> mResult;
	private final Set<PLACE> mRedundantPlaces;
	private final Set<PLACE> mEligibleRedundancyCandidates;
	private final Set<PLACE> mEligibleRestrictorCandidates;
	private int mRestrictorConditionChecks = 0;
	private final NestedMap2<PLACE, PLACE, Boolean> mRestrictorPlaceCache = new NestedMap2<>();
	private final Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> mInput2projected;

	public RemoveRedundantFlow(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, operand, null, null, null);
	}

	public RemoveRedundantFlow(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand,
			final BranchingProcess<LETTER, PLACE> finPre, final Set<PLACE> eligibleRedundancyCandidates,
			final Set<PLACE> eligibleRestrictorCandidates)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mEligibleRedundancyCandidates = eligibleRedundancyCandidates;
		mEligibleRestrictorCandidates = eligibleRestrictorCandidates;
		printStartMessage();
		if (finPre != null) {
			mFinitePrefixOperation = null;
			mFinPre = finPre;
		} else {
			mFinitePrefixOperation = new FinitePrefix<>(services, operand);
			mFinPre = mFinitePrefixOperation.getResult();
		}
		final HashRelation<Transition<LETTER, PLACE>, PLACE> redundantFlow = new HashRelation<>();
		for (final Transition<LETTER, PLACE> t : operand.getTransitions()) {
			for (final PLACE p : t.getPredecessors()) {
				if (isEligibleRedundancyCandidate(p)) {
					final boolean isFlowRedundant = isFlowRedundant(t, p, redundantFlow);
					if (isFlowRedundant) {
						redundantFlow.addPair(t, p);
						if (t.getSuccessors().contains(p)) {
							mRedundantSelfloopFlow.addPair(t, p);
						}
					}
				}
			}
		}
		mRedundantPlaces = operand.getPlaces().stream().filter(x -> isRedundantPlace(x, operand, redundantFlow))
				.collect(Collectors.toSet());
		final ProjectToSubnet<LETTER, PLACE> pts =
				new ProjectToSubnet<>(services, operand, mRedundantSelfloopFlow, mRedundantPlaces);
		mInput2projected = pts.getTransitionMapping();
		mResult = pts.getResult();
		printExitMessage();
	}

	private boolean isEligibleRedundancyCandidate(final PLACE p) {
		return mEligibleRedundancyCandidates == null || mEligibleRedundancyCandidates.contains(p);
	}

	private boolean isEligibleRestrictorCandidate(final PLACE p) {
		return mEligibleRestrictorCandidates == null || mEligibleRestrictorCandidates.contains(p);
	}

	private boolean isRedundantPlace(final PLACE p, final IPetriNet<LETTER, PLACE> operand,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> redundantFlow) {
		if (operand.isAccepting(p)) {
			return false;
		}
		final Set<Transition<LETTER, PLACE>> succTrans = operand.getSuccessors(p);
		if (succTrans.isEmpty()) {
			// TODO 20200225 Matthias: At the moment places without successor
			// transitions are not considered redundant. Otherwise we would
			// produce transitions without successor which are not yet supported
			// by the unfolding.
			return false;
		}
		for (final Transition<LETTER, PLACE> t : succTrans) {
			if (!redundantFlow.containsPair(t, p)) {
				return false;
			}
		}
		return true;
	}

	private boolean isFlowRedundant(final Transition<LETTER, PLACE> t, final PLACE redundancyCandidate,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> redundantFlow)
			throws AutomataOperationCanceledException {
		for (final PLACE p : t.getPredecessors()) {
			if (isEligibleRestrictorCandidate(p) && !p.equals(redundancyCandidate) && (!MOUNTAIN_COCK_HEURISTIC
					|| mFinPre.getConditions(p).size() <= mFinPre.getConditions(redundancyCandidate).size())) {
				if (redundantFlow.containsPair(t, p)) {
					// do nothing
					// must not use flow that is already marked for removal
				} else {
					if (!mServices.getProgressAwareTimer().continueProcessing()) {
						throw new AutomataOperationCanceledException(getClass());
					}
					final boolean isRestrictorPlace = isRestrictorPlace(redundancyCandidate, p);
					if (isRestrictorPlace) {
						if (DEBUG_LOG_RESTRICTOR_INFORMATION) {
							final int restrictorConditions = mFinPre.getConditions(p).size();
							final int redundancyConditions = mFinPre.getConditions(redundancyCandidate).size();
							mLogger.info("RestrictorPredecessor:" + restrictorConditions + " RendundantPredecessor:"
									+ redundancyConditions + "  " + p + " " + redundancyCandidate);
						}
						return true;
					}
				}
			}
		}
		return false;
	}

	private boolean isRestrictorPlace(final PLACE redundancyCandidate, final PLACE restrictorCandidate) {
		Boolean isRestrictor = mRestrictorPlaceCache.get(redundancyCandidate, restrictorCandidate);
		if (isRestrictor == null) {
			isRestrictor = checkRestrictorPlace(redundancyCandidate, restrictorCandidate);
			mRestrictorPlaceCache.put(redundancyCandidate, restrictorCandidate, isRestrictor);
		}
		return isRestrictor;
	}

	private boolean checkRestrictorPlace(final PLACE redundancyCandidate, final PLACE restrictorCandidate) {
		for (final Condition<LETTER, PLACE> restrictorCandidateCondition : mFinPre.place2cond(restrictorCandidate)) {
			if (restrictorCandidateCondition.getPredecessorEvent().isCutoffEvent()) {
				// we may omit the check because if the the candidate is not a
				// restrictor condition there is also another condition of the
				// same place that is not a restrictor condition and not
				// successor of a cut-off event.
			} else {
				final boolean isRestrictorCondition = isRestrictorCondition(restrictorCandidateCondition,
						redundancyCandidate, mFinPre.getCoRelation());
				if (!isRestrictorCondition) {
					return false;
				}
			}
		}
		return true;
	}

	private boolean isRestrictorCondition(final Condition<LETTER, PLACE> restrictorCandidateCondition,
			final PLACE redundancyCandidate, final ICoRelation<LETTER, PLACE> coRelation) {
		mRestrictorConditionChecks++;
		final Optional<Condition<LETTER, PLACE>> redundancyCandidateCondition =
				restrictorCandidateCondition.getPredecessorEvent().getConditionMark().stream()
						.filter(x -> x.getPlace().equals(redundancyCandidate)).findAny();
		if (!redundancyCandidateCondition.isPresent()) {
			return false;
		}
		final boolean isRestrictorCondition = redundancyCandidateCondition.get().getSuccessorEvents().stream()
				.allMatch(x -> !coRelation.isInCoRelation(restrictorCandidateCondition, x));
		return isRestrictorCondition;
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	protected IPetriNet<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	public HashRelation<Transition<LETTER, PLACE>, PLACE> getRedundantSelfloopFlow() {
		return mRedundantSelfloopFlow;
	}

	public Set<PLACE> getRedundantPlaces() {
		return mRedundantPlaces;
	}

	public Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> getOld2projected() {
		return mInput2projected;
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of " + getOperationName());
		}
		final boolean correct = PetriNetUtils.isEquivalent(mServices, stateFactory, mOperand, mResult);
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ", result has " + mResult.sizeInformation() + ", removed "
				+ mRedundantSelfloopFlow.size() + " selfloop flow, removed " + mRedundantPlaces.size()
				+ " redundant places.";
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();

		if (mFinitePrefixOperation != null) {
			statistics.addAllStatistics(mFinitePrefixOperation.getAutomataOperationStatistics());
		}
		statistics.addKeyValuePair(StatisticsType.PETRI_REMOVED_PLACES,
				mOperand.getPlaces().size() - mResult.getPlaces().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_REMOVED_TRANSITIONS,
				mOperand.getTransitions().size() - mResult.getTransitions().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_REMOVED_FLOW, mOperand.flowSize() - mResult.flowSize());
		statistics.addKeyValuePair(StatisticsType.RESTRICTOR_CONDITION_CHECKS, mRestrictorConditionChecks);

		statistics.addKeyValuePair(StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_PLACES, mResult.getPlaces().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_FLOW, mResult.flowSize());

		return statistics;
	}

}
