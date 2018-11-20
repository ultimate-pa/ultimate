/*
 * Copyright (C) 2018 schaetzc@tf.uni-freiburg.de
 * Copyright (C) 2009-2018 University of Freiburg
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

import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;

/**
 * Removes unreachable nodes of a Petri Net preserving its behavior.
 * Nodes are either transitions or places.
 * <p>
 * A transition is unreachable iff it can never fire
 * (because there is no reachable marking covering all of its preceding places).
 * <p>
 * A place is unreachable iff it is not covered by any reachable marking.
 * <p>
 * This operation may also remove some of the reachable places if they are not needed.
 * Required are only
 * <ul>
 *   <li> places with a reachable successor transition,
 *   <li> or accepting-places with a reachable predecessor transition,
 *   <li> or at most one accepting initial place without a reachable successor transition.
 * </ul>
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in alphabet of Petri net
 * @param <PLACE>
 *            Type of places in Petri net
 * @param <CRSF>
 *            Type of factory needed to check the result of this operation in {@link #checkResult(CRSF)}
 */
public class RemoveUnreachable<LETTER, PLACE, CRSF extends
		IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends UnaryNetOperation<LETTER, PLACE, CRSF> {

	private final BoundedPetriNet<LETTER, PLACE> mOperand;

	/** {@link #mOperand} with only reachable transitions and required places. */
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	private final Set<ITransition<LETTER, PLACE>> mReachableTransitions;

	public RemoveUnreachable(final AutomataLibraryServices services, final BoundedPetriNet<LETTER, PLACE> operand)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, operand, null);
	}

	/**
	 * Copies the reachable parts of a net.
	 *
	 * @param operand
	 *     Petri net to be copied such that only reachable nodes remain.
	 * @param reachableTransitions
	 *     The reachable transitions (or a superset) of {@code operand}.
	 *     Can be computed from an existing finite prefix using {@link #reachableTransitions(BranchingProcess)}
	 *     or automatically when using {@link #RemoveUnreachable(AutomataLibraryServices, BoundedPetriNet)}.
	 *
	 * @throws AutomataOperationCanceledException The operation was canceled
	 * @throws PetriNetNot1SafeException
	 */
	public RemoveUnreachable(final AutomataLibraryServices services, final BoundedPetriNet<LETTER, PLACE> operand,
			final Set<ITransition<LETTER, PLACE>> reachableTransitions)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mReachableTransitions = reachableTransitions == null ? reachableTransitions() : reachableTransitions;
		mResult = new CopySubnet<>(services, mOperand, mReachableTransitions).getResult();
	}

	private Set<ITransition<LETTER, PLACE>> reachableTransitions()
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		try {
			final BranchingProcess<LETTER, PLACE> finPre = new FinitePrefix<>(mServices, mOperand).getResult();
			return reachableTransitions(finPre);
		} catch (final AutomataOperationCanceledException aoce) {
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(), "anayzing net that has "
					+ mOperand.getPlaces().size() + " and " + mOperand.getTransitions().size() + " transistions.");
			aoce.addRunningTaskInfo(rti);
			throw aoce;
		}
	}

	/**
	 * From a complete finite prefix compute the reachable transitions of the original Petri net.
	 * A transition t is reachable iff there is a reachable marking enabling t.
	 * @param finPre complete finite Prefix of a Petri net N
	 * @return reachable transitions in N
	 */
	public static <LETTER, PLACE> Set<ITransition<LETTER, PLACE>> reachableTransitions(
			final BranchingProcess<LETTER, PLACE> finPre) {
		return finPre.getEvents().stream().map(Event::getTransition)
				// finPre contains dummy root-event which does not correspond to any transition
				.filter(Objects::nonNull)
				.collect(Collectors.toSet());
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	protected IPetriNet<LETTER, PLACE> getOperand() {
		return mOperand;
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
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();

		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_PLACES , mOperand.getPlaces().size() - mResult.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_TRANSITIONS, mOperand.getTransitions().size() - mResult.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_FLOW, mOperand.flowSize() - mResult.flowSize());

		statistics.addKeyValuePair(
				StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_PLACES , mResult.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_FLOW, mResult.flowSize());

		return statistics;
	}

}



