/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeNwaDd;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.LookaheadPartitionConstructor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMaxSat2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionAndMapBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * TODO: documentation
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class ReduceNwaFullMultipebbleSimulation<LETTER, STATE, GS extends FullMultipebbleGameState<STATE>>
		extends AbstractMinimizeNwaDd<LETTER, STATE> {
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final AutomataOperationStatistics mStatistics;
	
	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @param simulationInfoProvider
	 *            simulation info provider
	 * @throws AutomataOperationCanceledException
	 *             if suboperations fail
	 */
	public ReduceNwaFullMultipebbleSimulation(final AutomataLibraryServices services, final IMergeStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mOperand = operand;
	
		printStartMessage();
		
		final PartitionBackedSetOfPairs<STATE> partition = new PartitionAndMapBackedSetOfPairs<STATE>(
				new LookaheadPartitionConstructor<>(mServices, mOperand, true).getPartition().getRelation());
		mLogger.info("Initial partition has " + partition.getOrConstructPartitionSizeInformation().toString());
		final FullMultipebbleStateFactory<STATE, GS> gameFactory = constructGameFactory(partition);
		
		try {
			final FullMultipebbleGameAutomaton<LETTER, STATE, GS> gameAutomaton =
					new FullMultipebbleGameAutomaton<>(mServices, gameFactory, partition, operand);
			final Pair<IDoubleDeckerAutomaton<LETTER, GS>, Integer> simRes = computeSimulation(gameAutomaton);
			final int maxGameAutomatonSize = simRes.getSecond();
			final NestedMap2<STATE, STATE, GS> gsm = gameAutomaton.getGameStateMapping();
			
			final ReadoutSimulation rs = new ReadoutSimulation(gsm, simRes.getFirst(), gameFactory);
			rs.process(partition.getRelation());
			final UnionFind<STATE> equivalenceRelation = rs.getMutuallySimulating();
			final boolean mergeFinalAndNonFinalStates = !false;
			// TODO make this an option?
			final boolean addMapOldState2NewState = false;
			final MinimizeNwaPmaxSat<LETTER, STATE> maxSatMinimizer =
					new MinimizeNwaPmaxSat<>(mServices, stateFactory, mOperand,
							new PartitionBackedSetOfPairs<>(equivalenceRelation.getAllEquivalenceClasses()),
							new MinimizeNwaMaxSat2.Settings<STATE>()
									.setFinalStateConstraints(!mergeFinalAndNonFinalStates)
									.setAddMapOldState2NewState(addMapOldState2NewState));
			super.directResultConstruction(maxSatMinimizer.getResult());
			if (addMapOldState2NewState) {
				super.setOld2NewStateMap(maxSatMinimizer.getOldState2newState());
			}
			
			mStatistics = super.getAutomataOperationStatistics();
			mStatistics.addKeyValuePair(StatisticsType.MAX_NUMBER_OF_DOUBLEDECKER_PEBBLES, gameFactory.getMaxNumberOfDoubleDeckerPebbles());
			mStatistics.addKeyValuePair(StatisticsType.SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS,
					partition.getOrConstructPartitionSizeInformation().getSizeOfLargestBlock());
			mStatistics.addKeyValuePair(StatisticsType.NUMBER_PAIRS_INITIAL_EQUIVALENCE_CLASS,
					partition.getOrConstructPartitionSizeInformation().getNumberOfPairs());
			mStatistics.addKeyValuePair(StatisticsType.SIZE_GAME_AUTOMATON,
					maxGameAutomatonSize);
			mStatistics.addKeyValuePair(StatisticsType.STATES_INPUT, mOperand.size());
			mStatistics.addKeyValuePair(StatisticsType.STATES_OUTPUT, getResult().size());
			
		} catch (final AutomataOperationCanceledException aoce) {
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
					NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(operationName(), mOperand,
							partition.getOrConstructPartitionSizeInformation()));
			aoce.addRunningTaskInfo(rti);
			throw aoce;
		}
		printExitMessage();
	}

	protected abstract Pair<IDoubleDeckerAutomaton<LETTER, GS>,Integer> computeSimulation(FullMultipebbleGameAutomaton<LETTER, STATE, GS> gameAutomaton) throws AutomataOperationCanceledException;

	protected abstract FullMultipebbleStateFactory<STATE, GS> constructGameFactory(final ISetOfPairs<STATE, ?> initialPartition);
	
	private class ReadoutSimulation extends InitialPartitionProcessor<STATE> {
		private final NestedMap2<STATE, STATE, GS> mGameStateMapping;
		private final IDoubleDeckerAutomaton<LETTER, GS> mRemoved;
		private final UnionFind<STATE> mMutuallySimulating;
		private final FullMultipebbleStateFactory<STATE,?> mGameFactory;

		public ReadoutSimulation(final NestedMap2<STATE, STATE, GS> gsm,
				final IDoubleDeckerAutomaton<LETTER, GS> removed, final FullMultipebbleStateFactory<STATE, ?> gameFactory) {
			super(mServices);
			mGameStateMapping = gsm;
			mRemoved = removed;
			mGameFactory = gameFactory;
			mMutuallySimulating = new UnionFind<>();
		}

		@Override
		public boolean shouldBeProcessed(final STATE q0, final STATE q1) {
			if (mGameFactory.isImmediatelyWinningForSpoiler(q0, q1, mOperand) ||
					mGameFactory.isImmediatelyWinningForSpoiler(q1, q0, mOperand)) {
				return false;
			}
			final GS s1 = mGameStateMapping.get(q0, q1);
			if (mRemoved.isInitial(s1)) {
				return false;
			}
			final GS s2 = mGameStateMapping.get(q1, q0);
			if (mRemoved.isInitial(s2)) {
				return false;
			}
			return true;
		}

		@Override
		public void doProcess(final STATE q0, final STATE q1) {
			final STATE rep0 = mMutuallySimulating.findAndConstructEquivalenceClassIfNeeded(q0);
			final STATE rep1 = mMutuallySimulating.findAndConstructEquivalenceClassIfNeeded(q1);
			mMutuallySimulating.union(rep0, rep1);
		}

		public UnionFind<STATE> getMutuallySimulating() {
			return mMutuallySimulating;
		}
	}

	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		return mStatistics;
	}
}
