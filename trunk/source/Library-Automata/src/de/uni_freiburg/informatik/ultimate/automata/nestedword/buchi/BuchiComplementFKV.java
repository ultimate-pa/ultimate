/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaOutgoingLetterAndTransitionAdapter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.NumberOfTransitions;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementFkvStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Buchi Complementation based on 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiComplementFKV<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	private final BuchiComplementFKVNwa<LETTER, STATE> mOnDemandComplement;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mComplemented;
	private final FkvOptimization mOptimization;


	/**
	 * Extended constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public <SF extends IDeterminizeStateFactory<STATE> & IBuchiComplementFkvStateFactory<STATE>> BuchiComplementFKV(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, FkvOptimization.HEIMAT2.toString(), Integer.MAX_VALUE);
	}

	/**
	 * Constructor which uses a {@link PowersetDeterminizer}.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @param optimization
	 *            optimization parameter
	 * @param userDefinedMaxRank
	 *            user-defined maximal rank
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public <SF extends IDeterminizeStateFactory<STATE> & IBuchiComplementFkvStateFactory<STATE>> BuchiComplementFKV(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final String optimization,
			final int userDefinedMaxRank) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, new PowersetDeterminizer<>(operand, true, stateFactory),
				FkvOptimization.valueOf(optimization), userDefinedMaxRank);
	}

	/**
	 * Constructor with a given {@link IStateDeterminizer}.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @param stateDeterminizer
	 *            state determinizer
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public BuchiComplementFKV(final AutomataLibraryServices services,
			final IBuchiComplementFkvStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, stateDeterminizer, FkvOptimization.HEIMAT2, Integer.MAX_VALUE);
	}

	/**
	 * Full constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @param optimization
	 *            optimization parameter
	 * @param userDefinedMaxRank
	 *            user-defined maximal rank
	 *            <p>
	 *            TODO Allow definition of a maximal rank for cases where you know that this is sound. E.g. if the
	 *            automaton is reverse deterministic a maximal rank of 2 is sufficient, see paper of Seth Forgaty.
	 * @param stateDeterminizer
	 *            state determinizer
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	private BuchiComplementFKV(final AutomataLibraryServices services,
			final IBuchiComplementFkvStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer, final FkvOptimization optimization,
			final int userDefinedMaxRank) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mOptimization = optimization;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mOnDemandComplement = new BuchiComplementFKVNwa<>(mServices, operand, stateDeterminizer, stateFactory, mOptimization,
				userDefinedMaxRank);
		mComplemented = new NwaOutgoingLetterAndTransitionAdapter<>(mOnDemandComplement);
		mResult = new NestedWordAutomatonReachableStates<>(mServices, mComplemented);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		final boolean underApproximationOfComplement = false;
		mLogger.info("Start testing correctness of " + getOperationName());
		final List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<>();
		final BuchiIsEmpty<LETTER, STATE> operandEmptiness = new BuchiIsEmpty<>(mServices, mOperand);
		final boolean operandEmpty = operandEmptiness.getResult();
		if (!operandEmpty) {
			lassoWords.add(operandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> resultEmptiness = new BuchiIsEmpty<>(mServices, mResult);
		final boolean resultEmpty = resultEmptiness.getResult();
		if (!resultEmpty) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		boolean correct = true;
		correct &= !(operandEmpty && resultEmpty);
		assert correct;
		/*
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mResult.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mResult.size()));
		*/
		for (int i = 0; i < 11; ++i) {
			lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, 1, i));
			lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, 2, i));
		}
		lassoWords.addAll((new LassoExtractor<>(mServices, mOperand)).getResult());
		lassoWords.addAll((new LassoExtractor<>(mServices, mResult)).getResult());

		for (final NestedLassoWord<LETTER> nlw : lassoWords) {
			boolean thistime = checkAcceptance(nlw, mOperand, underApproximationOfComplement);
			if (!thistime) {
				thistime = checkAcceptance(nlw, mOperand, underApproximationOfComplement);
			}
			correct &= thistime;
			assert correct;
		}

		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
					"language is different", mOperand, mResult);
		}
		mLogger.info("Finished testing correctness of " + getOperationName());
		return correct;
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + " with optimization " + mOptimization + ". Operand "
				+ mOperand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " with optimization " + mOptimization + ". Operand "
				+ mOperand.sizeInformation() + " Result " + mResult.sizeInformation()
				+ mOnDemandComplement.getPowersetStates() + " powerset states" + mOnDemandComplement.getRankStates()
				+ " rank states. The highest rank that occured is " + mOnDemandComplement.getHighesRank();
	}

	public int getHighestRank() {
		return mOnDemandComplement.getHighesRank();
	}

	@Override
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	private boolean checkAcceptance(final NestedLassoWord<LETTER> nlw,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final boolean underApproximationOfComplement)
			throws AutomataLibraryException {
		final boolean op = (new BuchiAccepts<>(mServices, operand, nlw)).getResult();
		final boolean res = (new BuchiAccepts<>(mServices, mResult, nlw)).getResult();
		boolean correct;
		if (underApproximationOfComplement) {
			correct = !res || op;
		} else {
			correct = op ^ res;
		}
		return correct;
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics result = new AutomataOperationStatistics();

		final int inputSize = getOperand().size();
		final int outputSize = getResult().size();

		result.addKeyValuePair(StatisticsType.STATES_INPUT, inputSize);
		result.addKeyValuePair(StatisticsType.STATES_OUTPUT, outputSize);

		final int outputTransitions = new NumberOfTransitions<>(mServices, getResult()).getResult();
		result.addKeyValuePair(StatisticsType.TRANSITIONS_OUTPUT, outputTransitions);

		return result;
	}
}
