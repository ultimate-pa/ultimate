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
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * A finite prefix.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <STATE>
 *            place content type
 */
public final class FinitePrefix<LETTER, STATE>
		extends UnaryNetOperation<LETTER, STATE, IPetriNet2FiniteAutomatonStateFactory<STATE>> {
	private final IPetriNetSuccessorProvider<LETTER, STATE> mOperand;

	private final BranchingProcess<LETTER, STATE> mResult;

	private final PetriNetUnfolder<LETTER, STATE>.Statistics mUnfoldingStatistics;

	private final PetriNetRun<LETTER, STATE> mAcceptingRun;
	private final PetriNetUnfolder<LETTER, STATE> mUnf;

	public FinitePrefix(final AutomataLibraryServices services, final IPetriNetSuccessorProvider<LETTER, STATE> operand)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, operand, false);
	}

	public FinitePrefix(final AutomataLibraryServices services, final IPetriNetSuccessorProvider<LETTER, STATE> operand,
			final boolean sameTransitionCutOff) throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		final PetriNetUnfolder<LETTER, STATE> unf =
				new PetriNetUnfolder<>(mServices, operand, EventOrderEnum.ERV, sameTransitionCutOff, false);
		mUnf = unf;
		mAcceptingRun = unf.getAcceptingRun();
		mUnfoldingStatistics = unf.getUnfoldingStatistics();
		mResult = unf.getFinitePrefix();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Finished " + getOperationName());
		sb.append(" ");
		sb.append("Result " + mResult.sizeInformation() + ".");
		sb.append(" ");
		sb.append(mUnfoldingStatistics.prettyprintCutOffInformation());
		sb.append(" ");
		sb.append(mUnfoldingStatistics.prettyprintCoRelationInformation());
		sb.append(" ");
		sb.append(mUnfoldingStatistics.prettyprintPossibleExtensionsMaximalSize());
		sb.append(" ");
		sb.append(mUnfoldingStatistics.prettyprintNumberOfEventComparisons());
		sb.append(" ");
		sb.append(mUnfoldingStatistics.prettyprintPossibleExtensionCandidatesInformation());
		sb.append(" ");
		sb.append(mUnfoldingStatistics.prettyprintCoRelationMaximalDegree());
		sb.append(" ");
		sb.append(mUnfoldingStatistics.prettyprintConditionPerPlaceMax());
		sb.append(" ");
		return sb.toString();
	}

	@Override
	protected IPetriNetSuccessorProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public BranchingProcess<LETTER, STATE> getResult() {
		return mResult;
	}

	public PetriNetRun<LETTER, STATE> getAcceptingRun() {
		return mAcceptingRun;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return mUnf.checkResult(stateFactory);
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();

		final int numberConditions = new NumberOfConditions<>(mServices, getResult()).getResult();
		statistics.addKeyValuePair(StatisticsType.NUMBER_CONDITIONS, numberConditions);
		statistics.addKeyValuePair(StatisticsType.NUMBER_CO_RELATION_QUERIES_YES,
				mUnfoldingStatistics.getCoRelationQueriesYes());
		statistics.addKeyValuePair(StatisticsType.NUMBER_CO_RELATION_QUERIES_NO,
				mUnfoldingStatistics.getCoRelationQueriesNo());
		statistics.addKeyValuePair(StatisticsType.NUMBER_CUT_OFF_EVENTS, mUnfoldingStatistics.getCutOffEvents());
		statistics.addKeyValuePair(StatisticsType.NUMBER_NON_CUT_OFF_EVENTS, mUnfoldingStatistics.getNonCutOffEvents());
		statistics.addKeyValuePair(StatisticsType.NUMBER_EVENT_COMPARISONS,
				mUnfoldingStatistics.getNumberOfConfigurationComparisons());
		statistics.addKeyValuePair(StatisticsType.FOATA_NORMAL_FORM_COMPARISONS,
				mUnfoldingStatistics.getNumberOfFoataBasedConfigurationComparisons());
		if (mOperand instanceof IPetriNet) {
			statistics.addKeyValuePair(StatisticsType.NUMBER_UNREACHABLE_TRANSITIONS,
					mUnfoldingStatistics.unreachableTransitionsInOperand());
		}
		statistics.addKeyValuePair(StatisticsType.POSSIBLE_EXTENSIONS_SIZE_MAX,
				mUnfoldingStatistics.getMaximalSizeOfPossibleExtensions());
		statistics.addKeyValuePair(StatisticsType.EXTENSION_CANDIDATES_TOTAL,
				mUnfoldingStatistics.getNumberOfExtensionCandidates());
		statistics.addKeyValuePair(StatisticsType.EXTENSION_CANDIDATES_USELESS,
				mUnfoldingStatistics.getNumberOfUselessExtensionCandidates());

		statistics.addKeyValuePair(StatisticsType.CO_RELATION_MAX_DEGREE,
				mUnfoldingStatistics.computeCoRelationMaximalDegree());

		statistics.addKeyValuePair(StatisticsType.CONDITION_PER_PLACE_MAX,
				mUnfoldingStatistics.computeConditionPerPlaceMax());
		return statistics;
	}

}
