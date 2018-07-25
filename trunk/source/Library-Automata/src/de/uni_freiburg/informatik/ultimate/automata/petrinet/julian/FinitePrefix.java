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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder.UnfoldingOrder;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * A finite prefix.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <STATE>
 *            place content type
 */
public final class FinitePrefix<LETTER, STATE> extends UnaryNetOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final IPetriNet<LETTER, STATE> mOperand;

	private final BranchingProcess<LETTER, STATE> mResult;

	private final PetriNetUnfolder<LETTER, STATE>.Statistics mUnfoldingStatistics;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public FinitePrefix(final AutomataLibraryServices services, final BoundedPetriNet<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		final PetriNetUnfolder<LETTER, STATE> unf =
				new PetriNetUnfolder<>(mServices, operand, UnfoldingOrder.ERV, false, false);
		mUnfoldingStatistics = unf.getUnfoldingStatistics();
		mResult = unf.getFinitePrefix();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Result " + mResult.sizeInformation();
	}

	@Override
	protected IPetriNet<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public BranchingProcess<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();

		final int numberConditions = new NumberOfConditions<>(mServices, getResult()).getResult();
		statistics.addKeyValuePair(StatisticsType.NUMBER_CONDITIONS, numberConditions);
		statistics.addKeyValuePair(StatisticsType.NUMBER_CO_RELATION_QUERIES, mUnfoldingStatistics.getCoRelationQueries());
		statistics.addKeyValuePair(StatisticsType.NUMBER_CUT_OFF_EVENTS, mUnfoldingStatistics.getCutOffEvents());
		statistics.addKeyValuePair(StatisticsType.NUMBER_NON_CUT_OFF_EVENTS, mUnfoldingStatistics.getNonCutOffEvents());

		return statistics;
	}



}
