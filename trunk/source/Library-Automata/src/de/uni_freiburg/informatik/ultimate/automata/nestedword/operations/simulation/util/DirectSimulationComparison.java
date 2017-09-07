/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDirectBi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.ReduceNwaDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.ReduceNwaDirectSimulationB;

/**
 * Checks that the direct simulation result for finite automata is unique for all supporting minimization operations.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class DirectSimulationComparison<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE, IMinimizationCheckResultStateFactory<STATE>> {
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final ReduceNwaDirectSimulation<LETTER, STATE> mOldSimulation;
	private final ReduceNwaDirectSimulationB<LETTER, STATE> mNewSimulation;
	private final MinimizeNwaPmaxSat<LETTER, STATE> mMaxSat;

	/**
	 * Constructor.
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
	public DirectSimulationComparison(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		final IDoubleDeckerAutomaton<LETTER, STATE> dd = new RemoveDeadEnds<>(mServices, mOperand).getResult();
		mOldSimulation = new ReduceNwaDirectSimulation<>(mServices, stateFactory, dd);
		mNewSimulation = new ReduceNwaDirectSimulationB<>(mServices, stateFactory, dd);
		mMaxSat = new MinimizeNwaPmaxSatDirectBi<>(mServices, stateFactory, dd);
	}

	@Override
	public Object getResult() {
		return mNewSimulation.getResult();
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public boolean checkResult(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean correct;
		final boolean correctOld = mOldSimulation.checkResult(stateFactory);
		final boolean correctNew = mNewSimulation.checkResult(stateFactory);
		final boolean correctMaxSat = mMaxSat.checkResult(stateFactory);
		final int oldSize = mOldSimulation.getResult().size();
		final int newSize = mNewSimulation.getResult().size();
		final int maxSatSize = mMaxSat.getResult().size();
		correct = correctOld && correctNew && correctMaxSat;
		correct = correct && oldSize == newSize && oldSize == maxSatSize;
		if (mLogger.isWarnEnabled()) {
			mLogger.warn(String.format("old: (%b, %d)  new: (%b, %d)  Max-SAT: (%b, %d)", correctOld, oldSize,
					correctNew, newSize, correctMaxSat, maxSatSize));
		}
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed", getOperationName(),
					mOperand);
		}
		return correct;
	}
}
