/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>
 *
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Minimization of NWA by reduction to MaxSAT.
 * 
 * @author Jens Stimpfle (stimpflj@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaMaxSAT<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	private final INestedWordAutomaton<LETTER, STATE> mOperand;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input NWA
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaMaxSAT(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mOperand = operand;

		printStartMessage();
		final ILogger convertLog = services.getLoggingService().getLogger("Converter");
		final ILogger generateLog = services.getLoggingService().getLogger("NwaMinimizationClausesGenerator");
		final ILogger solveLog = services.getLoggingService().getLogger("Solver");

		convertLog.info("starting conversion");
		final Converter<LETTER, STATE> converter = new Converter<>(services, stateFactory, operand);
		final NwaWithArrays nwa = converter.getNwa();
		// it shouldn't be like this, but...
		final ArrayList<Hist> history = converter.computeHistoryStates();
		convertLog.info("finished conversion. " + nwa.mNumStates + " states, " + nwa.mNumISyms + " iSyms, "
				+ nwa.mNumCSyms + " cSyms, " + nwa.mNumRSyms + " rSyms, " + nwa.mITrans.length + " iTrans, "
				+ nwa.mCTrans.length + " cTrans, " + nwa.mRTrans.length + " rTrans.");

		generateLog.info("starting clauses generation");
		final Horn3Array clauses = Generator.generateClauses(mServices, nwa, history);
		generateLog.info("finished clauses generation. " + clauses.size() + " clauses");

		solveLog.info("starting Solver");
		final char[] assignments = new Solver(mServices, clauses).solve();
		solveLog.info("finished Solver");

		generateLog.info("making equivalence classes from assignments");
		final Partition eqCls = Generator.makeMergeRelation(nwa.mNumStates, assignments);
		generateLog.info("finished making equivalence classes");

		directResultConstruction(converter.constructMerged(eqCls));
		convertLog.info("constructed minimized automaton");

		printExitMessage();
	}

	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	protected Pair<Boolean, String> checkResultHelper(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return checkLanguageEquivalence(stateFactory);
	}
}
