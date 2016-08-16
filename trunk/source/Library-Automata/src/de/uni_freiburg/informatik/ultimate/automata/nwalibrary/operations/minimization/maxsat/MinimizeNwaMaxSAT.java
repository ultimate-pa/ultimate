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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.AMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.IMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Minimization of NWA by reduction to MaxSAT.
 * 
 * @author Jens Stimpfle (stimpflj@informatik.uni-freiburg.de)
 *
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class MinimizeNwaMaxSAT<LETTER, STATE>
		extends AMinimizeNwa<LETTER, STATE>
		implements IMinimizeNwa<LETTER, STATE>, IOperation<LETTER, STATE> {

	/**
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param automaton input NWA
	 */
	public MinimizeNwaMaxSAT(
			final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> automaton) {
		super(services, stateFactory, "MinimizeNwaMaxSAT", automaton);

		final ILogger convertLog = services.getLoggingService().getLogger(
				"Converter");
		final ILogger generateLog = services.getLoggingService().getLogger(
				"NwaMinimizationClausesGenerator");
		final ILogger solveLog = services.getLoggingService().getLogger(
				"Solver");

		convertLog.info("starting conversion");
		final Converter<LETTER, STATE> converter =
				new Converter<LETTER, STATE>(services, stateFactory, automaton);
		final NWA nwa = converter.getNWA();
		// it shouldn't be like this, but...
		final ArrayList<Hist> history = converter.computeHistoryStates();
		convertLog.info(
				"finished conversion. "
				+ Integer.toString(nwa.mNumStates) + " states, "
				+ Integer.toString(nwa.mNumISyms) + " iSyms, "
				+ Integer.toString(nwa.mNumCSyms) + " cSyms, "
				+ Integer.toString(nwa.mNumRSyms) + " rSyms, "
				+ Integer.toString(nwa.mITrans.length) + " iTrans, "
				+ Integer.toString(nwa.mCTrans.length) + " cTrans, "
				+ Integer.toString(nwa.mRTrans.length) + " rTrans."
		);

		generateLog.info("starting clauses generation");
		final Horn3Array clauses = Generator.generateClauses(nwa, history);
		generateLog.info("finished clauses generation. " +
				Integer.toString(clauses.size()) + " clauses");

		solveLog.info("starting Solver");
		final char[] assignments = new Solver(clauses).solve();
		solveLog.info("finished Solver");

		generateLog.info("making equivalence classes from assignments");
		final Partition eqCls = Generator.makeMergeRelation(nwa.mNumStates, assignments);
		generateLog.info("finished making equivalence classes");

		directResultConstruction(converter.constructMerged(eqCls));
		convertLog.info("constructed minimized automaton");

		mLogger.info(exitMessage());
	}
}
