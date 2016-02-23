/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;

import org.apache.log4j.Logger;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;

public class MinimizeNwaMaxSAT<LETTER, STATE>
		implements IOperation<LETTER, STATE> {

	private final NestedWordAutomaton<LETTER, STATE> m_result;

	public MinimizeNwaMaxSAT(
			AutomataLibraryServices services,
			StateFactory<STATE> stateFactory,
			INestedWordAutomaton<LETTER, STATE> automaton) {
		Logger logger = services.getLoggingService().getLogger(operationName());
		Logger convertLog = services.getLoggingService().getLogger("NiceConvert");
		Logger generateLog = services.getLoggingService().getLogger("MergeRelationClausesGenerator");
		Logger solveLog = services.getLoggingService().getLogger("MaxSATSolve");

		logger.info(startMessage());
		/*logger.info("input follows");
		logger.info(automaton);
		*/

		convertLog.info("starting conversion");
		NiceConvert<LETTER, STATE> converter = new NiceConvert<LETTER, STATE>(services, stateFactory, automaton);
		NiceNWA nwa = converter.getNiceNWA();
		// it shouldn't be like this, but...
		ArrayList<NiceHist> history = converter.computeHistoryStates();
		convertLog.info(
				"finished conversion. "
				+ Integer.toString(nwa.numStates) + " states, "
				+ Integer.toString(nwa.numISyms) + " iSyms, "
				+ Integer.toString(nwa.numCSyms) + " cSyms, "
				+ Integer.toString(nwa.numRSyms) + " rSyms, "
				+ Integer.toString(nwa.iTrans.length) + " iTrans, "
				+ Integer.toString(nwa.cTrans.length) + " cTrans, "
				+ Integer.toString(nwa.rTrans.length) + " rTrans."
		);
		/*convertLog.info("converted automaton follows");
		convertLog.info(NicePrint.makeString(nwa));
		*/

		generateLog.info("starting clauses generation");
		ArrayList<HornClause3> clauses = NwaMinimizationClausesGenerator.generateConstraints(nwa, history);
		generateLog.info("finished clauses generation. " + Integer.toString(clauses.size()) + " clauses");

		solveLog.info("starting MaxSATSolve");
		Assign[] assignments = new MaxSATSolve(clauses).solve();
		solveLog.info("finished MaxSATSolve");

		generateLog.info("making equivalence classes from assignments");
		NiceClasses eqCls = NwaMinimizationClausesGenerator.makeMergeRelation(nwa.numStates, assignments);
		generateLog.info("finished making equivalence classes");
		/*logger.info("equivalence classes following");
		logger.info(NicePrint.makeString(eqCls));
		 */

		logger.info("Testing correctness of equivalence classes");
		NiceCorrectness.testCorrectness(nwa, history, eqCls);

		m_result = converter.constructMerged(eqCls);
		convertLog.info("constructed minimized automaton");

		logger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "MinimizeNwaMaxSAT";
	}

	@Override
	public String startMessage() {
		return "starting MinimizeNwaMaxSAT";
	}

	@Override
	public String exitMessage() {
		return "ending MinimizeNwaMaxSAT";
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) {
		/* TODO */
		return true;
	}

	@Override
	public NestedWordAutomaton<LETTER, STATE> getResult() {
		return m_result;
	}
}
