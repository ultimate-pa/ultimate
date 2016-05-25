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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class MinimizeNwaMaxSAT<LETTER, STATE>
		implements IOperation<LETTER, STATE> {

	private final AutomataLibraryServices mservices;
	private final INestedWordAutomaton<LETTER, STATE> moperand;

	private final NestedWordAutomaton<LETTER, STATE> mresult;

	public MinimizeNwaMaxSAT(
			AutomataLibraryServices services,
			StateFactory<STATE> stateFactory,
			INestedWordAutomaton<LETTER, STATE> automaton) {

		mservices = services;
		moperand = automaton;

		final ILogger logger = services.getLoggingService().getLogger(operationName());
		final ILogger convertLog = services.getLoggingService().getLogger("Converter");
		final ILogger generateLog = services.getLoggingService().getLogger("NwaMinimizationClausesGenerator");
		final ILogger solveLog = services.getLoggingService().getLogger("Solver");

		logger.info(startMessage());

		convertLog.info("starting conversion");
		final Converter<LETTER, STATE> converter = new Converter<LETTER, STATE>(services, stateFactory, automaton);
		final NWA nwa = converter.getNWA();
		// it shouldn't be like this, but...
		final ArrayList<Hist> history = converter.computeHistoryStates();
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

		generateLog.info("starting clauses generation");
		final Horn3Array clauses = Generator.generateClauses(nwa, history);
		generateLog.info("finished clauses generation. " + Integer.toString(clauses.size()) + " clauses");

		solveLog.info("starting Solver");
		final char[] assignments = new Solver(clauses).solve();
		solveLog.info("finished Solver");

		generateLog.info("making equivalence classes from assignments");
		final Partition eqCls = Generator.makeMergeRelation(nwa.numStates, assignments);
		generateLog.info("finished making equivalence classes");

		mresult = converter.constructMerged(eqCls);
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
	public NestedWordAutomaton<LETTER, STATE> getResult() {
		return mresult;
	}

	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (checkInclusion(moperand, getResult(), stateFactory)
			&& checkInclusion(getResult(), moperand, stateFactory)) {
			return true;
		} else {
			ResultChecker.writeToFileIfPreferred(mservices, operationName() + " failed", "language equality check failed", moperand);
			return false;
		}
	 }

	/**
	 * This method checks language inclusion of the first automaton wrt. the
	 * second automaton.
	 *
	 * @param subset
	 *			  automaton describing the subset language
	 * @param superset
	 *			  automaton describing the superset language
	 * @param stateFactory
	 *			  state factory
	 * @return <code>true</code> iff language is included
	 * @throws AutomataLibraryException
	 *			   thrown by inclusion check
	 */
	private final boolean checkInclusion(
			final INestedWordAutomatonSimple<LETTER, STATE> subset,
			final INestedWordAutomatonSimple<LETTER, STATE> superset,
			final StateFactory<STATE> stateFactory)
				throws AutomataLibraryException {
		return ResultChecker.nwaLanguageInclusion(mservices,
				ResultChecker.getOldApiNwa(mservices, subset),
				ResultChecker.getOldApiNwa(mservices, superset),
				stateFactory) == null;
	}
}
