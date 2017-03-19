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
package de.uni_freiburg.informatik.ultimate.automata;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.GetRandomNestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

@Deprecated
public final class ResultChecker {
	private static int sResultCheckStackHeight;
	private static final int MAX_RESULT_CHECK_STACK_HEIGHT = 1;

	private ResultChecker() {
		// empty private constructor
	}

	public static <LETTER, STATE> boolean buchiComplement(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> operand,
			final INestedWordAutomatonSimple<LETTER, STATE> result) throws AutomataLibraryException {
		final ILogger logger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		if (sResultCheckStackHeight >= MAX_RESULT_CHECK_STACK_HEIGHT) {
			return true;
		}
		sResultCheckStackHeight++;
		logger.info("Testing correctness of buchiComplement");

		final int maxLength = Math.max(operand.size(), result.size());
		final int numberOfSamples = 10;
		boolean correct = true;
		for (int i = 0; i < numberOfSamples; i++) {
			final NestedLassoWord<LETTER> lasso = getRandomNestedLassoWord(operand, maxLength);
			final boolean operandAccepts = (new BuchiAccepts<>(services, operand, lasso)).getResult();
			final boolean resultAccepts = (new BuchiAccepts<>(services, result, lasso)).getResult();
			if (operandAccepts ^ resultAccepts) {
				// check passed
			} else {
				correct = false;
				final String message = "// Problem with lasso " + lasso.toString();
				AutomatonDefinitionPrinter.writeToFileIfPreferred(services, "FailedBuchiComplementCheck", message,
						operand);
				break;
			}
		}

		// INestedWordAutomaton intersection = (new Intersect(true, false, operand, result)).getResult();
		// NestedLassoRun ctx = new EmptinessCheck().getAcceptingNestedLassoRun(intersection);
		// boolean correct = (ctx == null);
		// assert (correct);

		logger.info("Finished testing correctness of complementBuchi");
		sResultCheckStackHeight--;
		return correct;
	}

	public static <LETTER, STATE> NestedLassoWord<LETTER>
			getRandomNestedLassoWord(final INestedWordAutomatonSimple<LETTER, STATE> automaton, final int size) {
		final long seed = 0;
		final NestedWord<LETTER> stem = (new GetRandomNestedWord<>(null, automaton, size, seed)).getResult();
		final NestedWord<LETTER> loop = (new GetRandomNestedWord<>(null, automaton, size, seed)).getResult();
		return new NestedLassoWord<>(stem, loop);
	}
}
