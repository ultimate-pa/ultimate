/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * <tt>BA</tt> format writer.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BaFormatWriter<LETTER, STATE> extends CommonExternalFormatWriter<LETTER, STATE> {
	private static final int MINIMUM_STATE_SIZE = 4;
	private static final int MINIMUM_TRANSITION_SIZE = 11;

	/**
	 * @param writer
	 *            Print writer.
	 * @param nwa
	 *            nested word automaton
	 */
	public BaFormatWriter(final PrintWriter writer, final INestedWordAutomaton<LETTER, STATE> nwa) {
		super(writer, nwa);
		doPrint();
		finish();
	}

	private void doPrint() {
		final StringBuilder initStateSb = getStateString(mNwa.getInitialStates(), mStateMapping);
		final StringBuilder transSb = getTransitionString(mNwa, mStateMapping, mAlphabetMapping);
		final StringBuilder finalStateSb = getStateString(mNwa.getFinalStates(), mStateMapping);
		print(initStateSb);
		print(transSb);
		print(finalStateSb);
	}

	private StringBuilder getStateString(final Collection<STATE> initialStates, final Map<STATE, String> stateMapping) {
		final StringBuilder result = new StringBuilder(MINIMUM_STATE_SIZE * initialStates.size());
		for (final STATE state : initialStates) {
			// @formatter:off
			result.append('[')
					.append(stateMapping.get(state))
					.append(']')
					.append(NEW_LINE);
			// @formatter:on
		}
		return result;
	}

	private StringBuilder getTransitionString(final INestedWordAutomaton<LETTER, STATE> nwa,
			final Map<STATE, String> stateMapping, final Map<LETTER, String> alphabetMapping) {
		final StringBuilder result = new StringBuilder(MINIMUM_TRANSITION_SIZE * nwa.size());
		for (final STATE state : nwa.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : nwa.internalSuccessors(state)) {
				// @formatter:off
				result.append(alphabetMapping.get(outTrans.getLetter()))
						.append(",[")
						.append(stateMapping.get(state))
						.append("]->[")
						.append(stateMapping.get(outTrans.getSucc()))
						.append(']')
						.append(NEW_LINE);
				// @formatter:on
			}
		}
		return result;
	}
}
