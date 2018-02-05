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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * <tt>GOAL</tt> format writer.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class GoalFormatWriter<LETTER, STATE> extends CommonExternalFormatWriter<LETTER, STATE> {
	private static final int MINIMUM_SKELETON_SIZE = 130;
	private static final String STATE_ID_CLOSE = "</StateID>";
	private static final String STATE_ID_OPEN = "<StateID>";
	private static final char TAB = '\t';

	private final IConverter<LETTER> mLetterConverter;
	private final IConverter<STATE> mStateConverter;

	/**
	 * @param writer
	 *            Print writer.
	 * @param nwa
	 *            nested word automaton
	 */
	public GoalFormatWriter(final PrintWriter writer, final INestedWordAutomaton<LETTER, STATE> nwa) {
		super(writer, nwa);
		mLetterConverter = new MapBasedConverter<>(mAlphabetMapping);
		mStateConverter = new MapBasedConverter<>(mStateMapping);
		doPrint();
		finish();
	}

	private void doPrint() {
		final StringBuilder builder = new StringBuilder(MINIMUM_SKELETON_SIZE);
		// @formatter:off
		builder.append("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>")
				.append(NEW_LINE)
				.append("<Structure label-on=\"Transition\" type=\"FiniteStateAutomaton\">")
				.append(NEW_LINE);
		// @formatter:on
		constructAlphabetSection(builder);
		constructStateSection(builder);
		constructInitialStateSection(builder);
		constructTransitionSection(builder);
		constructAcceptingStateSection(builder);
		// @formatter:off
		builder.append("</Structure>")
				.append(NEW_LINE);
		// @formatter:on

		print(builder);
	}

	private void constructAlphabetSection(final StringBuilder builder) {
		// @formatter:off
		builder.append(TAB)
				.append("<Alphabet type=\"Classical\">")
				.append(NEW_LINE);
		for (final LETTER letter : mNwa.getVpAlphabet().getInternalAlphabet()) {
			builder.append(TAB)
					.append(TAB)
					.append("<Symbol>")
					.append(mLetterConverter.convert(letter))
					.append("</Symbol>")
					.append(NEW_LINE);
		}
		builder.append(TAB)
				.append("</Alphabet>")
				.append(NEW_LINE);
		// @formatter:on
	}

	private void constructStateSection(final StringBuilder builder) {
		// @formatter:off
		builder.append(TAB)
				.append("<StateSet>")
				.append(NEW_LINE);
		for (final STATE state : mNwa.getStates()) {
			builder.append(TAB)
					.append(TAB)
					.append("<State sid=\"")
					.append(mStateConverter.convert(state))
					.append("\" />")
					.append(NEW_LINE);
		}
		builder.append(TAB)
				.append("</StateSet>")
				.append(NEW_LINE);
		// @formatter:on
	}

	private void constructInitialStateSection(final StringBuilder builder) {
		// @formatter:off
		builder.append(TAB)
				.append("<InitialStateSet>")
				.append(NEW_LINE);
		for (final STATE state : mNwa.getInitialStates()) {
			builder.append(TAB)
					.append(TAB)
					.append(STATE_ID_OPEN)
					.append(mStateConverter.convert(state))
					.append(STATE_ID_CLOSE)
					.append(NEW_LINE);
		}
		builder.append(TAB)
				.append("</InitialStateSet>")
				.append(NEW_LINE);
		// @formatter:on
	}

	private void constructTransitionSection(final StringBuilder builder) {
		int tid = 0;
		// @formatter:off
		builder.append(TAB)
				.append("<TransitionSet complete=\"false\">")
				.append(NEW_LINE);
		for (final STATE state : mNwa.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(state)) {
				builder.append(TAB)
						.append(TAB)
						.append("<Transition tid=\"")
						.append(tid)
						.append("\"><From>")
						.append(mStateConverter.convert(state))
						.append("</From><To>")
						.append(mStateConverter.convert(trans.getSucc()))
						.append("</To><Label>")
						.append(mLetterConverter.convert(trans.getLetter()))
						.append("</Label></Transition>")
						.append(NEW_LINE);
				tid++;
			}
		}
		builder.append(TAB)
				.append("</TransitionSet>")
				.append(NEW_LINE);
		// @formatter:on
	}

	private void constructAcceptingStateSection(final StringBuilder builder) {
		// @formatter:off
		builder.append(TAB)
				.append("<Acc type=\"Buchi\">")
				.append(NEW_LINE);
		for (final STATE state : mNwa.getFinalStates()) {
			builder.append(TAB)
					.append(TAB)
					.append(STATE_ID_OPEN)
					.append(mStateConverter.convert(state))
					.append(STATE_ID_CLOSE)
					.append(NEW_LINE);
		}
		builder.append(TAB)
				.append("</Acc>")
				.append(NEW_LINE);
		// @formatter:on
	}
}
