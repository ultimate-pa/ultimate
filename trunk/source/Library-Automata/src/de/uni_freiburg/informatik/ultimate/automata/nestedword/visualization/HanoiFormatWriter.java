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
 * {@code Hanoi} format writer.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class HanoiFormatWriter<LETTER, STATE> extends CommonExternalFormatWriter<LETTER, STATE> {
	private static final int MINIMUM_HEADER_SIZE = 137;
	private static final int MINIMUM_STATE_SIZE = 15;

	private static final boolean USE_LABELS = false;

	private final IConverter<LETTER> mLetterConverter;

	/**
	 * @param writer
	 *            Print writer.
	 * @param nwa
	 *            nested word automaton
	 */
	public HanoiFormatWriter(final PrintWriter writer, final INestedWordAutomaton<LETTER, STATE> nwa) {
		super(writer, nwa);
		mLetterConverter = USE_LABELS ? new ToStringConverter<>() : new MapBasedConverter<>(mAlphabetMapping);
		doPrint();
		finish();
	}

	private void doPrint() {
		final StringBuilder header = constructHeader();
		print(header);
		final String bodyToken = "--BODY--";
		print(bodyToken);
		print(NEW_LINE);
		final StringBuilder body = constructBody();
		print(body);
		final String endToken = "--END--";
		print(endToken);
	}

	@SuppressWarnings("squid:S1698")
	private StringBuilder constructHeader() {
		final StringBuilder builder = new StringBuilder(MINIMUM_HEADER_SIZE);
		// @formatter:off
		builder.append("HOA: v1")
				.append(NEW_LINE)
				//
				.append("States: ")
				.append(mNwa.getStates().size())
				.append(NEW_LINE);

		for (final STATE state : mNwa.getInitialStates()) {
			builder.append("Start: ")
					.append(mStateMapping.get(state))
					.append(NEW_LINE);
		}

		builder.append("AP: ")
				.append(mNwa.getVpAlphabet().getInternalAlphabet().size());
		for (final LETTER letter : mNwa.getVpAlphabet().getInternalAlphabet()) {
			builder.append(" \"p")
					.append(mLetterConverter.convert(letter) + QUOTE);
		}
		builder.append(NEW_LINE);

		for (final LETTER letter : mNwa.getVpAlphabet().getInternalAlphabet()) {
			builder.append("Alias: @")
					.append(mAlphabetMapping.get(letter));
			boolean firstOther = true;
			for (final LETTER otherLetter : mNwa.getVpAlphabet().getInternalAlphabet()) {
				if (firstOther) {
					firstOther = false;
				} else {
					builder.append(" &");
				}
				// comparison with '==' is fine here because the letters come from a set
				if (otherLetter == letter) {
					builder.append(' ')
							.append(mAlphabetMapping.get(otherLetter));
				} else {
					builder.append(" !")
							.append(mAlphabetMapping.get(otherLetter));
				}
			}
			builder.append(NEW_LINE);
		}

		builder.append("Acceptance: 1 Inf(0)")
				.append(NEW_LINE)
				//
				.append("acc-name: Buchi")
				.append(NEW_LINE)
				//
				.append("tool: \"Ultimate Automata Library\"")
				.append(NEW_LINE);
		// @formatter:on

		return builder;
	}

	private StringBuilder constructBody() {
		final StringBuilder builder = new StringBuilder(MINIMUM_STATE_SIZE * mNwa.size());

		for (final STATE state : mNwa.getStates()) {
			// @formatter:off
			builder.append("State: ")
					.append(mStateMapping.get(state));
			if (USE_LABELS) {
				builder.append(" \"")
						.append(state)
						.append(QUOTE);
			}
			if (mNwa.isFinal(state)) {
				builder.append(" {0}");
			}
			builder.append(NEW_LINE);
			for (final LETTER letter : mNwa.lettersInternal(state)) {
				for (final OutgoingInternalTransition<LETTER, STATE> tes : mNwa.internalSuccessors(state, letter)) {
					builder.append("[@")
							.append(mAlphabetMapping.get(tes.getLetter()))
							.append("] ")
							.append(mStateMapping.get(tes.getSucc()))
							.append(NEW_LINE);
				}
			}
			// @formatter:on
		}
		return builder;
	}
}
