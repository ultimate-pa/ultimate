/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayDeque;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;

/**
 * Check if word is accepted by automaton.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class Accepts<LETTER,STATE>
		extends AbstractAcceptance<LETTER,STATE>
		implements IOperation<LETTER,STATE> {

	private final NestedWord<LETTER> mWord;
	private final boolean mPrefixOfInputIsAccepted;
	private final boolean mInputIsSuffixOfAcceptedWord;

	/**
	 * @param services Ultimate services
	 * @param operand operand
	 * @param word word
	 * @param prefixOfIntputIsAccepted
	 *            is a prefix of the input accepted? Coincides with usual
	 *            acceptance for automata where accepting states can not be
	 *            left.
	 * @param inputIsSuffixOfAcceptedWord
	 *            is the input the suffix of an accepted word? Coincides with
	 *            the usual acceptance for automata where each transition can
	 *            also (nondeterministically) lead to an initial state.
	 * @throws AutomataLibraryException if acceptance fails
	 */
	public Accepts(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER,STATE> operand,
			final NestedWord<LETTER> word,
			final boolean prefixOfIntputIsAccepted,
			final boolean inputIsSuffixOfAcceptedWord)
					throws AutomataLibraryException {
		super(services, operand);
		mWord = word;
		mPrefixOfInputIsAccepted = prefixOfIntputIsAccepted;
		mInputIsSuffixOfAcceptedWord = inputIsSuffixOfAcceptedWord;
		mLogger.info(startMessage());
		mIsAccepted = isAccepted();
		mLogger.info(exitMessage());
	}
	
	/**
	 * @param services Ultimate services
	 * @param operand operand
	 * @param word word
	 * @throws AutomataLibraryException if acceptance fails
	 */
	public Accepts(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER,STATE> operand,
			final NestedWord<LETTER> word)
					throws AutomataLibraryException {
		this(services, operand, word, false, false);
	}

	@Override
	public String operationName() {
		return "acceptance";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " automaton "
				+ mOperand.sizeInformation() + ". Word has length "
				+ mWord.length();
	}

	@Override
	public String exitMessage() {
		String message = "Finished " + operationName() + ". ";
		final String quantifier = mIsAccepted ? "some " : "each ";
		if (mInputIsSuffixOfAcceptedWord) {
			if (mPrefixOfInputIsAccepted) {
				message += quantifier + "prefix of " + quantifier + "suffix ";
			} else {
				message += quantifier + "suffix ";
			}
		} else {
			if (mPrefixOfInputIsAccepted) {
				message += quantifier + "prefix ";
			} else {
				message += "word ";
			}
		}
		if (mIsAccepted) {
			message += "is accepted.";
		} else {
			message += "is rejected.";
		}
		return message;
	}
	
	private boolean isAccepted() throws AutomataLibraryException {
		Set<ArrayDeque<STATE>> currentConfigs =
				emptyStackConfiguration(mOperand.getInitialStates());
		for (int i = 0; i < mWord.length(); i++) {
			currentConfigs = successorConfigurations(currentConfigs, mWord, i,
					mOperand, mInputIsSuffixOfAcceptedWord);
			if (mPrefixOfInputIsAccepted
					&& containsAcceptingConfiguration(currentConfigs,
							mOperand)) {
				return true;
			}
		}
		return containsAcceptingConfiguration(currentConfigs, mOperand);
	}

	/**
	 * Check if set of configurations contains an accepting configuration. We
	 * say that a configuration is accepting if the topmost stack element is an
	 * accepting state.
	 * 
	 * @param configurations set of configurations
	 * @param nwa nested word automaton
	 * @return true iff configurations contain an accepting configuration
	 */
	public boolean containsAcceptingConfiguration(
			final Set<ArrayDeque<STATE>> configurations,
			final INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		for (final ArrayDeque<STATE> config : configurations) {
			if (isAcceptingConfiguration(config, mOperand)) {
				return true;
			}
		}
		return false;
	}
}
