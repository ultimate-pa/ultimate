/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * Check if word is accepted by automaton.
 * 
 * @param prefixOfIntputIsAccepted
 *            is a prefix of the input accepted? Coincides with usual
 *            acceptance for automata where accepting states can not be
 *            left.
 * @param inputIsSuffixOfAcceptedWord
 *            is the input the suffix of an accepted word? Coincides with
 *            the usual acceptance for automata where each transition can
 *            also (nondeterministically) lead to an initial state.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class Accepts<LETTER,STATE> extends AbstractAcceptance<LETTER,STATE>
									  implements IOperation<LETTER,STATE> {

	private final INestedWordAutomatonSimple<LETTER,STATE> m_Automaton;
	private final NestedWord<LETTER> m_Word;
	private final boolean m_PrefixOfInputIsAccepted;
	private final boolean m_InputIsSuffixOfAcceptedWord;
	private boolean m_IsAccepted;

	private static Logger s_Logger = NestedWordAutomata.getLogger();


	public Accepts(INestedWordAutomatonSimple<LETTER,STATE> automaton, NestedWord<LETTER> word,
			boolean prefixOfIntputIsAccepted,
			boolean inputIsSuffixOfAcceptedWord) {
		super();
		this.m_Automaton = automaton;
		this.m_Word = word;
		this.m_PrefixOfInputIsAccepted = prefixOfIntputIsAccepted;
		this.m_InputIsSuffixOfAcceptedWord = inputIsSuffixOfAcceptedWord;
		s_Logger.info(startMessage());
		m_IsAccepted = isAccepted();
		s_Logger.info(exitMessage());
	}
	public Accepts(INestedWordAutomatonSimple<LETTER,STATE> automaton, NestedWord<LETTER> word) {
		this(automaton, word, false, false);
	}

	@Override
	public String operationName() {
		return "accptance";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " automaton "
				+ m_Automaton.sizeInformation() + ". " + "word has length "
				+ m_Word.length();
	}

	@Override
	public String exitMessage() {
		String message = "Finished " + operationName() + ". ";
		String quantifier = m_IsAccepted ? "some " : "each ";
		if (m_InputIsSuffixOfAcceptedWord) {
			if (m_PrefixOfInputIsAccepted) {
				message += quantifier + "prefix of " + quantifier + "suffix ";
			} else {
				message += quantifier + "suffix ";
			}
		} else {
			if (m_PrefixOfInputIsAccepted) {
				message += quantifier + "prefix ";
			} else {
				message += "word ";
			}
		}
		if (m_IsAccepted) {
			message += "is accepted.";
		} else {
			message += "is rejected.";
		}
		return message;
	}

	@Override
	public Boolean getResult() throws OperationCanceledException {
		return m_IsAccepted;
	}

	private boolean isAccepted() {
		Set<Stack<STATE>> currentConfigs = emptyStackConfiguration(m_Automaton.getInitialStates());
		for (int i = 0; i < m_Word.length(); i++) {
			currentConfigs = successorConfigurations(currentConfigs, m_Word, i,
					m_Automaton, m_InputIsSuffixOfAcceptedWord);
			if (m_PrefixOfInputIsAccepted
					&& containsAcceptingConfiguration(currentConfigs,
							m_Automaton)) {
				return true;
			}
		}
		if (containsAcceptingConfiguration(currentConfigs, m_Automaton)) {
			return true;
		} else {
			return false;
		}

	}

	/**
	 * Check if set of configurations contains an accepting configuration. We
	 * say that a configuration is accepting if the topmost stack element is an
	 * accepting state.
	 */
	public boolean containsAcceptingConfiguration(Set<Stack<STATE>> configurations,
			INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		for (Stack<STATE> config : configurations) {
			if (isAcceptingConfiguration(config, m_Automaton)) {
				return true;
			}
		}
		return false;
	}
	
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) {
		return true;
	}


}
