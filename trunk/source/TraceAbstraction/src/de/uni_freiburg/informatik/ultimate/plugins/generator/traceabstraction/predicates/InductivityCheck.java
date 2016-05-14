/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Check if each edge of automaton is inductive (resp. if inductivity can be
 * refuted if <i>antiInductivity</i> is set).
 * 
 * @param antiInductivity
 *            if false, we check if each edge is inductive, if true we check if
 *            inductivity of each edge can be refuted.
 * @param assertInductivity
 *            if true, assert statements require inductivity (resp.
 *            anti-inductivity)
 */
public class InductivityCheck {

	private final IUltimateServiceProvider m_Services;
	private final ILogger m_Logger;
	

	private final INestedWordAutomaton<CodeBlock, IPredicate> nwa;
	
	private final IHoareTripleChecker m_HoareTripleChecker;
	private final boolean m_AntiInductivity;
	private final boolean m_AssertInductivity;
	private final int[] yield = new int[3];
	private final boolean m_Result;

	public InductivityCheck(IUltimateServiceProvider services, INestedWordAutomaton<CodeBlock, IPredicate> m_Nwa, boolean m_AntiInductivity,
			boolean m_AssertInductivity, IHoareTripleChecker hoareTripleChecker) {
		super();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		this.nwa = m_Nwa;
		this.m_HoareTripleChecker = hoareTripleChecker;
		this.m_AntiInductivity = m_AntiInductivity;
		this.m_AssertInductivity = m_AssertInductivity;
		m_Result = checkInductivity();
	}

	public boolean getResult() {
		return m_Result;
	}

	private boolean checkInductivity() {
		if (m_AntiInductivity) {
			m_Logger.debug("Start checking anti-inductivity of automaton");
		} else {
			m_Logger.debug("Start checking inductivity of automaton");
		}

		boolean result = true;
		// yield[0] is the number of edges whose inductiveness could be
		// proven
		// yield[1] is the number of edges whose inductiveness could be
		// refuted
		// yield[2] is the number of edges whose inductiveness could be
		// neither proven nor refuted because theorem prover too weak
		// yield[3] is the number of edges whose inductiveness could be
		// neither proven nor refuted because there were no interpolants

		for (IPredicate state : nwa.getStates()) {
			for (CodeBlock cb : nwa.lettersInternal(state)) {
				for (OutgoingInternalTransition<CodeBlock, IPredicate> outTrans : nwa.internalSuccessors(state, cb)) {
					Validity inductivity = m_HoareTripleChecker.checkInternal(state, (IInternalAction) cb, outTrans.getSucc());
					evaluateResult(inductivity, state, outTrans);
				}
			}
			for (CodeBlock cb : nwa.lettersCall(state)) {
				for (OutgoingCallTransition<CodeBlock, IPredicate> outTrans : nwa.callSuccessors(state, cb)) {
					Validity inductivity = m_HoareTripleChecker.checkCall(state, (ICallAction) cb, outTrans.getSucc());
					evaluateResult(inductivity, state, outTrans);
				}
			}
			for (CodeBlock cb : nwa.lettersReturn(state)) {
				for (IPredicate hier : nwa.hierPred(state, cb)) {
					for (OutgoingReturnTransition<CodeBlock, IPredicate> outTrans : nwa.returnSucccessors(state, hier,
							cb)) {
						Validity inductivity = m_HoareTripleChecker.checkReturn(state, hier, (IReturnAction) cb, outTrans.getSucc());
						evaluateResult(inductivity, state, outTrans);
					}
				}
			}
		}
		if (m_HoareTripleChecker instanceof IncrementalHoareTripleChecker) {
			((IncrementalHoareTripleChecker) m_HoareTripleChecker).clearAssertionStack();
		}
		m_Logger.info("Interpolant automaton has " + (yield[0] + yield[1] + yield[2]) + " edges. " + yield[0]
				+ " inductive. " + yield[1] + " not inductive. " + yield[2] + " times theorem prover too"
				+ " weak to decide inductivity. ");
		return result;
	}

	private boolean evaluateResult(Validity inductivity, IPredicate state, Object trans) {
		boolean result = true;
		switch (inductivity) {
		case VALID: {
			yield[0]++;
			if (m_AntiInductivity) {
				m_Logger.warn("Transition " + state + " " + trans + " not anti inductive");
				result = false;
				assert !m_AssertInductivity || result : "anti inductivity failed";
			}
			break;
		}
		case INVALID: {
			yield[1]++;
			if (!m_AntiInductivity) {
				m_Logger.warn("Transition " + state + " " + trans + " not inductive");
				result = false;
				assert !m_AssertInductivity || result : "inductivity failed";
			}
			break;
		}
		case UNKNOWN: {
			yield[2]++;
			break;
		}
		default:
			throw new IllegalArgumentException();
		}
		return result;
	}
}
