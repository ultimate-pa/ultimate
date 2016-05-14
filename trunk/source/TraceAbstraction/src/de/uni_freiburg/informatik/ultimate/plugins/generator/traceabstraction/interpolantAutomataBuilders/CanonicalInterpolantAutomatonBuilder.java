/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;

/**
 * Constructs the canonical interpolant automaton. Boolean flags determine if we
 * also add selfloops in the initial and final state. I think this construction
 * is unsound if the precondition if not the "true" predicate.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class CanonicalInterpolantAutomatonBuilder extends CoverageAnalysis {

	private final NestedWordAutomaton<CodeBlock, IPredicate> m_IA;

	private final boolean m_SelfloopAtInitial = false;
	private final boolean m_SelfloopAtFinal = true;

	private final SmtManager m_SmtManager;

	private final Map<Integer, Set<IPredicate>> m_AlternativeCallPredecessors = new HashMap<Integer, Set<IPredicate>>();

	public CanonicalInterpolantAutomatonBuilder(IUltimateServiceProvider services, 
			IInterpolantGenerator interpolantGenerator, List<ProgramPoint> programPointSequence,
			InCaReAlphabet<CodeBlock> alphabet, SmtManager smtManager, StateFactory<IPredicate> predicateFactory,
			ILogger logger) {
		super(services, interpolantGenerator, programPointSequence, logger);
		m_IA = new NestedWordAutomaton<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), alphabet.getInternalAlphabet(),
				alphabet.getCallAlphabet(), alphabet.getReturnAlphabet(), predicateFactory);
		m_SmtManager = smtManager;
	}

	protected void processCodeBlock(int i) {
		// interpolant after the CodeBlock
		IPredicate successorInterpolant = m_IPP.getInterpolant(i + 1);
		if (!m_IA.getStates().contains(successorInterpolant)) {
			assert (successorInterpolant != m_InterpolantGenerator.getPostcondition());
			m_IA.addState(false, false, successorInterpolant);
		}
		addTransition(i, i, i + 1);
	}

	protected void processCoveringResult(int currentPosition, int previousOccurrence, LBool lbool) {
		if (lbool == LBool.UNSAT) {
			addTransition(currentPosition - 1, currentPosition - 1, previousOccurrence);
			addTransition(currentPosition, previousOccurrence, previousOccurrence + 1);
		}
	}

	protected void postprocess() {
		if (m_SelfloopAtInitial) {
			IPredicate precond = m_InterpolantGenerator.getPrecondition();
			for (CodeBlock symbol : m_IA.getInternalAlphabet()) {
				m_IA.addInternalTransition(precond, symbol, precond);
			}
			for (CodeBlock symbol : m_IA.getCallAlphabet()) {
				m_IA.addCallTransition(precond, symbol, precond);
			}
			for (CodeBlock symbol : m_IA.getReturnAlphabet()) {
				m_IA.addReturnTransition(precond, precond, symbol, precond);
				for (Integer pos : m_AlternativeCallPredecessors.keySet()) {
					for (IPredicate hier : m_AlternativeCallPredecessors.get(pos)) {
						m_IA.addReturnTransition(precond, hier, symbol, precond);
					}
				}
			}
		}

		if (m_SelfloopAtFinal) {
			IPredicate postcond = m_InterpolantGenerator.getPostcondition();
			for (CodeBlock symbol : m_IA.getInternalAlphabet()) {
				m_IA.addInternalTransition(postcond, symbol, postcond);
			}
			for (CodeBlock symbol : m_IA.getCallAlphabet()) {
				m_IA.addCallTransition(postcond, symbol, postcond);
			}
			for (CodeBlock symbol : m_IA.getReturnAlphabet()) {
				m_IA.addReturnTransition(postcond, postcond, symbol, postcond);
				for (Integer pos : m_AlternativeCallPredecessors.keySet()) {
					for (IPredicate hier : m_AlternativeCallPredecessors.get(pos)) {
						m_IA.addReturnTransition(postcond, hier, symbol, postcond);
					}
				}
			}
		}
	}

	protected void preprocess() {
		String interpolantAutomatonType = "Constructing canonical interpolant automaton";
		if (m_SelfloopAtInitial) {
			interpolantAutomatonType += ", with selfloop in true state";
		}
		if (m_SelfloopAtFinal) {
			interpolantAutomatonType += ", with selfloop in false state";
		}
		mLogger.info(interpolantAutomatonType);

		m_IA.addState(true, false, m_InterpolantGenerator.getPrecondition());
		m_IA.addState(false, true, m_InterpolantGenerator.getPostcondition());
	}

	public NestedWordAutomaton<CodeBlock, IPredicate> getInterpolantAutomaton() {
		return m_IA;
	}

	private void addTransition(int prePos, int symbolPos, int succPos) {
		IPredicate pred = m_IPP.getInterpolant(prePos);
		IPredicate succ = m_IPP.getInterpolant(succPos);
		CodeBlock symbol = (CodeBlock) m_NestedWord.getSymbol(symbolPos);
		if (m_NestedWord.isCallPosition(symbolPos)) {
			m_IA.addCallTransition(pred, symbol, succ);
			if (m_IPP.getInterpolant(prePos) != m_IPP.getInterpolant(symbolPos)) {
				addAlternativeCallPredecessor(symbolPos, m_IPP.getInterpolant(prePos));
			}
		} else if (m_NestedWord.isReturnPosition(symbolPos)) {
			int callPos = m_NestedWord.getCallPosition(symbolPos);
			IPredicate hier = m_IPP.getInterpolant(callPos);
			m_IA.addReturnTransition(pred, hier, symbol, succ);
			addAlternativeReturnTransitions(pred, callPos, symbol, succ);
		} else {
			m_IA.addInternalTransition(pred, symbol, succ);
		}
	}

	private void addAlternativeCallPredecessor(int symbolPos, IPredicate alternativeCallPredecessor) {
		Set<IPredicate> alts = m_AlternativeCallPredecessors.get(symbolPos);
		if (alts == null) {
			alts = new HashSet<IPredicate>();
			m_AlternativeCallPredecessors.put(symbolPos, alts);
		}
		alts.add(alternativeCallPredecessor);
	}

	private void addAlternativeReturnTransitions(IPredicate pred, int callPos, CodeBlock symbol, IPredicate succ) {
		if (m_AlternativeCallPredecessors.get(callPos) == null) {
			return;
		}
		for (IPredicate hier : m_AlternativeCallPredecessors.get(callPos)) {
			LBool isInductive = m_SmtManager.isInductiveReturn(pred, hier, (Return) symbol, succ);
			mLogger.debug("Trying to add alternative call Predecessor");
			if (isInductive == Script.LBool.UNSAT) {
				m_IA.addReturnTransition(pred, hier, symbol, succ);
				mLogger.debug("Added return from alternative call Pred");
			}
		}
	}

}
