/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * Build an interpolant automaton whose shape is a straight line.
 * The input for this construction is a TraceChecker that has proven that
 * its trace is infeasible.
 * The result of this construction is a NestedWordAutomaton object that can 
 * still be modified by adding additional states or transitions.
 * The result has one initial state which is the precondition of the trace 
 * check, the result has one accepting/final state which is the postcondition
 * of the trace check, the result has one state for each interpolant,
 * the result has one transition for each CodeBlock in the trace.
 * The result accepts the word/trace of the trace check. IPredicates may occur
 * several times in the array of interpolants, hence the resulting automaton
 * may also have loops and accept more than a single word.
 * @author Matthias Heizmann
 *
 */
public class StraightLineInterpolantAutomatonBuilder {
	private final IUltimateServiceProvider m_Services;
	
	private final NestedWordAutomaton<CodeBlock, IPredicate> m_Result;
	
	public StraightLineInterpolantAutomatonBuilder(
			IUltimateServiceProvider services, 
			InCaReAlphabet<CodeBlock> alphabet,
			IInterpolantGenerator interpolantGenerator,
			PredicateFactory predicateFactory) {
		m_Services = services;
		InterpolantsPreconditionPostcondition ipp = 
				new InterpolantsPreconditionPostcondition(interpolantGenerator);
		m_Result =	new NestedWordAutomaton<CodeBlock, IPredicate>(
				m_Services, 
						alphabet.getInternalAlphabet(),
						alphabet.getCallAlphabet(),
						alphabet.getReturnAlphabet(),
						predicateFactory);
		addStatesAndTransitions(interpolantGenerator, predicateFactory, ipp);
	}

	private void addStatesAndTransitions(IInterpolantGenerator interpolantGenerator, 
			PredicateFactory predicateFactory, InterpolantsPreconditionPostcondition ipp) { 

		m_Result.addState(true, false, interpolantGenerator.getPrecondition());
		m_Result.addState(false, true, interpolantGenerator.getPostcondition());
		NestedWord<CodeBlock> trace = (NestedWord<CodeBlock>) interpolantGenerator.getTrace();
		for (int i=0; i<trace.length(); i++) {
			IPredicate pred = ipp.getInterpolant(i);
			IPredicate succ = ipp.getInterpolant(i+1);
			assert m_Result.getStates().contains(pred);
			if (!m_Result.getStates().contains(succ)) {
				m_Result.addState(false, false, succ);
			}
			if (trace.isCallPosition(i)) {
				m_Result.addCallTransition(pred, trace.getSymbol(i), succ);
			} else if (trace.isReturnPosition(i)) {
				assert !trace.isPendingReturn(i);
				int callPos = trace.getCallPosition(i);
				IPredicate hierPred = ipp.getInterpolant(callPos);
				m_Result.addReturnTransition(pred, hierPred, trace.getSymbol(i), succ);
			} else {
				assert trace.isInternalPosition(i);
				m_Result.addInternalTransition(pred, trace.getSymbol(i), succ);
			}
		}
	}


	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return m_Result;
	}
	
}
