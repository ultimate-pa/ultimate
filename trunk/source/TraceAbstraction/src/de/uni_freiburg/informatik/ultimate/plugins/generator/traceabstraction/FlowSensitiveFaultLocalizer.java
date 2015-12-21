/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collections;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * 
 * @author Numair Mansur
 * @author Matthias Heizmann
 * @author Christian Schilling
 * 
 *
 */
public class FlowSensitiveFaultLocalizer {

	private IUltimateServiceProvider m_Services;
	private final Logger m_Logger;

	public FlowSensitiveFaultLocalizer(NestedWord<CodeBlock> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg, IUltimateServiceProvider services, SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager, PredicateUnifier predicateUnifier) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		
		IPredicate errorPrecondition = computeErrorPrecondition(counterexample, smtManager, predicateUnifier, modGlobVarManager);
		Object informationFromCFG = computeInformationFromCFG(counterexample, cfg);
		computeFlowSensitiveTraceFormula(errorPrecondition, counterexample, predicateUnifier.getFalsePredicate(), modGlobVarManager, smtManager);
	}

	private Object computeInformationFromCFG(NestedWord<CodeBlock> counterexample,
			INestedWordAutomaton<CodeBlock, IPredicate> cfg) {
		// use findPathInCFG
		NestedRun<CodeBlock, IPredicate> test = findPathInCFG(null, null, cfg);
		return null;
	}

	private void computeFlowSensitiveTraceFormula(IPredicate errorPrecondition, NestedWord<CodeBlock> counterexample,
			IPredicate falsePredicate, ModifiableGlobalVariableManager modGlobVarManager, SmtManager smtManager) {
		
		// nice representation of error trace (important for interprocedural traces)
		DefaultTransFormulas nestedTransFormulas = new DefaultTransFormulas(counterexample, errorPrecondition, falsePredicate, null, modGlobVarManager, false);
		NestedSsaBuilder ssaBuilder = new NestedSsaBuilder(counterexample, smtManager, nestedTransFormulas, modGlobVarManager, m_Logger, false);
		// nice representation where all variables have been renamed
		NestedFormulas<Term, Term> ssa = ssaBuilder.getSsa();
		
		
		
	}

	private IPredicate computeErrorPrecondition(NestedWord<CodeBlock> counterexample, SmtManager smtManager,
			PredicateUnifier predicateUnifier, ModifiableGlobalVariableManager modGlobVarManager) {
		PredicateTransformer pt = new PredicateTransformer(smtManager, modGlobVarManager, m_Services);
		// iterate over the counterexample and compute the error precondition
		return null;
	}
	
	
	/**
	 * Check if there is a path from startPoint so some element of the 
	 * possibleEndPoints set.
	 * If yes, a NestedRun is returned, otherwise null is returned.
	 * 
	 * @throws ToolchainCanceledException if toolchain was cancelled (e.g., 
	 * because of a timeout)
	 */
	private NestedRun<CodeBlock, IPredicate> findPathInCFG(IPredicate startPoint, 
			Set<IPredicate> possibleEndPoints, INestedWordAutomaton<CodeBlock, 
			IPredicate> cfg) {
		try {
			return (new IsEmpty<CodeBlock, IPredicate>(m_Services, cfg, 
					Collections.singleton(startPoint), possibleEndPoints)).getNestedRun();
		} catch (OperationCanceledException e) {
			throw new ToolchainCanceledException(getClass());
		}
	}
	
}