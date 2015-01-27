package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.Map;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

public class TraceCheckerWithAccessibleSSATerms extends TraceChecker {
	
	Script m_script;

	public TraceCheckerWithAccessibleSSATerms(IPredicate precondition,
			IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			NestedWord<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			AssertCodeBlockOrder assertCodeBlocksIncrementally,
			IUltimateServiceProvider services, boolean computeRcfgProgramExecution, 
			PredicateUnifier predicateUnifier, INTERPOLATION interpolation) {
		super(precondition, postcondition, pendingContexts, trace, smtManager, modifiedGlobals, 
				assertCodeBlocksIncrementally, services, computeRcfgProgramExecution);
//		super(precondition, postcondition, pendingContexts, trace, smtManager,
//				modifiedGlobals, assertCodeBlocksIncrementally, services,
//				computeRcfgProgramExecution, predicateUnifier, interpolation);
		m_script = smtManager.getScript();
	}
	
//	public Term[] computeInterpolants(Term[] partition, int[] startOfSubtree) {
//		return m_script.getInterpolants(partition, startOfSubtree);
//	}
	
	public void traceCheckFinished() {
		m_TraceCheckFinished = true;
	}
	
	public Term getAnnotatedSSATerm(int position) {
		return m_AAA.getAnnotatedSsa().getFormulaFromNonCallPos(position);
	}
	
	public Term getSSATerm(int position) {
		return m_Nsb.getSsa().getFormulaFromNonCallPos(position);
	}
	
	public Map<Term, BoogieVar> getConstantsToBoogieVar() {
		return m_Nsb.getConstants2BoogieVar();
	}
}
