package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

/**
 * InterpolatingTraceChecker that returns path invariants as interpolants.
 * If no path invariants are available, Craig interpolation is used as a 
 * fallback.
 * 
 * @author Matthias Heizmann
 */
public class InterpolatingTraceCheckerPathInvariantsWithFallback extends
		InterpolatingTraceChecker {
	
	private final NestedRun<CodeBlock, IPredicate> m_NestedRun;
	
	public InterpolatingTraceCheckerPathInvariantsWithFallback(
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			NestedRun<CodeBlock, IPredicate> run, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			AssertCodeBlockOrder assertCodeBlocksIncrementally,
			IUltimateServiceProvider services,
			boolean computeRcfgProgramExecution,
			PredicateUnifier predicateUnifier) {
		super(precondition, postcondition, pendingContexts, run.getWord(), smtManager,
				modifiedGlobals, assertCodeBlocksIncrementally, services,
				computeRcfgProgramExecution, predicateUnifier);
		m_NestedRun = run;
		if (super.isCorrect() == LBool.UNSAT) {
			super.unlockSmtManager();
			computeInterpolants(new AllIntegers(), INTERPOLATION.PathInvariants);
		}
	}

	@Override
	protected void computeInterpolants(Set<Integer> interpolatedPositions,
			INTERPOLATION interpolation) {
		PathInvariantsGenerator pathInvariantsGenerator = new PathInvariantsGenerator(
				super.mServices, m_NestedRun, super.getPrecondition(), 
				super.getPostcondition(), m_PredicateUnifier, super.m_SmtManager,
				m_ModifiedGlobals);
		IPredicate[] interpolants = pathInvariantsGenerator.getInterpolants();
		if (interpolants == null) {
			interpolants = fallbackInterpolantComputation();
		}
		m_Interpolants = interpolants;
	}

	private IPredicate[] fallbackInterpolantComputation() {
		throw new UnsupportedOperationException("fallback comutation not yet implemented");
	}

}
