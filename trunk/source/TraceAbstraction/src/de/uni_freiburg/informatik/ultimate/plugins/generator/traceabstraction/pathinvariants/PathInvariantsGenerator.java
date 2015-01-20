package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

public class PathInvariantsGenerator implements IInterpolantGenerator {
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	private final NestedRun<CodeBlock, IPredicate> m_Run;
	private final IPredicate m_Precondition;
	private final IPredicate m_Postcondition;
	private final PredicateUnifier m_PredicateUnifier;
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	private final SmtManager m_SmtManager;
	

	public PathInvariantsGenerator(IUltimateServiceProvider services,
			NestedRun<CodeBlock, IPredicate> run, IPredicate precondition,
			IPredicate postcondition, PredicateUnifier predicateUnifier,
			SmtManager smtManager, 
			ModifiableGlobalVariableManager modGlobVarManager) {
		super();
		m_Services = services;
		m_Logger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Run = run;
		m_Precondition = precondition;
		m_Postcondition = postcondition;
		m_PredicateUnifier = predicateUnifier;
		m_ModifiableGlobalVariableManager = modGlobVarManager;
		m_SmtManager = smtManager;
		
	}

	@Override
	public Word<CodeBlock> getTrace() {
		return m_Run.getWord();
	}

	@Override
	public IPredicate getPrecondition() {
		return m_Precondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return m_Postcondition;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		throw new UnsupportedOperationException("Call/Return not supported yet");
	}

	@Override
	public IPredicate[] getInterpolants() {
		// TODO Auto-generated method stub
		return null;
	}
	
}
