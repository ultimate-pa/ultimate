package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

public class AbstractInterpretationPathProgramGenerator
        implements IAbstractInterpretationAutomatonGenerator<CodeBlock, IPredicate> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final NestedWordAutomaton<CodeBlock, IPredicate> mResult;
	private final SmtManager mSmtManager;

	public AbstractInterpretationPathProgramGenerator(final IUltimateServiceProvider services,
	        final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
	        final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult,
	        final PredicateUnifier predUnifier, final SmtManager smtManager) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSmtManager = smtManager;

		mResult = getPathProgramAutomaton(oldAbstraction, aiResult);
	}

	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return mResult;
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> getPathProgramAutomaton(
	        final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
	        final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult) {

		mLogger.info("Creating automaton from AI predicates.");

		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<>(
		        new AutomataLibraryServices(mServices), oldAbstraction.getInternalAlphabet(),
		        oldAbstraction.getCallAlphabet(), oldAbstraction.getReturnAlphabet(), oldAbstraction.getStateFactory());

		return result;
	}

}
