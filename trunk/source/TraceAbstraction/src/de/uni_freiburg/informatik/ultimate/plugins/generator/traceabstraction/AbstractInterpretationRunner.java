package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationRunner {

	private final CegarLoopBenchmarkGenerator mCegarLoopBenchmark;
	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private final RootNode mRoot;

	private final Set<Set<CodeBlock>> mKnownPathPrograms;

	private IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, IPredicate> mAbsIntResult;
	private boolean mSkipSeen;

	public AbstractInterpretationRunner(final IUltimateServiceProvider services,
			final CegarLoopBenchmarkGenerator benchmark, final RootNode root) {
		mCegarLoopBenchmark = benchmark;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mRoot = root;
		mAbsIntResult = null;
		mSkipSeen = false;
		mKnownPathPrograms = new HashSet<Set<CodeBlock>>();
	}

	/**
	 * Generate fixpoints for each program location of a path program represented by the current counterexample in the
	 * current abstraction.
	 */
	public void generateFixpoints(final IRun<CodeBlock, IPredicate> currentCex,
			final INestedWordAutomatonOldApi<CodeBlock, IPredicate> currentAbstraction) {
		assert currentCex != null : "Cannot run AI on empty counterexample";
		assert currentAbstraction != null : "Cannot run AI on empty abstraction";

		mCegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AbsIntTime);
		mAbsIntResult = null;

		if (!shouldRun(mKnownPathPrograms, currentCex)) {
			mSkipSeen = true;
			mLogger.info("Skipping current iteration for AI because path program would be the same");
			mCegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AbsIntTime);
			return;
		}

		// allow for 20% of the remaining time
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		mLogger.info("Running abstract interpretation on error trace of length " + currentCex.getLength());
		final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, IPredicate> result = AbstractInterpreter
				.runSilently((NestedRun<CodeBlock, IPredicate>) currentCex, currentAbstraction, mRoot, timer,
						mServices);
		mAbsIntResult = result;
		mCegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AbsIntTime);
	}

	private boolean shouldRun(final Set<Set<CodeBlock>> knownPathPrograms,
			final IRun<CodeBlock, IPredicate> currentCex) {

		final Set<CodeBlock> transitions = new HashSet<CodeBlock>();
		final int length = currentCex.getLength();
		for (int i = 0; i < length; ++i) {
			transitions.add(currentCex.getSymbol(i));
		}
		return knownPathPrograms.add(transitions);
	}

	public void refine(final PredicateUnifier predUnifier, final SmtManager smtManager,
			final INestedWordAutomaton<CodeBlock, IPredicate> abstraction, final IRun<CodeBlock, IPredicate> currentCex,
			final RefineFunction refineFun) throws AutomataLibraryException {
		if (mSkipSeen) {
			return;
		}
		if (mAbsIntResult == null) {
			mLogger.error("Cannot refine abstraction with AI automaton without calculating fixpoint first");
			return;
		}

		mCegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AbsIntTime);
		mLogger.info("Refining with abstract interpretation automaton");
		final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton = new AbstractInterpretationAutomatonGenerator(
				mServices, abstraction, mAbsIntResult, predUnifier, smtManager).getResult();
		boolean aiResult = refineFun.refine(aiInterpolAutomaton, predUnifier);
		assert hasAiProgress(aiResult, aiInterpolAutomaton, currentCex) : "No progress during AI refinement";
		mLogger.info("Finished additional refinement with abstract interpretation automaton. Did we make progress: "
				+ aiResult);
		mCegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AbsIntTime);

	}

	private boolean hasAiProgress(final boolean result,
			final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton,
			final IRun<CodeBlock, IPredicate> m_Counterexample) {
		if (result) {
			return result;
		}
		if (mAbsIntResult == null) {
			return true;
		}
		if (mAbsIntResult.hasReachedError()) {
			return true;
		}
		mLogger.fatal(
				"No progress during refinement with abstract interpretation although AI did not reach the error state. The following run is still accepted.");
		mLogger.fatal(m_Counterexample);
		mLogger.fatal("Used the following AI result: " + mAbsIntResult);
		mLogger.fatal("Automaton had the following predicates: " + aiInterpolAutomaton.getStates());
		return false;
	}

	@FunctionalInterface
	public interface RefineFunction {
		boolean refine(NestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton, PredicateUnifier unifier)
				throws AssertionError, OperationCanceledException, AutomataLibraryException;
	}

}
