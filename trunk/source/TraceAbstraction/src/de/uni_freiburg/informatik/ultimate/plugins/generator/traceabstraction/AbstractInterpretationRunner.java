package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationRunner {

	private final CegarLoopStatisticsGenerator mCegarLoopBenchmark;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final RootNode mRoot;

	private final Set<Set<CodeBlock>> mKnownPathPrograms;

	private IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> mAbsIntResult;
	private boolean mSkipIteration;

	public AbstractInterpretationRunner(final IUltimateServiceProvider services,
	        final CegarLoopStatisticsGenerator benchmark, final RootNode root) {
		mCegarLoopBenchmark = benchmark;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRoot = root;
		mAbsIntResult = null;
		mSkipIteration = false;
		mKnownPathPrograms = new HashSet<Set<CodeBlock>>();
	}

	/**
	 * Generate fixpoints for each program location of a path program represented by the current counterexample in the
	 * current abstraction.
	 * 
	 * Do not run if
	 * <ul>
	 * <li>We have already analyzed the exact same path program.
	 * <li>The path program does not contain any loops.
	 * </ul>
	 */
	public void generateFixpoints(final IRun<CodeBlock, IPredicate> currentCex,
	        final INestedWordAutomatonOldApi<CodeBlock, IPredicate> currentAbstraction) {
		assert currentCex != null : "Cannot run AI on empty counterexample";
		assert currentAbstraction != null : "Cannot run AI on empty abstraction";

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		try {
			mAbsIntResult = null;

			final Set<CodeBlock> pathProgramSet = convertCex2Set(currentCex);

			if (!mKnownPathPrograms.add(pathProgramSet)) {
				mSkipIteration = true;
				mLogger.info("Skipping current iteration for AI because we have already analyzed this path program");
				return;
			}
			if (!containsLoop(pathProgramSet)) {
				mSkipIteration = true;
				mLogger.info("Skipping current iteration for AI because the path program does not contain any loops");
				return;
			}

			mSkipIteration = false;
			mCegarLoopBenchmark.announceNextAbsIntIteration();

			// allow for 20% of the remaining time
			final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
			mLogger.info("Running AI on error trace of length " + currentCex.getLength()
			        + " with the following transitions: ");
			mLogger.info(String.join(", ", pathProgramSet.stream().map(a -> a.hashCode()).sorted()
					.map(a -> "[" + String.valueOf(a) + "]").collect(Collectors.toList())));
			if (mLogger.isDebugEnabled()) {
				for (final CodeBlock trans : pathProgramSet) {
					mLogger.debug("[" + trans.hashCode() + "] " + trans);
				}
			}
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> result =
					AbstractInterpreter.runOnPathProgram((NestedRun<CodeBlock, IPredicate>) currentCex,
							currentAbstraction, mRoot, timer, mServices);
			mAbsIntResult = result;
			if (hasShownInfeasibility()) {
				mCegarLoopBenchmark.announceStrongAbsInt();
			}
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		}
	}

	private boolean containsLoop(final Set<CodeBlock> pathProgramSet) {
		final Set<RCFGNode> programPoints = new HashSet<>();
		return pathProgramSet.stream().anyMatch(a -> !programPoints.add(a.getTarget()));
	}

	/**
	 * 
	 * @return true iff abstract interpretation was strong enough to prove infeasibility of the current counterexample.
	 */
	public boolean hasShownInfeasibility() {
		return mAbsIntResult != null && !mAbsIntResult.hasReachedError();
	}

	public NestedWordAutomaton<CodeBlock, IPredicate> constructInterpolantAutomaton(final PredicateUnifier predUnifier,
			final SmtManager smtManager, final INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			final IRun<CodeBlock, IPredicate> currentCex) {
		if (mSkipIteration) {
			return null;
		}
		if (mAbsIntResult == null) {
			mLogger.warn("Cannot construct AI interpolant automaton without calculating fixpoint first");
			return null;
		}

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		try {
			mLogger.info("Constructing AI automaton");
			final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton;
			final IPreferenceProvider pref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
			if (pref.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_USE_AI_PATH_PROGRAM_CONSTRUCTION)
			        && pref.getEnum(TraceAbstractionPreferenceInitializer.LABEL_InterpolantAutomatonEnhancement,
			                InterpolantAutomatonEnhancement.class) == InterpolantAutomatonEnhancement.NONE) {
				mLogger.info("Using path program construction from abstract interpretation predicates.");
				aiInterpolAutomaton = new AbstractInterpretationPathProgramGenerator(mServices, abstraction,
				        predUnifier, smtManager, currentCex).getResult();
			} else {
				mLogger.info("Using NWA construction from abstract interpretation predicates.");
				aiInterpolAutomaton = new AbstractInterpretationPredicateAutomatonGenerator(mServices, abstraction,
				        mAbsIntResult, predUnifier, smtManager).getResult();
			}
			return aiInterpolAutomaton;
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		}
	}

	public void refineAnyways(final PredicateUnifier predUnifier, final SmtManager smtManager,
	        final INestedWordAutomaton<CodeBlock, IPredicate> abstraction, final IRun<CodeBlock, IPredicate> cex,
	        final RefineFunction refineFun) throws AutomataLibraryException {
		mLogger.info("Refining with AI automaton anyways");
		final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton = constructInterpolantAutomaton(
		        predUnifier, smtManager, abstraction, cex);
		refine(predUnifier, aiInterpolAutomaton, cex, refineFun);
	}

	/**
	 * 
	 * @return true iff abstract interpretation was strong enough to prove infeasibility of the current counterexample.
	 */
	public boolean refine(final PredicateUnifier predUnifier,
	        final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton,
	        final IRun<CodeBlock, IPredicate> currentCex, final RefineFunction refineFun)
	        throws AutomataLibraryException {
		if (mSkipIteration) {
			mLogger.debug("Cannot refine with AI when iteration was skipped");
			return false;
		}
		if (mAbsIntResult == null) {
			mLogger.warn("Cannot refine abstraction with AI automaton without calculating fixpoint first");
			return false;
		}

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		try {
			mLogger.info("Refining with AI automaton");
			final boolean aiResult = refineFun.refine(aiInterpolAutomaton, predUnifier);
			// TODO Check!!!
			//assert hasAiProgress(aiResult, aiInterpolAutomaton, currentCex) : "No progress during AI refinement";
			mLogger.info("Finished additional refinement with AI automaton. Did we make progress: " + aiResult);
			return !mAbsIntResult.hasReachedError();
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		}
	}

	private Set<CodeBlock> convertCex2Set(final IRun<CodeBlock, IPredicate> currentCex) {
		final Set<CodeBlock> transitions = new HashSet<CodeBlock>();
		// words count their states, so 0 is first state, length is last state
		final int length = currentCex.getLength() - 1;
		for (int i = 0; i < length; ++i) {
			transitions.add(currentCex.getSymbol(i));
		}
		return transitions;
	}

	private boolean hasAiProgress(final boolean result,
	        final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton,
	        final IRun<CodeBlock, IPredicate> cex) {
		if (result) {
			return result;
		}
		if (mAbsIntResult == null) {
			return true;
		}
		if (mAbsIntResult.hasReachedError()) {
			return true;
		}
		mLogger.fatal("No progress during refinement with AI. The following run is still accepted.");
		mLogger.fatal(cex);
		mLogger.fatal("Used the following AI result: " + mAbsIntResult.toSimplifiedString(this::simplify));
		mLogger.fatal("Automaton had the following predicates: " + aiInterpolAutomaton.getStates());
		return false;
	}

	private String simplify(Term term) {
		return SmtUtils.simplify(mRoot.getRootAnnot().getScript(), term, mServices).toStringDirect();
	}

	@FunctionalInterface
	public interface RefineFunction {
		boolean refine(NestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton, PredicateUnifier unifier)
		        throws AssertionError, AutomataOperationCanceledException, AutomataLibraryException;
	}

}
