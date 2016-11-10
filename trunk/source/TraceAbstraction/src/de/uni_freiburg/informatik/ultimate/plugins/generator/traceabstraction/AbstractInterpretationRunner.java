package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntNonSmtInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntStraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntTotalInterpolationAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AbstractInterpretationMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
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

	private final CfgSmtToolkit mCsToolkit;
	private final BoogieIcfgContainer mRoot;

	private final Set<Set<CodeBlock>> mKnownPathPrograms;
	private IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> mAbsIntResult;

	private final AbstractInterpretationMode mMode;
	private final boolean mAlwaysRefine;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	private boolean mSkipIteration;

	public AbstractInterpretationRunner(final IUltimateServiceProvider services,
			final CegarLoopStatisticsGenerator benchmark, final BoogieIcfgContainer root,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final CfgSmtToolkit csToolkit) {
		mCegarLoopBenchmark = benchmark;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mRoot = root;
		mAbsIntResult = null;
		mSkipIteration = false;
		mKnownPathPrograms = new HashSet<Set<CodeBlock>>();
		mCsToolkit = csToolkit;

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mAlwaysRefine = prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ABSINT_ALWAYS_REFINE);
		mMode = prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ABSINT_MODE,
				AbstractInterpretationMode.class);
		checkSettings();
	}

	private void checkSettings() {
		if (mMode == AbstractInterpretationMode.USE_PATH_PROGRAM && mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT,
						InterpolantAutomatonEnhancement.class) != InterpolantAutomatonEnhancement.NONE) {
			throw new IllegalArgumentException("If using \"" + TraceAbstractionPreferenceInitializer.LABEL_ABSINT_MODE
					+ "\"=" + AbstractInterpretationMode.USE_PATH_PROGRAM + " you also have to use \""
					+ TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT + "\"="
					+ InterpolantAutomatonEnhancement.NONE);
		}
		if (mMode == AbstractInterpretationMode.NONE && mAlwaysRefine) {
			throw new IllegalArgumentException("If using \"" + TraceAbstractionPreferenceInitializer.LABEL_ABSINT_MODE
					+ "\"=" + AbstractInterpretationMode.NONE + " you cannot use \""
					+ TraceAbstractionPreferenceInitializer.LABEL_ABSINT_ALWAYS_REFINE + "\"=true");
		}
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
	public void generateFixpoints(final IRun<CodeBlock, IPredicate, ?> currentCex,
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> currentAbstraction) {
		assert currentCex != null : "Cannot run AI on empty counterexample";
		assert currentAbstraction != null : "Cannot run AI on empty abstraction";
		if (mMode == AbstractInterpretationMode.NONE) {
			return;
		}

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
					.map(a -> '[' + String.valueOf(a) + ']').collect(Collectors.toList())));
			if (mLogger.isDebugEnabled()) {
				for (final CodeBlock trans : pathProgramSet) {
					mLogger.debug("[" + trans.hashCode() + "] " + trans);
				}
			}
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> result =
					AbstractInterpreter.runOnPathProgram(mRoot, currentAbstraction,
							(NestedRun<CodeBlock, IPredicate>) currentCex, pathProgramSet, timer, mServices);
			mAbsIntResult = result;
			if (hasShownInfeasibility()) {
				mCegarLoopBenchmark.announceStrongAbsInt();
			}
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		}
	}

	private boolean containsLoop(final Set<CodeBlock> pathProgramSet) {
		final Set<IcfgLocation> programPoints = new HashSet<>();
		return pathProgramSet.stream().anyMatch(a -> !programPoints.add(a.getTarget()));
	}

	/**
	 *
	 * @return true iff abstract interpretation was strong enough to prove infeasibility of the current counterexample.
	 */
	public boolean hasShownInfeasibility() {
		return mMode != AbstractInterpretationMode.NONE && mAbsIntResult != null && !mAbsIntResult.hasReachedError();
	}

	public boolean isDisabled() {
		return mMode == AbstractInterpretationMode.NONE;
	}

	public IInterpolantAutomatonBuilder<CodeBlock, IPredicate> createInterpolantAutomatonBuilder(
			final IInterpolantGenerator interpolGenerator,
			final INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			final IRun<CodeBlock, IPredicate, ?> currentCex) {
		if (mMode == AbstractInterpretationMode.NONE) {
			return null;
		}
		if (mSkipIteration) {
			return null;
		}
		if (mAbsIntResult == null) {
			mLogger.warn("Cannot construct AI interpolant automaton without calculating fixpoint first");
			return null;
		}

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		try {
			mLogger.info("Constructing AI automaton with mode " + mMode);
			final IInterpolantAutomatonBuilder<CodeBlock, IPredicate> aiInterpolAutomatonBuilder;
			switch (mMode) {
			case NONE:
				throw new AssertionError("Mode should have been checked earlier");
			case USE_PATH_PROGRAM:
				aiInterpolAutomatonBuilder = new AbsIntNonSmtInterpolantAutomatonBuilder(mServices, abstraction,
						interpolGenerator.getPredicateUnifier(), mCsToolkit.getManagedScript(),
						mRoot.getBoogie2SMT().getBoogie2SmtSymbolTable(), currentCex, mSimplificationTechnique,
						mXnfConversionTechnique);
				break;
			case USE_PREDICATES:
				aiInterpolAutomatonBuilder = new AbsIntStraightLineInterpolantAutomatonBuilder(mServices, abstraction,
						mAbsIntResult, interpolGenerator.getPredicateUnifier(), mCsToolkit, currentCex,
						mSimplificationTechnique, mXnfConversionTechnique, 
						mRoot.getBoogie2SMT().getBoogie2SmtSymbolTable());
				break;
			case USE_CANONICAL:
				throw new UnsupportedOperationException(
						"Canonical interpolant automaton generation not yet implemented.");
			case USE_TOTAL:
				aiInterpolAutomatonBuilder = new AbsIntTotalInterpolationAutomatonBuilder(mServices, abstraction,
						mAbsIntResult, interpolGenerator.getPredicateUnifier(), mCsToolkit, currentCex, 
						mRoot.getBoogie2SMT().getBoogie2SmtSymbolTable());
				break;
			default:
				throw new UnsupportedOperationException("AI mode " + mMode + " not yet implemented");
			}
			return aiInterpolAutomatonBuilder;
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		}
	}

	public void refineAnyways(final IInterpolantGenerator interpolGenerator,
			final INestedWordAutomaton<CodeBlock, IPredicate> abstraction, final IRun<CodeBlock, IPredicate, ?> cex,
			final IRefineFunction refineFun) throws AutomataLibraryException {
		if (mMode == AbstractInterpretationMode.NONE || !mAlwaysRefine || mSkipIteration) {
			return;
		}
		mLogger.info("Refining with AI automaton anyways");
		final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton =
				createInterpolantAutomatonBuilder(interpolGenerator, abstraction, cex).getResult();
		refine(interpolGenerator.getPredicateUnifier(), aiInterpolAutomaton, cex, refineFun);
	}

	/**
	 *
	 * @return true iff abstract interpretation was strong enough to prove infeasibility of the current counterexample.
	 */
	public boolean refine(final PredicateUnifier predUnifier,
			final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton,
			final IRun<CodeBlock, IPredicate, ?> currentCex, final IRefineFunction refineFun)
			throws AutomataLibraryException {
		if (mMode == AbstractInterpretationMode.NONE) {
			throw new UnsupportedOperationException("You cannot refine in mode " + AbstractInterpretationMode.NONE);
		}
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
			if (mMode == AbstractInterpretationMode.USE_PREDICATES) {
				assert hasAiProgress(aiResult, aiInterpolAutomaton, currentCex) : "No progress during AI refinement";
			}
			mLogger.info("Finished additional refinement with AI automaton. Progress: " + aiResult);
			return !mAbsIntResult.hasReachedError();
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		}
	}

	private Set<CodeBlock> convertCex2Set(final IRun<CodeBlock, IPredicate, ?> currentCex) {
		final Set<CodeBlock> transitions = new HashSet<CodeBlock>();
		// words count their states, so 0 is first state, length is last state
		final int length = currentCex.getLength() - 1;
		for (int i = 0; i < length; ++i) {
			transitions.add(currentCex.getSymbol(i));
		}
		return transitions;
	}

	private boolean hasAiProgress(final boolean result,
			final INestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton,
			final IRun<CodeBlock, IPredicate, ?> cex) {
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

	private String simplify(final Term term) {
		return SmtUtils.simplify(mCsToolkit.getManagedScript(), term, mServices, mSimplificationTechnique)
				.toStringDirect();
	}

	@FunctionalInterface
	public interface IRefineFunction {
		boolean refine(NestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton, PredicateUnifier unifier)
				throws AssertionError, AutomataOperationCanceledException, AutomataLibraryException;
	}

}
