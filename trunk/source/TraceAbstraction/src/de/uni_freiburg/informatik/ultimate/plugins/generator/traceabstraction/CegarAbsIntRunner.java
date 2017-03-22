/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntNonSmtInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntStraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntTotalInterpolationAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.AbsIntHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker_Map;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AbstractInterpretationMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantComputationStatus.ItpErrorStatus;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CegarAbsIntRunner<LETTER extends IIcfgTransition<?>> {

	private final CegarLoopStatisticsGenerator mCegarLoopBenchmark;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final CfgSmtToolkit mCsToolkit;
	private final IIcfg<?> mRoot;

	private final Set<Set<LETTER>> mKnownPathPrograms;

	private final AbstractInterpretationMode mMode;
	private final boolean mAlwaysRefine;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	private AbsIntCurrentIteration<?> mCurrentIteration;
	private IPredicateUnifier mPredicateUnifier;

	public CegarAbsIntRunner(final IUltimateServiceProvider services, final CegarLoopStatisticsGenerator benchmark,
			final IIcfg<?> root, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final CfgSmtToolkit csToolkit) {
		mCegarLoopBenchmark = benchmark;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mRoot = root;
		mKnownPathPrograms = new HashSet<>();
		mCsToolkit = csToolkit;

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mAlwaysRefine = prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ABSINT_ALWAYS_REFINE);
		mMode = prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ABSINT_MODE,
				AbstractInterpretationMode.class);
		checkSettings();
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
	public void generateFixpoints(final IRun<LETTER, IPredicate, ?> currentCex,
			final INestedWordAutomatonSimple<LETTER, IPredicate> currentAbstraction, final IPredicateUnifier unifier) {
		assert currentCex != null : "Cannot run AI on empty counterexample";
		assert currentAbstraction != null : "Cannot run AI on empty abstraction";

		if (!mRoot.getLocationClass().equals(BoogieIcfgLocation.class)) {
			// TODO: AI only supports BoogieIcfgLocations and Codeblocks atm, so die if this is not the type presented.
			throw new UnsupportedOperationException(
					"AbsInt only supports BoogieIcfgLocations and Codeblocks at the moment");
		}
		mPredicateUnifier = Objects.requireNonNull(unifier);
		mCurrentIteration = null;

		if (mMode == AbstractInterpretationMode.NONE) {
			return;
		}

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		try {

			final Set<LETTER> pathProgramSet = convertCex2Set(currentCex);

			if (!mKnownPathPrograms.add(pathProgramSet)) {
				mLogger.info("Skipping current iteration for AI because we have already analyzed this path program");
				return;
			}
			if (!containsLoop(pathProgramSet)) {
				mLogger.info("Skipping current iteration for AI because the path program does not contain any loops");
				return;
			}

			mCegarLoopBenchmark.announceNextAbsIntIteration();

			// allow for 20% of the remaining time
			final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
			mLogger.info("Running AI on error trace of length " + currentCex.getLength()
					+ " with the following transitions: ");
			mLogger.info(String.join(", ", pathProgramSet.stream().map(a -> a.hashCode()).sorted()
					.map(a -> '[' + String.valueOf(a) + ']').collect(Collectors.toList())));
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Trace:");
				for (final LETTER trans : currentCex.getWord().asList()) {
					mLogger.debug("[" + trans.hashCode() + "] " + trans);
				}
			}
			@SuppressWarnings("unchecked")
			final IAbstractInterpretationResult<?, LETTER, IBoogieVar, ?> result =
					(IAbstractInterpretationResult<?, LETTER, IBoogieVar, ?>) AbstractInterpreter.runOnPathProgram(
							(IIcfg<BoogieIcfgLocation>) mRoot,
							(INestedWordAutomatonSimple<CodeBlock, ?>) currentAbstraction,
							(NestedRun<CodeBlock, IPredicate>) currentCex, (Set<CodeBlock>) pathProgramSet, timer,
							mServices);
			mCurrentIteration = new AbsIntCurrentIteration<>(currentCex, result);
			if (hasShownInfeasibility()) {
				mCegarLoopBenchmark.announceStrongAbsInt();
			}
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		}
	}

	/**
	 *
	 * @return true iff abstract interpretation was strong enough to prove infeasibility of the current counterexample.
	 */
	public boolean hasShownInfeasibility() {
		return mMode != AbstractInterpretationMode.NONE && mCurrentIteration != null
				&& !mCurrentIteration.hasReachedError();
	}

	public boolean isDisabled() {
		return mMode == AbstractInterpretationMode.NONE;
	}

	public CachingHoareTripleChecker getHoareTripleChecker() {
		if (mCurrentIteration == null) {
			throw createNoFixpointsException();
		}
		return mCurrentIteration.getHoareTripleChecker();
	}

	public IInterpolantGenerator getInterpolantGenerator() {
		if (mCurrentIteration == null) {
			return new AbsIntFailedInterpolantGenerator(mPredicateUnifier, null, ItpErrorStatus.OTHER,
					createNoFixpointsException());
		}
		return mCurrentIteration.getInterpolantGenerator();
	}

	public IInterpolantAutomatonBuilder<LETTER, IPredicate> createInterpolantAutomatonBuilder(
			final IPredicateUnifier predicateUnifier, final INestedWordAutomaton<LETTER, IPredicate> abstraction,
			final IRun<LETTER, IPredicate, ?> currentCex) {
		if (mCurrentIteration == null) {
			throw createNoFixpointsException();
		}

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		try {
			mLogger.info("Constructing AI automaton with mode " + mMode);
			final IInterpolantAutomatonBuilder<LETTER, IPredicate> aiInterpolAutomatonBuilder;
			switch (mMode) {
			case NONE:
				throw new AssertionError("Mode should have been checked earlier");
			case USE_PATH_PROGRAM:
				aiInterpolAutomatonBuilder = new AbsIntNonSmtInterpolantAutomatonBuilder<>(mServices, abstraction,
						predicateUnifier, mCsToolkit.getManagedScript(), mRoot.getCfgSmtToolkit().getSymbolTable(),
						currentCex, mSimplificationTechnique, mXnfConversionTechnique);
				break;
			case USE_PREDICATES:
				aiInterpolAutomatonBuilder = new AbsIntStraightLineInterpolantAutomatonBuilder<>(mServices, abstraction,
						mCurrentIteration.getResult(), predicateUnifier, mCsToolkit, currentCex,
						mSimplificationTechnique, mXnfConversionTechnique, mRoot.getCfgSmtToolkit().getSymbolTable());
				break;
			case USE_CANONICAL:
				throw new UnsupportedOperationException(
						"Canonical interpolant automaton generation not yet implemented.");
			case USE_TOTAL:
				aiInterpolAutomatonBuilder = new AbsIntTotalInterpolationAutomatonBuilder<>(mServices, abstraction,
						mCurrentIteration.getResult(), predicateUnifier, mCsToolkit, currentCex,
						mRoot.getCfgSmtToolkit().getSymbolTable(), mSimplificationTechnique, mXnfConversionTechnique);
				break;
			default:
				throw new UnsupportedOperationException("AI mode " + mMode + " not yet implemented");
			}
			return aiInterpolAutomatonBuilder;
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
		}
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

	private boolean containsLoop(final Set<LETTER> pathProgramSet) {
		final Set<IcfgLocation> programPoints = new HashSet<>();
		return pathProgramSet.stream().anyMatch(a -> !programPoints.add(a.getTarget()));
	}

	private static UnsupportedOperationException createNoFixpointsException() {
		return new UnsupportedOperationException(
				"AbsInt can only provide a hoare triple checker if it generated fixpoints");
	}

	private Set<LETTER> convertCex2Set(final IRun<LETTER, IPredicate, ?> currentCex) {
		final Set<LETTER> transitions = new HashSet<>();
		// words count their states, so 0 is first state, length is last state
		final int length = currentCex.getLength() - 1;
		for (int i = 0; i < length; ++i) {
			transitions.add(currentCex.getSymbol(i));
		}
		return transitions;
	}

	private final class AbsIntCurrentIteration<STATE extends IAbstractState<STATE, IBoogieVar>> {
		private final IRun<LETTER, IPredicate, ?> mCex;
		private final IAbstractInterpretationResult<STATE, LETTER, IBoogieVar, ?> mResult;

		private IInterpolantGenerator mInterpolantGenerator;
		private CachingHoareTripleChecker mHtc;
		private final AbsIntPredicate<STATE, IBoogieVar> mFalsePredicate;

		public AbsIntCurrentIteration(final IRun<LETTER, IPredicate, ?> cex,
				final IAbstractInterpretationResult<STATE, LETTER, IBoogieVar, ?> result) {
			mCex = Objects.requireNonNull(cex);
			mResult = Objects.requireNonNull(result);
			mFalsePredicate = new AbsIntPredicate<>(mPredicateUnifier.getFalsePredicate(),
					mResult.getUsedDomain().createBottomState());
		}

		public IAbstractInterpretationResult<STATE, LETTER, IBoogieVar, ?> getResult() {
			return mResult;
		}

		public boolean hasReachedError() {
			return mResult.hasReachedError();
		}

		public CachingHoareTripleChecker getHoareTripleChecker() {
			if (mHtc == null) {
				final IHoareTripleChecker htc = new AbsIntHoareTripleChecker<>(mLogger, mServices,
						mResult.getUsedDomain(), mResult.getUsedVariableProvider(), mPredicateUnifier, mCsToolkit);
				mHtc = new CachingHoareTripleChecker_Map(mServices, htc, mPredicateUnifier);
			}
			return mHtc;
		}

		public IInterpolantGenerator getInterpolantGenerator() {
			if (mInterpolantGenerator == null) {
				mInterpolantGenerator = createInterpolantGenerator();
			}
			return mInterpolantGenerator;
		}

		private IInterpolantGenerator createInterpolantGenerator() {
			if (mResult.hasReachedError()) {
				// analysis was not strong enough
				return new AbsIntFailedInterpolantGenerator(mPredicateUnifier, mCex.getWord(),
						ItpErrorStatus.ALGORITHM_FAILED, null);
			}
			// we were strong enough!
			final Word<LETTER> word = mCex.getWord();
			try {
				final List<AbsIntPredicate<STATE, IBoogieVar>> interpolants = generateInterpolants(word);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Interpolant sequence:");
					mLogger.debug(interpolants);
				}
				assert word.length() - 1 == interpolants.size() : "Word has length " + word.length()
						+ " but interpolant sequence has length " + interpolants.size();
				return new AbsIntInterpolantGenerator(mPredicateUnifier, mCex.getWord(),
						interpolants.toArray(new IPredicate[interpolants.size()]), getHoareTripleChecker());
			} catch (final ToolchainCanceledException tce) {
				tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), "generating AI predicates"));
				throw tce;
			}
		}

		private List<AbsIntPredicate<STATE, IBoogieVar>> generateInterpolants(final Word<LETTER> word) {
			mLogger.info("Generating AI predicates...");

			final List<AbsIntPredicate<STATE, IBoogieVar>> rtr = new ArrayList<>();
			final Deque<LETTER> callstack = new ArrayDeque<>();
			final Script script = mCsToolkit.getManagedScript().getScript();
			final int wordlength = word.length();
			Set<STATE> previousStates = Collections.emptySet();
			for (int i = 0; i < wordlength - 1; i++) {
				final LETTER symbol = word.getSymbol(i);
				if (symbol instanceof ICallAction) {
					callstack.addFirst(symbol);
				} else if (symbol instanceof IReturnAction) {
					callstack.removeFirst();
				}
				final Set<STATE> postStates = mResult.getPostStates(callstack, symbol, previousStates);
				final AbsIntPredicate<STATE, IBoogieVar> next = getPredicateFromStates(postStates, script);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(symbol + " " + next);
				}
				previousStates = postStates;
				rtr.add(next);
			}
			return rtr;
		}

		private AbsIntPredicate<STATE, IBoogieVar> getPredicateFromStates(final Set<STATE> postStates,
				final Script script) {
			if (postStates.isEmpty()) {
				return mFalsePredicate;
			}
			final Set<IPredicate> predicates = postStates.stream().map(s -> s.getTerm(script))
					.map(mPredicateUnifier::getOrConstructPredicate).collect(Collectors.toSet());
			final IPredicate disjunction = mPredicateUnifier.getOrConstructPredicateForDisjunction(predicates);
			return new AbsIntPredicate<>(disjunction, postStates);
		}
	}

	private static final class AbsIntInterpolantGenerator extends AbsIntBaseInterpolantGenerator {

		private final IPredicate[] mInterpolants;
		private final CachingHoareTripleChecker mHtc;

		private AbsIntInterpolantGenerator(final IPredicateUnifier predicateUnifier, final Word<? extends IAction> cex,
				final IPredicate[] sequence, final CachingHoareTripleChecker htc) {
			super(predicateUnifier, cex, new InterpolantComputationStatus(true, null, null));
			mInterpolants = Objects.requireNonNull(sequence);
			mHtc = Objects.requireNonNull(htc);
		}

		@Override
		public CachingHoareTripleChecker getHoareTripleChecker() {
			// evil hack but Matthias does not want to change the architecture.
			return mHtc;
		}

		@Override
		public Map<Integer, IPredicate> getPendingContexts() {
			// TODO: Do I need this?
			return null;
		}

		@Override
		public IPredicate[] getInterpolants() {
			return mInterpolants;
		}

		@Override
		public boolean isPerfectSequence() {
			// if we have a sequence, its always perfect
			return true;
		}

	}

	private static final class AbsIntFailedInterpolantGenerator extends AbsIntBaseInterpolantGenerator {

		private AbsIntFailedInterpolantGenerator(final IPredicateUnifier predicateUnifier,
				final Word<? extends IAction> cex, final ItpErrorStatus status, final Exception ex) {
			super(predicateUnifier, cex, new InterpolantComputationStatus(false, status, ex));
		}

		@Override
		public Map<Integer, IPredicate> getPendingContexts() {
			throw new UnsupportedOperationException();
		}

		@Override
		public IPredicate[] getInterpolants() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isPerfectSequence() {
			// if we fail there is no sequence
			return false;
		}

		@Override
		public CachingHoareTripleChecker getHoareTripleChecker() {
			throw new UnsupportedOperationException();
		}
	}
}
