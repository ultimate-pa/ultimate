/*
 * Copyright (C) 2017 Julian Jarecki (julian.jarecki@neptun.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientSorryException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.InteractiveLive;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.MultiTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.AssertionOrderModulation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.MultiTrackTraceAbstractionRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

/**
 * interactive {@link IRefinementStrategy} that asks the user.
 * <p>
 * The class uses a {@link MultiTrackInterpolantAutomatonBuilder} for constructing the interpolant automaton.
 *
 * @author Julian Jarecki (julian.jarecki@neptun.uni-freiburg.de)
 */
public abstract class ParrotRefinementStrategy<LETTER extends IIcfgTransition<?>>
		extends MultiTrackTraceAbstractionRefinementStrategy<LETTER> {

	private IRefinementStrategy<LETTER> mFallback;
	private Track mNextTrack;
	private boolean mAsked;
	private boolean mInitialized;
	private Set<Track> mLeft;
	private Iterator<Track> mIterator;

	public ParrotRefinementStrategy(final ILogger logger, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final PredicateUnifier predicateUnifier,
			final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IRun<LETTER, IPredicate, ?> counterexample, final IAutomaton<LETTER, IPredicate> abstraction,
			final TAPreferences taPrefsForInterpolantConsolidation, final int iteration,
			final CegarLoopStatisticsGenerator cegarLoopBenchmarks) {
		super(logger, prefs, services, cfgSmtToolkit, predicateFactory, predicateUnifier, assertionOrderModulation,
				counterexample, abstraction, taPrefsForInterpolantConsolidation, iteration, cegarLoopBenchmarks);
		mInitialized = true;
	}

	protected abstract InteractiveLive getInteractive();

	protected abstract IRefinementStrategy<LETTER> createFallbackStrategy(RefinementStrategy strategy);

	protected abstract ParrotInteractiveIterationInfo getIterationInfo();

	private void useFallbackStrategy(final ParrotInteractiveIterationInfo itInfo) {
		mLogger.info("using Fallback Strategy '" + itInfo.getFallbackStrategy() + "'.");
		mFallback = createFallbackStrategy(itInfo.getFallbackStrategy());
	}

	private void ask() {
		if (mAsked)
			return;
		mAsked = true;
		if (mLeft.isEmpty()) {
			mNextTrack = null;
			return;
		}
		Future<Track[]> answer = getInteractive().getInterface().request(Track[].class, mLeft.stream().toArray(Track[]::new));
		Track[] results;
		try {
			results = answer.get();
		} catch (InterruptedException e) {
			throw new IllegalStateException(e);
		} catch (ExecutionException e) {
			if (e.getCause() instanceof ClientSorryException) {
				mNextTrack = null;
				mLogger.error("No client answer.");
				return;
			}
			mLogger.error("No client answer. Aborting Parrot Strategy.", e);
			return;
		}
		if (results != null && results.length > 0) {
			mNextTrack = results[0];
			mLeft.remove(mNextTrack);
		}
	}

	@Override
	protected Iterator<Track> initializeInterpolationTechniquesList() {
		mIterator = new Iterator<Track>() {
			@Override
			public boolean hasNext() {
				ask();
				return mNextTrack != null;
			}

			@Override
			public Track next() {
				ask();
				mAsked = false;
				return mNextTrack;
			}
		};

		mInitialized = false;
		mAsked = false;
		mLeft = new HashSet<>();
		Arrays.stream(Track.values()).forEach(mLeft::add);

		final ParrotInteractiveIterationInfo itInfo = getIterationInfo();

		if (mIteration >= itInfo.getNextInteractiveIteration()) {
			try {
				ParrotInteractiveIterationInfo other =
						getInteractive().getInterface().request(ParrotInteractiveIterationInfo.class).get();
				itInfo.setFrom(other);
			} catch (InterruptedException | ExecutionException e) {
				mLogger.error("no client answer.");
				useFallbackStrategy(itInfo);
				return mIterator;
			}
		}
		if (mIteration < itInfo.getNextInteractiveIteration()) {
			useFallbackStrategy(itInfo);
			return mIterator;
		}

		return mIterator;
	}

	@Override
	public boolean hasNextTraceChecker() {
		if (mFallback != null) {
			if (mFallback.hasNextTraceChecker()) {
				return true;
			} else {
				// Fallback has failed before user interaction.
				// so we ask the user to continue manually.
				mLogger.info("Fallback Strategy " + getIterationInfo().getFallbackStrategy()
						+ " has failed prematurely in iteration " + mIteration + " - asking the user");
				mFallback = null;
			}
		}
		return super.hasNextTraceChecker();
	}

	@Override
	public void nextTraceChecker() {
		if (mFallback != null) {
			if (!mInitialized)
				return;
			mFallback.nextTraceChecker();
		} else {
			super.nextTraceChecker();
		}
	}

	@Override
	public TraceChecker getTraceChecker() {
		return mFallback != null ? mFallback.getTraceChecker() : super.getTraceChecker();
	}

	@Override
	public boolean hasNextInterpolantGenerator(List<InterpolantsPreconditionPostcondition> perfectIpps,
			List<InterpolantsPreconditionPostcondition> imperfectIpps) {
		return mFallback != null ? mFallback.hasNextInterpolantGenerator(perfectIpps, imperfectIpps)
				: super.hasNextInterpolantGenerator(perfectIpps, imperfectIpps);
	}

	@Override
	public void nextInterpolantGenerator() {
		if (mFallback != null) {
			mFallback.nextInterpolantGenerator();
		} else {
			super.nextInterpolantGenerator();
		}
	}

	@Override
	public IInterpolantGenerator getInterpolantGenerator() {
		return mFallback != null ? mFallback.getInterpolantGenerator() : super.getInterpolantGenerator();
	}

	@Override
	public IInterpolantAutomatonBuilder<LETTER, IPredicate> getInterpolantAutomatonBuilder(
			List<InterpolantsPreconditionPostcondition> perfectIpps,
			List<InterpolantsPreconditionPostcondition> imperfectIpps) {
		return mFallback != null ? mFallback.getInterpolantAutomatonBuilder(perfectIpps, imperfectIpps)
				: super.getInterpolantAutomatonBuilder(perfectIpps, imperfectIpps);
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mFallback != null ? mFallback.getPredicateUnifier() : super.getPredicateUnifier();
	}

	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return mFallback != null ? mFallback.getExceptionBlacklist() : super.getExceptionBlacklist();
	}

	@Override
	protected String getCvc4Logic() {
		return LOGIC_CVC4_DEFAULT;
	}
}
