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

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.commondata.ChoiceRequest;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.InteractiveCegar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.InterpolantSequences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.AssertionOrderModulation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.BaseRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.MultiTrackRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

/**
 * interactive {@link IRefinementStrategy} that asks the user.
 * <p>
 * The class uses a {@link StraightLineInterpolantAutomatonBuilder} for constructing the interpolant automaton.
 *
 * @author Julian Jarecki (julian.jarecki@neptun.uni-freiburg.de)
 */
public abstract class ParrotRefinementStrategy<LETTER extends IIcfgTransition<?>>
		extends MultiTrackRefinementStrategy<LETTER> {

	private BaseRefinementStrategy<LETTER> mFallback;
	private Track mNextTrack;
	private boolean mAsked;
	private boolean mInitialized;
	private Set<Track> mLeft;
	private Iterator<Track> mIterator;

	public ParrotRefinementStrategy(final ILogger logger, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IRun<LETTER, IPredicate, ?> counterexample, final IPredicate precondition, final IAutomaton<LETTER, IPredicate> abstraction,
			final TAPreferences taPrefsForInterpolantConsolidation, final TaskIdentifier taskIdentifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		super(logger, prefs, services, cfgSmtToolkit, predicateFactory, predicateUnifier, assertionOrderModulation,
				counterexample, precondition, abstraction, taPrefsForInterpolantConsolidation, taskIdentifier, emptyStackFactory);
		mInitialized = true;
	}

	protected abstract InteractiveCegar getInteractive();

	protected abstract BaseRefinementStrategy<LETTER> createFallbackStrategy(RefinementStrategy strategy);

	private void ask() {
		if (mAsked) {
			return;
		}
		mAsked = true;
		if (mLeft.isEmpty()) {
			mNextTrack = null;
			return;
		}
		final Track[] leftTracks = mLeft.stream().toArray(Track[]::new);
		final Track result;
		try {
			final StringBuilder message = new StringBuilder();
			if (mNextTrack != null) {
				message.append("The Track " + mNextTrack.name() + " has failed. ");
			}
			message.append("Please select the next Track to try.");
			result = ChoiceRequest.get(leftTracks, t -> t.name()).setLogger(mLogger).setTitle("Select Track")
					.setSubtitle(message.toString()).request(getInteractive().getInterface()).get();
		} catch (final InterruptedException | ExecutionException e) {
			mNextTrack = null;
			mLogger.error("No client answer. Aborting Parrot Strategy.", e);
			return;
		}
		if (result != null) {
			mNextTrack = result;
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

		if (!getInteractive().getPreferences().isRSS()) {
			final ParrotInteractiveIterationInfo itInfo = getInteractive().getParrotInteractiveIterationInfo();
			mLogger.info("using Fallback Strategy '" + itInfo.getFallbackStrategy() + "'.");
			mFallback = createFallbackStrategy(itInfo.getFallbackStrategy());
		}

		return mIterator;
	}

	@Override
	public boolean hasNextTraceCheck() {
		if (mFallback != null) {
			if (mFallback.hasNextTraceCheck()) {
				return true;
			}
			// Fallback has failed before user interaction.
			// so we ask the user to continue manually.
			mLogger.info(
					"Fallback Strategy " + getInteractive().getParrotInteractiveIterationInfo().getFallbackStrategy()
							+ " has failed prematurely in iteration " + mTaskIdentifier + " - asking the user");
			mFallback = null;
		}
		return super.hasNextTraceCheck();
	}

	@Override
	public void nextTraceCheck() {
		if (mFallback != null) {
			if (!mInitialized) {
				return;
			}
			mFallback.nextTraceCheck();
		} else {
			super.nextTraceCheck();
		}
	}

	@Override
	public ITraceCheck getTraceCheck() {
		return mFallback != null ? mFallback.getTraceCheck() : super.getTraceCheck();
	}

	@Override
	public boolean hasNextInterpolantGenerator(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
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
	public IInterpolantGenerator<LETTER> getInterpolantGenerator() {
		return mFallback != null ? mFallback.getInterpolantGenerator() : super.getInterpolantGenerator();
	}

	@Override
	public IInterpolantAutomatonBuilder<LETTER, IPredicate> getInterpolantAutomatonBuilder(
			final List<TracePredicates> perfectIpps, final List<TracePredicates> imperfectIpps) {
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
		return SolverBuilder.LOGIC_CVC4_DEFAULT;
	}

	@Override
	protected LBool constructAutomatonFromIpps(List<TracePredicates> perfectIpps, List<TracePredicates> imperfectIpps) {
		if (getInteractive().isInteractiveMode()) {
			final InterpolantSequences sequences = InterpolantSequences.instance.set(perfectIpps, imperfectIpps);
			if (getInteractive().getPreferences().isIPS() && perfectIpps.size() + imperfectIpps.size() > 1) {
				mLogger.info("Asking the user to select interpolant sequences.");
				try {
					final InterpolantSequences userSequences =
							getInteractive().getInterface().request(InterpolantSequences.class, sequences).get();
					perfectIpps = userSequences.mPerfectIpps;
					imperfectIpps = userSequences.mImperfectIpps;
					mLogger.info("User Selected " + perfectIpps.size() + " perfect and " + imperfectIpps.size()
							+ " imperfect interpolant sequences.");
				} catch (InterruptedException | ExecutionException e) {
					mLogger.error(e);
				}
			} else {
				getInteractive().send(sequences);
			}
		}

		return super.constructAutomatonFromIpps(perfectIpps, imperfectIpps);
	}
}
