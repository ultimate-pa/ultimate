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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.MultiTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;

/**
 * interactive {@link IRefinementStrategy} that asks the user.
 * <p>
 * The class uses a {@link MultiTrackInterpolantAutomatonBuilder} for
 * constructing the interpolant automaton.
 *
 * @author Julian Jarecki (julian.jarecki@neptun.uni-freiburg.de)
 */
public abstract class ParrotRefinementStrategy<LETTER extends IIcfgTransition<?>>
		extends MultiTrackTraceAbstractionRefinementStrategy<LETTER> {
	public ParrotRefinementStrategy(final ILogger logger, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateUnifier predicateUnifier, final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IRun<LETTER, IPredicate, ?> counterexample, final IAutomaton<LETTER, IPredicate> abstraction,
			final TAPreferences taPrefsForInterpolantConsolidation, final int iteration,
			final CegarLoopStatisticsGenerator cegarLoopBenchmarks) {
		super(logger, prefs, services, cfgSmtToolkit, predicateUnifier, assertionOrderModulation, counterexample,
				abstraction, taPrefsForInterpolantConsolidation, iteration, cegarLoopBenchmarks);
	}

	protected abstract IInteractive<Object> getInteractive();

	@Override
	protected Iterator<Track> initializeInterpolationTechniquesList() {
		final Set<Track> left = new HashSet<>();
		Arrays.stream(Track.values()).forEach(left::add);
		return new Iterator<Track>() {
			private Track mNextTrack;
			private boolean mAsked = false;

			private void ask() {
				if (mAsked)
					return;
				Future<Track[]> answer = getInteractive().request(Track[].class, left.stream().toArray(Track[]::new));
				mAsked = true;
				Track[] results;
				try {
					results = answer.get();
				} catch (InterruptedException | ExecutionException e) {
					mLogger.error("no client answer.");
					throw new IllegalStateException(e);
				}
				if (results != null && results.length > 0) {
					mNextTrack = results[0];
					left.remove(mNextTrack);
				}
			}

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
	}

	@Override
	protected String getCvc4Logic() {
		return LOGIC_CVC4_DEFAULT;
	}
}
