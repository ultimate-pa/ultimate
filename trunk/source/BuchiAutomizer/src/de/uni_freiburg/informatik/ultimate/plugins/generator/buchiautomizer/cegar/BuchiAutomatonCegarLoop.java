/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiClosureNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.GeneralizedBuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.GeneralizedDifference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.UtilFixedCounterexample;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RefineBuchi;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiComplementationConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.NcsbImplementation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class BuchiAutomatonCegarLoop<L extends IIcfgTransition<?>>
		extends AbstractBuchiCegarLoop<L, INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {

	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final PredicateFactoryResultChecking mPredicateFactoryResultChecking;
	private final RefineBuchi<L> mRefineBuchi;
	private final BuchiComplementationConstruction mComplementationConstruction;

	public BuchiAutomatonCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction,
			final PredicateFactoryRefinement stateFactoryForRefinement,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		super(icfg, rankVarConstructor, predicateFactory, taPrefs, services, transitionClazz, initialAbstraction,
				benchmarkGenerator);
		mPredicateFactoryResultChecking = new PredicateFactoryResultChecking(predicateFactory);
		mStateFactoryForRefinement = stateFactoryForRefinement;
		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final NcsbImplementation ncsbImplementation =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_NCSB_IMPLEMENTATION, NcsbImplementation.class);
		final boolean difference =
				baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_DETERMINIZATION_ON_DEMAND);
		mRefineBuchi = new RefineBuchi<>(difference, mDefaultStateFactory, stateFactoryForRefinement, mUseDoubleDeckers,
				new AutomataLibraryServices(services), ncsbImplementation);
		mComplementationConstruction =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BUCHI_COMPLEMENTATION_CONSTRUCTION,
						BuchiComplementationConstruction.class);
	}

	@Override
	protected boolean isAbstractionEmpty(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction)
			throws AutomataLibraryException {
		final String counterName = mIdentifier + "_" + getClass().getName() + "Abstraction";
		final UtilFixedCounterexample<L, IPredicate> utilFixedCe = new UtilFixedCounterexample<>();
		final NestedLassoRun<L, IPredicate> counterexample = utilFixedCe
				.getNestedLassoRun(new AutomataLibraryServices(mServices), abstraction, counterName, mIteration);
		if (counterexample != null) {
			mCounterexample = counterexample;
		} else {
			if (abstraction instanceof IGeneralizedNestedWordAutomaton) {
				final GeneralizedBuchiIsEmpty<L, IPredicate> ec =
						new GeneralizedBuchiIsEmpty<>(new AutomataLibraryServices(mServices),
								(IGeneralizedNestedWordAutomaton<L, IPredicate>) abstraction);
				if (ec.getResult()) {
					return true;
				}
				mCounterexample = ec.getAcceptingNestedLassoRun();
			} else {
				final BuchiIsEmpty<L, IPredicate> ec =
						new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), abstraction);
				if (ec.getResult()) {
					return true;
				}
				mCounterexample = ec.getAcceptingNestedLassoRun();
			}
			utilFixedCe.writeNestedLassoRun(abstraction, mCounterexample, counterName, mIteration);
		}

		final HistogramOfIterable<L> traceHistogramStem =
				new HistogramOfIterable<>(mCounterexample.getStem().getWord());
		mBenchmarkGenerator.reportTraceHistogramMaximum(traceHistogramStem.getMax());
		final HistogramOfIterable<L> traceHistogramLoop =
				new HistogramOfIterable<>(mCounterexample.getLoop().getWord());
		mBenchmarkGenerator.reportTraceHistogramMaximum(traceHistogramLoop.getMax());

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Counterexample stem histogram " + traceHistogramStem);
			mLogger.info("Counterexample loop histogram " + traceHistogramLoop);
		}
		assert mCounterexample.getLoop().getLength() > 1;

		return false;
	}

	/**
	 * We construct the module with the same algorithm that we use in our safety analysis (there the Floyd-Hoare
	 * automata also have a single accepting state that is labeled with "false" and that has a self-loop for every
	 * letter). "Coincidentally" is holds that for these kind of automata the powerset-based complementation of finite
	 * automata is also sound for Büchi automata, hence we use a difference operation that is based on this rather
	 * inexpensive complementation algorithm.
	 */
	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> refineFinite(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataOperationCanceledException {
		final PowersetDeterminizer<L, IPredicate> psd =
				new PowersetDeterminizer<>(interpolantAutomaton, true, mDefaultStateFactory);
		try {
			if (abstraction instanceof IGeneralizedNestedWordAutomaton) {
				final GeneralizedDifference<L, IPredicate> gbaDiff = new GeneralizedDifference<>(
						new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
						(IGeneralizedNestedWordAutomaton<L, IPredicate>) abstraction, interpolantAutomaton, psd);
				return gbaDiff.getResult();
			}
			final Difference<L, IPredicate> diff = new Difference<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement, abstraction, interpolantAutomaton, psd, true);
			return diff.getResult();
		} catch (final AutomataLibraryException e) {
			throw new AssertionError("Implement support for handling timeouts");
		}
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> reduceAbstractionSize(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final Minimization automataMinimization) throws AutomataOperationCanceledException {
		if (abstraction instanceof IGeneralizedNestedWordAutomaton) {
			// GBA does not have minimization support yet.
			return abstraction;
		}
		if (automataMinimization == Minimization.NWA_OVERAPPROXIMATION) {
			throw new UnsupportedOperationException("Setting currently not supported");
		}

		INestedWordAutomaton<L, IPredicate> result;
		mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.NON_LIVE_STATE_REMOVAL);
		try {
			result = new RemoveNonLiveStates<>(new AutomataLibraryServices(mServices), abstraction).getResult();
		} finally {
			mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.NON_LIVE_STATE_REMOVAL);
		}
		mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.BUCHI_CLOSURE);
		try {
			result = new BuchiClosureNwa<>(new AutomataLibraryServices(mServices), result);
		} finally {
			mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.BUCHI_CLOSURE);
		}
		try {
			final boolean isDeterministic =
					new IsDeterministic<>(new AutomataLibraryServices(mServices), result).getResult();
			if (isDeterministic) {
				mBenchmarkGenerator.reportMinimizationOfDetAutom();
			} else {
				mBenchmarkGenerator.reportMinimizationOfNondetAutom();
			}
			mLogger.info("Abstraction has " + result.sizeInformation());

			if (result.size() > 0) {
				AutomataMinimization<Set<IcfgLocation>, IPredicate, L> am;
				try {
					am = new AutomataMinimization<>(mServices, result, automataMinimization, false, mIteration,
							mStateFactoryForRefinement, -1, null, null, -1, mPredicateFactoryResultChecking,
							PredicateUtils::getLocations, false);
				} catch (final AutomataMinimizationTimeout e) {
					mBenchmarkGenerator.addAutomataMinimizationData(e.getStatistics());
					throw e.getAutomataOperationCanceledException();
				}
				mBenchmarkGenerator.addAutomataMinimizationData(am.getStatistics());
				if (am.newAutomatonWasBuilt()) {
					result = am.getMinimizedAutomaton();
				}
			}
		} catch (final AutomataOperationCanceledException e) {
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
					"minimizing (" + automataMinimization + ") automaton with " + result.size() + " states");
			throw new ToolchainCanceledException(e, rti);
		}
		mLogger.info("Abstraction has " + result.sizeInformation());
		return result;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> refineBuchi(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException {
		return mRefineBuchi.refineBuchi(abstraction, interpolantAutomaton, mIsSemiDeterministic, mBenchmarkGenerator,
				mComplementationConstruction);
	}
}
