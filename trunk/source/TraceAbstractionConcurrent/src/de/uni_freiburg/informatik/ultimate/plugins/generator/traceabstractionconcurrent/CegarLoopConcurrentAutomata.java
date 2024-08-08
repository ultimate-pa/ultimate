/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaFloydHoareValidityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class CegarLoopConcurrentAutomata<L extends IIcfgTransition<?>> extends NwaCegarLoop<L> {

	public CegarLoopConcurrentAutomata(final DebugIdentifier name, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final IUltimateServiceProvider services,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, createInitialAbstraction(services, csToolkit, predicateFactory, taPrefs, rootNode), rootNode,
				csToolkit, predicateFactory, taPrefs, errorLocs, null, services, transitionClazz,
				stateFactoryForRefinement);
	}

	private static <L extends IIcfgTransition<?>> INestedWordAutomaton<L, IPredicate> createInitialAbstraction(
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences pref, final IIcfg<?> icfg) {
		final IEmptyStackStateFactory<IPredicate> predicateFactoryForItp = new PredicateFactoryForInterpolantAutomata(
				csToolkit.getManagedScript(), predicateFactory, pref.getHoareSettings().computeHoareAnnotation());
		final Cfg2Nwa<L> cFG2NestedWordAutomaton = new Cfg2Nwa<>(icfg, predicateFactoryForItp, csToolkit,
				predicateFactory, services, pref.getXnfConversionTechnique(), pref.getSimplificationTechnique());
		return cFG2NestedWordAutomaton.getResult();
	}

	private static <E> Set<E> asHashSet(final E[] array) {
		return new HashSet<>(Arrays.asList(array));
	}

	@Override
	protected void minimizeAbstraction(final PredicateFactoryRefinement predicateFactoryRefinement,
			final PredicateFactoryResultChecking resultCheckPredFac, final Minimization minimization)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {
		final Function<IMLPredicate, Set<IcfgLocation>> lcsProvider = x -> asHashSet(x.getProgramPoints());
		AutomataMinimization<Set<IcfgLocation>, IMLPredicate, L> am;
		try {
			final boolean computeOld2New = mProofUpdater != null;
			am = new AutomataMinimization<>(getServices(), mAbstraction, minimization, computeOld2New, getIteration(),
					predicateFactoryRefinement, MINIMIZE_EVERY_KTH_ITERATION, mStoredRawInterpolantAutomata,
					mInterpolAutomaton, MINIMIZATION_TIMEOUT, resultCheckPredFac, lcsProvider, false);
		} catch (final AutomataMinimizationTimeout e) {
			mCegarLoopBenchmark.addAutomataMinimizationData(e.getStatistics());
			throw e.getAutomataOperationCanceledException();
		}
		mCegarLoopBenchmark.addAutomataMinimizationData(am.getStatistics());

		final boolean newAutomatonWasBuilt = am.newAutomatonWasBuilt();

		if (newAutomatonWasBuilt) {
			// postprocessing after minimization
			final IDoubleDeckerAutomaton<L, IPredicate> newAbstraction = am.getMinimizedAutomaton();

			// update proof
			if (mProofUpdater != null) {
				final Map<IPredicate, IPredicate> oldState2newState = am.getOldState2newStateMapping();
				if (oldState2newState == null) {
					throw new AssertionError("Hoare annotation and " + minimization + " incompatible");
				}
				mProofUpdater.updateOnMinimization(oldState2newState, newAbstraction);
			}

			// statistics
			final int oldSize = mAbstraction.size();
			final int newSize = newAbstraction.size();
			assert oldSize == 0 || oldSize >= newSize : "Minimization increased state space";

			// use result
			mAbstraction = newAbstraction;
		}
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(getIteration());
		// howDifferentAreInterpolants(mInterpolAutomaton.getStates());

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final boolean exploitSigmaStarConcatOfIA = mProofUpdater == null || mProofUpdater.exploitSigmaStarConcatOfIa();

		final INestedWordAutomaton<L, IPredicate> oldAbstraction = mAbstraction;
		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();
		final IHoareTripleChecker htc;
		if (mRefinementResult.getHoareTripleChecker() != null) {
			htc = mRefinementResult.getHoareTripleChecker();
		} else {
			htc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(getServices(),
					mPref.getHoareTripleChecks(), mCsToolkit, predicateUnifier);
		}
		mLogger.debug("Start constructing difference");
		// assert (oldAbstraction.getStateFactory() == mInterpolAutomaton.getStateFactory());

		IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;

		final DeterministicInterpolantAutomaton<L> determinized = new DeterministicInterpolantAutomaton<>(getServices(),
				mCsToolkit, htc, mInterpolAutomaton, predicateUnifier, false, false);
		// ComplementDeterministicNwa<LETTER, IPredicate>
		// cdnwa = new ComplementDeterministicNwa<>(dia);
		final PowersetDeterminizer<L, IPredicate> psd2 =
				new PowersetDeterminizer<>(determinized, false, mPredicateFactoryInterpolantAutomata);

		if (mPref.differenceSenwa()) {
			diff = new DifferenceSenwa<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
					oldAbstraction, determinized, psd2, false);
		} else {
			diff = new Difference<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
					oldAbstraction, determinized, psd2, exploitSigmaStarConcatOfIA);
		}
		determinized.switchToReadonlyMode();
		assert !mCsToolkit.getManagedScript().isLocked();
		assert NwaFloydHoareValidityCheck.forInterpolantAutomaton(mServices, mCsToolkit.getManagedScript(),
				new IncrementalHoareTripleChecker(mCsToolkit, false), mRefinementResult.getPredicateUnifier(),
				mInterpolAutomaton, true).getResult();
		// do the following check only to obtain logger messages of
		// checkInductivity

		if (REMOVE_DEAD_ENDS) {
			if (mProofUpdater != null) {
				final Difference<L, IPredicate> difference = (Difference<L, IPredicate>) diff;
				mProofUpdater.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
			}
			diff.removeDeadEnds();
			if (mProofUpdater != null) {
				mProofUpdater.addDeadEndDoubleDeckers(diff);
			}
		}

		mAbstraction = diff.getResult();
		// mDeadEndRemovalTime = diff.getDeadEndRemovalTime();
		if (mPref.dumpAutomata()) {
			final String filename = "InterpolantAutomaton_Iteration" + getIteration();
			super.writeAutomatonToFile(mInterpolAutomaton, filename);
		}

		mCegarLoopBenchmark.addEdgeCheckerData(htc.getStatistics());
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		final Minimization minimization = mPref.getMinimization();
		switch (minimization) {
		case NONE:
			break;
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			minimizeAbstraction(mStateFactoryForRefinement, mPredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}

		final boolean stillAccepted = new Accepts<>(new AutomataLibraryServices(getServices()),
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction,
				(NestedWord<L>) mCounterexample.getWord()).getResult();
		return !stillAccepted;
	}
}
