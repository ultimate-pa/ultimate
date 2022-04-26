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

import java.util.List;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStyle;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TraceCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RefineBuchi;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiComplementationConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.NcsbImplementation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class BuchiAutomatonCegarLoop<L extends IIcfgTransition<?>>
		extends AbstractBuchiCegarLoop<L, INestedWordAutomaton<L, IPredicate>> {

	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final PredicateFactoryResultChecking mPredicateFactoryResultChecking;
	private final RefineBuchi<L> mRefineBuchi;
	private final List<BuchiInterpolantAutomatonConstructionStyle> mBiaConstructionStyleSequence;
	private final BuchiComplementationConstruction mComplementationConstruction;

	public BuchiAutomatonCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction,
			final PredicateFactoryRefinement stateFactoryForRefinement,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		super(icfg, rankVarConstructor, predicateFactory, taPrefs, services, transitionClazz, initialAbstraction,
				benchmarkGenerator);
		mPredicateFactoryResultChecking = new PredicateFactoryResultChecking(predicateFactory);
		mStateFactoryForRefinement = stateFactoryForRefinement;
		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final NcsbImplementation ncsbImplemntation =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_NCSB_IMPLEMENTATION, NcsbImplementation.class);
		final boolean useDoubleDeckers =
				!baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_IGNORE_DOWN_STATES);
		final boolean difference =
				baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_DETERMINIZATION_ON_DEMAND);
		mRefineBuchi = new RefineBuchi<>(mIcfg, mCsToolkitWithRankVars, predicateFactory, mPref.dumpAutomata(),
				difference, mDefaultStateFactory, mStateFactoryForRefinement, useDoubleDeckers, mPref.dumpPath(),
				mPref.getAutomataFormat(), mInterpolation, mServices, mLogger, SIMPLIFICATION_TECHNIQUE,
				XNF_CONVERSION_TEQCHNIQUE, ncsbImplemntation);
		final BuchiInterpolantAutomatonConstructionStrategy biaConstructionStrategy =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BIA_CONSTRUCTION_STRATEGY,
						BuchiInterpolantAutomatonConstructionStrategy.class);
		mBiaConstructionStyleSequence = biaConstructionStrategy.getBiaConstrucionStyleSequence(baPref);
		mComplementationConstruction =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BUCHI_COMPLEMENTATION_CONSTRUCTION,
						BuchiComplementationConstruction.class);
	}

	@Override
	protected void reduceAbstractionSize(final Minimization automataMinimization)
			throws AutomataOperationCanceledException {
		if (mAbstraction instanceof IGeneralizedNestedWordAutomaton) {
			// GBA does not have minimization support yet.
			return;
		}

		mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.NON_LIVE_STATE_REMOVAL);
		try {
			mAbstraction = new RemoveNonLiveStates<>(new AutomataLibraryServices(mServices), mAbstraction).getResult();
		} finally {
			mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.NON_LIVE_STATE_REMOVAL);
		}
		mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.BUCHI_CLOSURE);
		try {
			mAbstraction = new BuchiClosureNwa<>(new AutomataLibraryServices(mServices), mAbstraction);
		} finally {
			mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.BUCHI_CLOSURE);
		}
		try {
			final boolean isDeterministic =
					new IsDeterministic<>(new AutomataLibraryServices(mServices), mAbstraction).getResult();
			if (isDeterministic) {
				mBenchmarkGenerator.reportMinimizationOfDetAutom();
			} else {
				mBenchmarkGenerator.reportMinimizationOfNondetAutom();
			}
			mLogger.info("Abstraction has " + mAbstraction.sizeInformation());

			if (mAbstraction.size() > 0) {
				final Function<ISLPredicate, IcfgLocation> locProvider = ISLPredicate::getProgramPoint;
				AutomataMinimization<IcfgLocation, ISLPredicate, L> am;
				try {
					am = new AutomataMinimization<>(mServices, mAbstraction, automataMinimization, false, mIteration,
							mStateFactoryForRefinement, -1, null, mInterpolAutomaton, -1,
							mPredicateFactoryResultChecking, locProvider, false);
				} catch (final AutomataMinimizationTimeout e) {
					mBenchmarkGenerator.addAutomataMinimizationData(e.getStatistics());
					throw e.getAutomataOperationCanceledException();
				}
				mBenchmarkGenerator.addAutomataMinimizationData(am.getStatistics());
				if (am.newAutomatonWasBuilt()) {
					mAbstraction = am.getMinimizedAutomaton();
				}
			}
		} catch (final AutomataOperationCanceledException e) {
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
					"minimizing (" + automataMinimization + ") automaton with " + mAbstraction.size() + " states");
			throw new ToolchainCanceledException(e, rti);
		}
		mLogger.info("Abstraction has " + mAbstraction.sizeInformation());
	}

	@Override
	protected void refineBuchi(final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException {
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		int stage = 0;

		/*
		 * Iterate through a sequence of BuchiInterpolantAutomatonConstructionStyles Each construction style defines how
		 * an interpolant automaton is constructed. Constructions that provide simpler (less nondeterministic) automata
		 * should come first. In each iteration we compute the difference which causes an on-demand construciton of the
		 * automaton and evaluate the automaton afterwards. If the automaton is "good" we keep the difference and
		 * continued with the termination analysis. If the automaton is "bad" we construct the next automaton. Currently
		 * an automaton is "good" iff the counterexample of the current CEGAR iteration is accepted by the automaton
		 * (otherwise the counterexample would not be excluded and we might get it again in the next iteration of the
		 * CEGAR loop).
		 *
		 */
		for (final BuchiInterpolantAutomatonConstructionStyle constructionStyle : mBiaConstructionStyleSequence) {
			assert automatonUsesISLPredicates(mAbstraction) : "used wrong StateFactory";
			INestedWordAutomaton<L, IPredicate> newAbstraction = null;
			try {
				newAbstraction = mRefineBuchi.refineBuchi(mAbstraction, mCounterexample, mIteration, constructionStyle,
						lassoCheck.getBinaryStatePredicateManager(), mCsToolkitWithRankVars.getModifiableGlobalsTable(),
						mInterpolation, mBenchmarkGenerator, mComplementationConstruction);
			} catch (final AutomataOperationCanceledException e) {
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), "applying stage " + stage);
				throw new ToolchainCanceledException(e, rti);
			} catch (final ToolchainCanceledException e) {
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				throw e;
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e.getMessage());
			}

			if (newAbstraction != null) {
				mAbstraction = newAbstraction;
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportBuchiModule(mIteration,
							mRefineBuchi.getInterpolAutomatonUsedInRefinement());
				}
				mBenchmarkGenerator.announceSuccessfullRefinementStage(stage);
				switch (constructionStyle.getInterpolantAutomaton()) {
				case Deterministic:
				case LassoAutomaton:
					mMDBenchmark.reportDeterminsticModule(mIteration,
							mRefineBuchi.getInterpolAutomatonUsedInRefinement().size());
					break;
				case ScroogeNondeterminism:
				case EagerNondeterminism:
					mMDBenchmark.reportNonDeterminsticModule(mIteration,
							mRefineBuchi.getInterpolAutomatonUsedInRefinement().size());
					break;
				default:
					throw new AssertionError("unsupported");
				}
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				mBenchmarkGenerator.addBackwardCoveringInformationBuchi(mRefineBuchi.getBci());
				return;
			}
			stage++;
		}
		throw new AssertionError("no settings was sufficient");
	}

	private boolean automatonUsesISLPredicates(final INestedWordAutomaton<L, IPredicate> nwa) {
		final Set<IPredicate> states = nwa.getStates();
		if (states.isEmpty()) {
			return true;
		}
		final IPredicate someState = states.iterator().next();
		return someState instanceof ISLPredicate;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataLibraryException {
		final String counterName = mIcfg.getIdentifier() + "_" + getClass().getName() + "Abstraction";
		final UtilFixedCounterexample<L, IPredicate> utilFixedCe = new UtilFixedCounterexample<>();
		final NestedLassoRun<L, IPredicate> counterexample = utilFixedCe
				.getNestedLassoRun(new AutomataLibraryServices(mServices), mAbstraction, counterName, mIteration);
		if (counterexample != null) {
			mCounterexample = counterexample;
		} else {
			if (mAbstraction instanceof IGeneralizedNestedWordAutomaton) {
				final IGeneralizedNestedWordAutomaton<L, IPredicate> abstraction =
						(IGeneralizedNestedWordAutomaton<L, IPredicate>) mAbstraction;
				final GeneralizedBuchiIsEmpty<L, IPredicate> ec =
						new GeneralizedBuchiIsEmpty<>(new AutomataLibraryServices(mServices), abstraction);
				if (ec.getResult()) {
					return true;
				}
				mCounterexample = ec.getAcceptingNestedLassoRun();
			} else {
				final BuchiIsEmpty<L, IPredicate> ec =
						new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), mAbstraction);
				if (ec.getResult()) {
					return true;
				}
				mCounterexample = ec.getAcceptingNestedLassoRun();
			}
			utilFixedCe.writeNestedLassoRun(mAbstraction, mCounterexample, counterName, mIteration);
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

	@Override
	protected void refineFinite(final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException {
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> traceCheck;
		final LassoCheck<L>.LassoCheckResult lcr = lassoCheck.getLassoCheckResult();
		if (lassoCheck.getLassoCheckResult().getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
			// if both (stem and loop) are infeasible we take the smaller one.
			final int stemSize = mCounterexample.getStem().getLength();
			final int loopSize = mCounterexample.getLoop().getLength();
			if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE && loopSize <= stemSize) {
				traceCheck = lassoCheck.getLoopCheck();
			} else {
				traceCheck = lassoCheck.getStemCheck();
			}
		} else if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
			traceCheck = lassoCheck.getLoopCheck();
		} else {
			assert lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE;
			traceCheck = lassoCheck.getConcatCheck();
		}

		mInterpolAutomaton = traceCheck.getInfeasibilityProof();

		final IHoareTripleChecker htc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(
				mServices, HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, traceCheck.getPredicateUnifier());

		final DeterministicInterpolantAutomaton<L> determinized = new DeterministicInterpolantAutomaton<>(mServices,
				mCsToolkitWithRankVars, htc, mInterpolAutomaton, traceCheck.getPredicateUnifier(), false, false);
		final PowersetDeterminizer<L, IPredicate> psd =
				new PowersetDeterminizer<>(determinized, true, mDefaultStateFactory);
		Difference<L, IPredicate> diff = null;
		GeneralizedDifference<L, IPredicate> gbaDiff = null;
		try {
			IGeneralizedNwaOutgoingLetterAndTransitionProvider<L, IPredicate> gbaAbstraction;
			if (mAbstraction instanceof IGeneralizedNestedWordAutomaton) {
				gbaAbstraction = (IGeneralizedNestedWordAutomaton<L, IPredicate>) mAbstraction;
				gbaDiff = new GeneralizedDifference<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, gbaAbstraction, determinized, psd);
			} else {
				diff = new Difference<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
						mAbstraction, determinized, psd, true);
			}
		} catch (final AutomataOperationCanceledException e) {
			mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			throw e;
		} catch (final AutomataLibraryException e) {
			throw new AssertionError();
		} catch (final ToolchainCanceledException e) {
			mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			throw e;
		}
		determinized.switchToReadonlyMode();
		if (mPref.dumpAutomata()) {
			final String filename =
					mIcfg.getIdentifier() + "_" + "interpolAutomatonUsedInRefinement" + mIteration + "after";
			BuchiAutomizerUtils.writeAutomatonToFile(mServices, mInterpolAutomaton, mPref.dumpPath(), filename,
					mPref.getAutomataFormat(), "");
		}
		if (mConstructTermcompProof) {
			mTermcompProofBenchmark.reportFiniteModule(mIteration, mInterpolAutomaton);
		}
		mMDBenchmark.reportTrivialModule(mIteration, mInterpolAutomaton.size());
		assert new InductivityCheck<>(mServices, mInterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(mCsToolkitWithRankVars, false)).getResult();
		if (gbaDiff == null) {
			mAbstraction = diff.getResult();
		} else {
			mAbstraction = gbaDiff.getResult();
		}
		assert automatonUsesISLPredicates(mAbstraction) : "used wrong StateFactory";
		mBenchmarkGenerator.addEdgeCheckerData(htc.getStatistics());
		mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
	}
}