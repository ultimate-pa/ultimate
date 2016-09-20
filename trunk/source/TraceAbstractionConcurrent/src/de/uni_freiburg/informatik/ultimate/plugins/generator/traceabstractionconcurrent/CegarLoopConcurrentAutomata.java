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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class CegarLoopConcurrentAutomata extends BasicCegarLoop {

	public CegarLoopConcurrentAutomata(final String name, final RootNode rootNode, final SmtManager smtManager,
			final TraceAbstractionBenchmarks timingStatistics, final TAPreferences taPrefs, final Collection<ProgramPoint> errorLocs,
			final IUltimateServiceProvider services, final IToolchainStorage storage) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, InterpolationTechnique.Craig_TreeInterpolation, false, services, storage);
		// mContentFactory = new TaConcurContentFactory(
		// rootNode.getRootAnnot().getLocNodes(),
		// this,
		// super.mSmtManager.getTheory(),
		// super.mHoareAnnotation,
		// false);
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
		final StraightLineInterpolantAutomatonBuilder iab = new StraightLineInterpolantAutomatonBuilder(
				mServices, new InCaReAlphabet<>(mAbstraction), mInterpolantGenerator, mPredicateFactoryInterpolantAutomata);
		mInterpolAutomaton = iab.getResult();
		mLogger.info("Interpolatants " + mInterpolAutomaton.getStates());

		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
		assert (accepts(mServices, mInterpolAutomaton, mCounterexample.getWord())) : "Interpolant automaton broken!";
		assert (new InductivityCheck(mServices, mInterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(mRootNode.getRootAnnot().getManagedScript(), mModGlobVarManager))).getResult() : "Not inductive";
	}

	@Override
	protected void getInitialAbstraction() {
		final IStateFactory<IPredicate> predicateFactory = new PredicateFactoryForInterpolantAutomata(super.mSmtManager, mPref.computeHoareAnnotation());
		final CFG2Automaton cFG2NestedWordAutomaton = new Cfg2Nwa(mRootNode, predicateFactory, mSmtManager, mServices, mXnfConversionTechnique, mSimplificationTechnique);
		mAbstraction = (INestedWordAutomatonSimple<CodeBlock, IPredicate>) cFG2NestedWordAutomaton.getResult();

		if (mIteration <= mPref.watchIteration()
				&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
			mArtifactAutomaton = mAbstraction;
		}
	}

	@Override
	protected Collection<Set<IPredicate>> computePartition(final INestedWordAutomaton<CodeBlock, IPredicate> automaton) {
		mLogger.info("Start computation of initial partition.");
		final Collection<IPredicate> states = automaton.getStates();
		final Map<Set<ProgramPoint>, Set<IPredicate>> pp2p = new HashMap<>();
		for (final IPredicate p : states) {
			final IMLPredicate mp = (IMLPredicate) p;
			pigeonHole(pp2p, mp);
		}
		final Collection<Set<IPredicate>> partition = new ArrayList<>();
		for (final Set<ProgramPoint> pps : pp2p.keySet()) {
			final Set<IPredicate> statesWithSamePP = pp2p.get(pps);
			partition.add(statesWithSamePP);
		}
		mLogger.info("Finished computation of initial partition.");
		return partition;
	}

	/**
	 * Pigeon-hole (german: einsortieren) predicates according to their
	 * ProgramPoint
	 */
	protected static void pigeonHole(final Map<Set<ProgramPoint>, Set<IPredicate>> pp2p, final IMLPredicate mp) {
		Set<IPredicate> statesWithSamePPs = pp2p.get(asHashSet(mp.getProgramPoints()));
		if (statesWithSamePPs == null) {
			statesWithSamePPs = new HashSet<>();
			pp2p.put(asHashSet(mp.getProgramPoints()), statesWithSamePPs);
		}
		statesWithSamePPs.add(mp);
	}

	private static <E> Set<E> asHashSet(final E[] array) {
		return new HashSet<>(Arrays.asList(array));
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(super.mIteration);
		// howDifferentAreInterpolants(mInterpolAutomaton.getStates());

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final boolean explointSigmaStarConcatOfIA = !mComputeHoareAnnotation;

		final PredicateFactoryForInterpolantAutomata predicateFactory = (PredicateFactoryForInterpolantAutomata) mAbstraction.getStateFactory();

		final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction = (INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction;
		final Map<IPredicate, Set<IPredicate>> removedDoubleDeckers = null;
		final Map<IPredicate, IPredicate> context2entry = null;
		final IHoareTripleChecker htc = getEfficientHoareTripleChecker(mServices, mPref.getHoareTripleChecks(),
				mSmtManager, mModGlobVarManager, mInterpolantGenerator.getPredicateUnifier());
		mLogger.debug("Start constructing difference");
//		assert (oldAbstraction.getStateFactory() == mInterpolAutomaton.getStateFactory());

		IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

		final DeterministicInterpolantAutomaton determinized = new DeterministicInterpolantAutomaton(
				mServices, mSmtManager, mModGlobVarManager, htc, oldAbstraction, mInterpolAutomaton,
				mInterpolantGenerator.getPredicateUnifier(), mLogger, false, false);
		// ComplementDeterministicNwa<CodeBlock, IPredicate>
		// cdnwa = new ComplementDeterministicNwa<>(dia);
		final PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<>(
				determinized, false, mPredicateFactoryInterpolantAutomata);

		if (mPref.differenceSenwa()) {
			diff = new DifferenceSenwa<>(new AutomataLibraryServices(mServices), oldAbstraction, (INestedWordAutomaton<CodeBlock, IPredicate>) determinized, psd2, false);
		} else {
			diff = new Difference<>(new AutomataLibraryServices(mServices), oldAbstraction, determinized, psd2,
					mStateFactoryForRefinement, explointSigmaStarConcatOfIA);
		}
		determinized.switchToReadonlyMode();
		assert !mSmtManager.isLocked();
		assert (new InductivityCheck(mServices, mInterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(mRootNode.getRootAnnot().getManagedScript(), mModGlobVarManager))).getResult();
		// do the following check only to obtain logger messages of
		// checkInductivity

		if (REMOVE_DEAD_ENDS) {
			if (mComputeHoareAnnotation) {
				final Difference<CodeBlock, IPredicate> difference = (Difference<CodeBlock, IPredicate>) diff;
				mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
			}
			diff.removeDeadEnds();
			if (mComputeHoareAnnotation) {
				mHaf.addDeadEndDoubleDeckers(diff);
			}
		}

		mAbstraction = diff.getResult();
		// mDeadEndRemovalTime = diff.getDeadEndRemovalTime();
		if (mPref.dumpAutomata()) {
			final String filename = "InterpolantAutomaton_Iteration" + mIteration;
			super.writeAutomatonToFile(mInterpolAutomaton, filename);
		}

		mCegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		final Minimization minimization = mPref.minimize();
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

		final boolean stillAccepted = (new Accepts<>(new AutomataLibraryServices(mServices),
				(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction,
				(NestedWord<CodeBlock>) mCounterexample.getWord())).getResult();
		return !stillAccepted;
	}
}
