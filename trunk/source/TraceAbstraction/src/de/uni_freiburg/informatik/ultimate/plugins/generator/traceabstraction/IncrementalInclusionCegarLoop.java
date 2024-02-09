/*
 * Copyright (C) 2015 Jeffery Hsu (a71128@gmail.com)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.AbstractIncrementalInclusionCheck;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.InclusionViaDifference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck2DeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck2DeadEndRemovalAdvanceCover;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck3;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck3_2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck4;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck4_2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck5;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IncrementalInclusionCheck5_2;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;

public class IncrementalInclusionCegarLoop<L extends IIcfgTransition<?>> extends NwaCegarLoop<L> {

	protected AbstractIncrementalInclusionCheck<L, IPredicate> mInclusionCheck;
	protected final LanguageOperation mLanguageOperation;
	protected final List<AbstractInterpolantAutomaton<L>> mInterpolantAutomata = new ArrayList<>();
	protected final List<IHoareTripleChecker> mHoareTripleChecker = new ArrayList<>();

	public IncrementalInclusionCegarLoop(final DebugIdentifier name,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final NwaHoareProofProducer<L> proofProducer,
			final IUltimateServiceProvider services, final LanguageOperation languageOperation,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);
		mLanguageOperation = languageOperation;

		if (mProofUpdater != null) {
			throw new UnsupportedOperationException(
					"while using this CEGAR loop computation of proofs is unsupported ");
		}
	}

	@Override
	protected void initialize() throws AutomataLibraryException {
		super.initialize();
		switch (mLanguageOperation) {
		case DIFFERENCE:
			throw new AssertionError("wrong cegar loop for this");
		case INCREMENTAL_INCLUSION_VIA_DIFFERENCE: {
			mInclusionCheck = new InclusionViaDifference<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mPredicateFactoryInterpolantAutomata, mAbstraction);
		}
			break;
		case INCREMENTAL_INCLUSION_2: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemoval<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover<>(
					new AutomataLibraryServices(getServices()), mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks<>(
					new AutomataLibraryServices(getServices()), mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS_MULTIPLECE: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck =
					new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce<>(
							new AutomataLibraryServices(getServices()), mStateFactoryForRefinement, mAbstraction,
							empty);
		}
			break;
		case INCREMENTAL_INCLUSION_3: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck3<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_3_2: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck3_2<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_4: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck4<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_4_2: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck4_2<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_5: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck5<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_5_2: {
			final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck5_2<>(new AutomataLibraryServices(getServices()),
					mStateFactoryForRefinement, mAbstraction, empty);
		}
			break;
		default:
			throw new AssertionError("unknown case");
		}
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		super.mCounterexample = mInclusionCheck.getCounterexample();
		// try {
		// mCounterexample = emptyWithAI.getNestedRun();
		// } else {
		// mCounterexample = (new IsEmpty<LETTER, IPredicate>((INestedWordAutomatonOldApi) mAbstraction))
		// .getNestedRun();
		// }
		// } catch (OperationCanceledException e) {
		// // TODO Auto-generated catch block
		// e.printStackTrace();
		// }
		if (super.mCounterexample == null) {
			return true;
		}
		mLogger.info("Found potential Counterexample");
		return false;
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(getIteration());
		// howDifferentAreInterpolants(mInterpolAutomaton.getStates());

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();
		final IHoareTripleChecker htc;
		if (mRefinementResult.getHoareTripleChecker() != null) {
			htc = mRefinementResult.getHoareTripleChecker();
		} else {
			htc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(getServices(),
					HoareTripleChecks.MONOLITHIC, mCsToolkit, predicateUnifier);
		}

		boolean progress;
		try {
			mLogger.debug("Start constructing difference");
			// assert(oldAbstraction.getStateFactory() ==
			// mInterpolAutomaton.getStateFactory());

			switch (mPref.interpolantAutomatonEnhancement()) {
			case PREDICATE_ABSTRACTION:
			case PREDICATE_ABSTRACTION_CONSERVATIVE:
			case PREDICATE_ABSTRACTION_CANNIBALIZE: {
				final boolean conservativeSuccessorCandidateSelection = mPref
						.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE;
				final boolean cannibalize = mPref
						.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE;
				final DeterministicInterpolantAutomaton<L> determinized =
						new DeterministicInterpolantAutomaton<>(getServices(), mCsToolkit, htc, mInterpolAutomaton,
								predicateUnifier, conservativeSuccessorCandidateSelection, cannibalize);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				mInclusionCheck.addSubtrahend(determinized);
				mInterpolantAutomata.add(determinized);
				mHoareTripleChecker.add(htc);
				switchAllInterpolantAutomataToReadOnlyMode();
				final INestedWordAutomaton<L, IPredicate> test =
						new RemoveUnreachable<>(new AutomataLibraryServices(getServices()), determinized).getResult();
				assert checkInterpolantAutomatonInductivity(test);

				progress = true;
				break;
			}
			case EAGER:
			case NO_SECOND_CHANCE:
			case EAGER_CONSERVATIVE: {
				final boolean conservativeSuccessorCandidateSelection =
						mPref.interpolantAutomatonEnhancement() == mPref.interpolantAutomatonEnhancement();
				final boolean secondChance =
						mPref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE;
				final NondeterministicInterpolantAutomaton<L> nondet =
						new NondeterministicInterpolantAutomaton<>(getServices(), mCsToolkit, htc, mInterpolAutomaton,
								predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				mInclusionCheck.addSubtrahend(nondet);
				mInterpolantAutomata.add(nondet);
				mHoareTripleChecker.add(htc);
				switchAllInterpolantAutomataToReadOnlyMode();
				final INestedWordAutomaton<L, IPredicate> test =
						new RemoveUnreachable<>(new AutomataLibraryServices(getServices()), nondet).getResult();
				assert checkInterpolantAutomatonInductivity(test);
				progress = true;
				break;
			}
			case NONE:
				mInclusionCheck.addSubtrahend(mInterpolAutomaton);
				final boolean acceptedByIA = new Accepts<>(new AutomataLibraryServices(getServices()),
						mInterpolAutomaton, (NestedWord<L>) mCounterexample.getWord()).getResult();
				progress = acceptedByIA;
				break;
			default:
				throw new UnsupportedOperationException();
			}
			if (mPref.dumpAutomata()) {
				for (int i = 0; i < mInterpolantAutomata.size(); i++) {
					final String filename =
							"IncrementalInclusion_Interation" + getIteration() + "_InterpolantAutomaton" + i;
					super.writeAutomatonToFile(mInterpolantAutomata.get(i), filename);
				}
			}
		} finally {
			// mCegarLoopBenchmark.addEdgeCheckerData(edgeChecker.getEdgeCheckerBenchmark());
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		}
		return progress;
	}

	private void switchAllInterpolantAutomataToOnTheFlyConstructionMode() {
		for (final AbstractInterpolantAutomaton<L> ia : mInterpolantAutomata) {
			ia.switchToOnDemandConstructionMode();
		}
	}

	private void switchAllInterpolantAutomataToReadOnlyMode() {
		for (final AbstractInterpolantAutomaton<L> ia : mInterpolantAutomata) {
			ia.switchToReadonlyMode();
		}
		if (mPref.dumpAutomata()) {
			for (int i = 0; i < mInterpolantAutomata.size(); i++) {
				final String filename =
						"EnhancedInterpolantAutomaton_WhoseConstructionWasStartedIn_Iteration" + getIteration();
				super.writeAutomatonToFile(mInterpolantAutomata.get(i), filename);
				mInterpolantAutomata.get(i);
			}
		}
	}

	@Override
	public void finish() {
		assert mHoareTripleChecker.size() == mInterpolantAutomata.size();
		for (final IHoareTripleChecker htc : mHoareTripleChecker) {
			mCegarLoopBenchmark.addEdgeCheckerData(htc.getStatistics());
		}

	}

}
