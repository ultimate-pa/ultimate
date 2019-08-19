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
import java.util.Collection;
import java.util.Collections;
import java.util.List;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;

public class IncrementalInclusionCegarLoop<LETTER extends IIcfgTransition<?>> extends BasicCegarLoop<LETTER> {

	protected AbstractIncrementalInclusionCheck<LETTER, IPredicate> mInclusionCheck;
	protected final LanguageOperation mLanguageOperation;
	protected final List<AbstractInterpolantAutomaton<LETTER>> mInterpolantAutomata = new ArrayList<>();
	protected final List<IHoareTripleChecker> mHoareTripleChecker = new ArrayList<>();

	public IncrementalInclusionCegarLoop(final DebugIdentifier name, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final LanguageOperation languageOperation) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation,
				services);
		mLanguageOperation = languageOperation;
		if (mComputeHoareAnnotation) {
			throw new UnsupportedOperationException(
					"while using this CEGAR loop computation of Hoare annotation is unsupported ");
		}
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();
		switch (mLanguageOperation) {
		case DIFFERENCE:
			throw new AssertionError("wrong cegar loop for this");
		case INCREMENTAL_INCLUSION_VIA_DIFFERENCE: {
			mInclusionCheck = new InclusionViaDifference<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement, mPredicateFactoryInterpolantAutomata,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction);
		}
			break;
		case INCREMENTAL_INCLUSION_2: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck =
					new IncrementalInclusionCheck2<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
							(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemoval<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover<>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks<>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS_MULTIPLECE: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck =
					new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce<>(
							new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
							(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_3: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck =
					new IncrementalInclusionCheck3<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
							(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_3_2: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck3_2<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_4: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck =
					new IncrementalInclusionCheck4<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
							(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_4_2: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck4_2<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_5: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck =
					new IncrementalInclusionCheck5<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
							(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
		}
			break;
		case INCREMENTAL_INCLUSION_5_2: {
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck5_2<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, empty);
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
		mStateFactoryForRefinement.setIteration(super.mIteration);
		// howDifferentAreInterpolants(mInterpolAutomaton.getStates());

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		final IHoareTripleChecker edgeChecker = TraceAbstractionUtils.constructEfficientHoareTripleChecker(mServices,
				HoareTripleChecks.MONOLITHIC, mCsToolkit, mTraceCheckAndRefinementEngine.getPredicateUnifier());

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
				final DeterministicInterpolantAutomaton<LETTER> determinized =
						new DeterministicInterpolantAutomaton<>(mServices, mCsToolkit, edgeChecker, mInterpolAutomaton,
								mTraceCheckAndRefinementEngine.getPredicateUnifier(),
								conservativeSuccessorCandidateSelection, cannibalize);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				mInclusionCheck.addSubtrahend(determinized);
				mInterpolantAutomata.add(determinized);
				mHoareTripleChecker.add(edgeChecker);
				switchAllInterpolantAutomataToReadOnlyMode();
				final INestedWordAutomaton<LETTER, IPredicate> test =
						new RemoveUnreachable<>(new AutomataLibraryServices(mServices), determinized).getResult();
				assert new InductivityCheck<>(mServices, test, false, true,
						new IncrementalHoareTripleChecker(mIcfg.getCfgSmtToolkit(), false)).getResult();
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
				final NondeterministicInterpolantAutomaton<LETTER> nondet =
						new NondeterministicInterpolantAutomaton<>(mServices, mCsToolkit, edgeChecker,
								mInterpolAutomaton, mTraceCheckAndRefinementEngine.getPredicateUnifier(),
								conservativeSuccessorCandidateSelection, secondChance);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				mInclusionCheck.addSubtrahend(nondet);
				mInterpolantAutomata.add(nondet);
				mHoareTripleChecker.add(edgeChecker);
				switchAllInterpolantAutomataToReadOnlyMode();
				final INestedWordAutomaton<LETTER, IPredicate> test =
						new RemoveUnreachable<>(new AutomataLibraryServices(mServices), nondet).getResult();
				assert new InductivityCheck<>(mServices, test, false, true,
						new IncrementalHoareTripleChecker(mIcfg.getCfgSmtToolkit(), false)).getResult();
				progress = true;
				break;
			}
			case NONE:
				mInclusionCheck.addSubtrahend(mInterpolAutomaton);
				final boolean acceptedByIA = new Accepts<>(new AutomataLibraryServices(mServices), mInterpolAutomaton,
						(NestedWord<LETTER>) mCounterexample.getWord()).getResult();
				progress = acceptedByIA;
				break;
			default:
				throw new UnsupportedOperationException();
			}
			if (mPref.dumpAutomata()) {
				for (int i = 0; i < mInterpolantAutomata.size(); i++) {
					final String filename =
							"IncrementalInclusion_Interation" + mIteration + "_InterpolantAutomaton" + i;
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
		for (final AbstractInterpolantAutomaton<LETTER> ia : mInterpolantAutomata) {
			ia.switchToOnDemandConstructionMode();
		}
	}

	private void switchAllInterpolantAutomataToReadOnlyMode() {
		for (final AbstractInterpolantAutomaton<LETTER> ia : mInterpolantAutomata) {
			ia.switchToReadonlyMode();
		}
		if (mPref.dumpAutomata()) {
			for (int i = 0; i < mInterpolantAutomata.size(); i++) {
				final String filename =
						"EnhancedInterpolantAutomaton_WhoseConstructionWasStartedIn_Iteration" + mIteration;
				super.writeAutomatonToFile(mInterpolantAutomata.get(i), filename);
				mInterpolantAutomata.get(i);
			}
		}
	}

	@Override
	public void finish() {
		assert mHoareTripleChecker.size() == mInterpolantAutomata.size();
		for (final IHoareTripleChecker htc : mHoareTripleChecker) {
			mCegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
		}

	}

}
