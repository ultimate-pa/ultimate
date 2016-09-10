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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;

public class IncrementalInclusionCegarLoop extends BasicCegarLoop {
	
	protected AbstractIncrementalInclusionCheck<CodeBlock, IPredicate> mInclusionCheck;
	protected final LanguageOperation mLanguageOperation;
	protected final List<AbstractInterpolantAutomaton> mInterpolantAutomata = new ArrayList<AbstractInterpolantAutomaton>();
	protected final List<IHoareTripleChecker> mHoareTripleChecker = new ArrayList<IHoareTripleChecker>();

	public IncrementalInclusionCegarLoop(final String name, final RootNode rootNode,
			final SmtManager smtManager, final TAPreferences taPrefs,
			final Collection<ProgramPoint> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final LanguageOperation languageOperation) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, interpolation,
				computeHoareAnnotation, services, storage);
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
			mInclusionCheck = new InclusionViaDifference(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement,
					mPredicateFactoryInterpolantAutomata,
					(INestedWordAutomatonSimple) mAbstraction);
		}
		break;
		case INCREMENTAL_INCLUSION_2: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemoval<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS_MULTIPLECE: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_3: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck3<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_3_2: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck3_2<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_4: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck4<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_4_2: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck4_2<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_5: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck5<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_5_2: {
			final List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			mInclusionCheck = new IncrementalInclusionCheck5_2<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					(INestedWordAutomatonSimple) mAbstraction, empty);
		}
		break;
		default:
			throw new AssertionError("unknown case");
		}
	}




	@Override
	protected boolean isAbstractionCorrect() throws AutomataOperationCanceledException {
		super.mCounterexample = mInclusionCheck.getCounterexample();
//		try {
//				mCounterexample = emptyWithAI.getNestedRun();
//			} else {
//				mCounterexample = (new IsEmpty<CodeBlock, IPredicate>((INestedWordAutomatonOldApi) mAbstraction))
//						.getNestedRun();
//			}
//		} catch (OperationCanceledException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		if (super.mCounterexample == null) {
			return true;
		} else {
			mLogger.info("Found potential Counterexample");
			return false;
		}
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(super.mIteration);
		// howDifferentAreInterpolants(mInterpolAutomaton.getStates());

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final boolean explointSigmaStarConcatOfIA = !mComputeHoareAnnotation;

//		EdgeChecker edgeChecker = new EdgeChecker(mSmtManager, mRootNode.getRootAnnot().getModGlobVarManager(),
//				mTraceChecker.getPredicateUnifier().getCoverageRelation());
		IHoareTripleChecker edgeChecker = new MonolithicHoareTripleChecker(mSmtManager.getManagedScript(), mModGlobVarManager);
		edgeChecker = new EfficientHoareTripleChecker(edgeChecker, mModGlobVarManager, mInterpolantGenerator.getPredicateUnifier(), mSmtManager);
		
		boolean progress;
		try {
			mLogger.debug("Start constructing difference");
			// assert(oldAbstraction.getStateFactory() ==
			// mInterpolAutomaton.getStateFactory());

			final IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

			switch (mPref.interpolantAutomatonEnhancement()) {
			case PREDICATE_ABSTRACTION:
			case PREDICATE_ABSTRACTION_CONSERVATIVE:
			case PREDICATE_ABSTRACTION_CANNIBALIZE:
			{
				final boolean conservativeSuccessorCandidateSelection =
					(mPref.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE);
				final boolean cannibalize =
						(mPref.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE);
				final DeterministicInterpolantAutomaton determinized = new DeterministicInterpolantAutomaton(mServices,
						mSmtManager, mModGlobVarManager, edgeChecker,
						(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction,
						mInterpolAutomaton, mInterpolantGenerator.getPredicateUnifier(), mLogger,
						conservativeSuccessorCandidateSelection, cannibalize);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				mInclusionCheck.addSubtrahend(determinized);
				mInterpolantAutomata.add(determinized);
				mHoareTripleChecker.add(edgeChecker);
				switchAllInterpolantAutomataToReadOnlyMode();
				final INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
						determinized)).getResult();
				assert (new InductivityCheck(mServices, test, false, true,
						new IncrementalHoareTripleChecker(mRootNode.getRootAnnot().getManagedScript(), mModGlobVarManager))).getResult();
				progress = true;
				break;
			}
			case EAGER:
			case NO_SECOND_CHANCE:
			case EAGER_CONSERVATIVE:
			{
				final boolean conservativeSuccessorCandidateSelection = mPref.interpolantAutomatonEnhancement() == mPref.interpolantAutomatonEnhancement();
				final boolean secondChance = (mPref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE);;
				final NondeterministicInterpolantAutomaton nondet = new NondeterministicInterpolantAutomaton(mServices,
						mSmtManager, mModGlobVarManager, edgeChecker,
						(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction,
						mInterpolAutomaton, mInterpolantGenerator.getPredicateUnifier(), mLogger, conservativeSuccessorCandidateSelection, secondChance);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				mInclusionCheck.addSubtrahend(nondet);
				mInterpolantAutomata.add(nondet);
				mHoareTripleChecker.add(edgeChecker);
				switchAllInterpolantAutomataToReadOnlyMode();
				final INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
						nondet)).getResult();
				assert (new InductivityCheck(mServices, test, false, true,
						new IncrementalHoareTripleChecker(mRootNode.getRootAnnot().getManagedScript(), mModGlobVarManager))).getResult();
				progress = true;
				break;
			}
			case NONE:
				mInclusionCheck.addSubtrahend(mInterpolAutomaton);
				final boolean acceptedByIA = (new Accepts<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
						mInterpolAutomaton,
						(NestedWord<CodeBlock>) mCounterexample.getWord())).getResult();
				progress = acceptedByIA;
				break;
			case BESTAPPROXIMATION_DEPRECATED:
			case SELFLOOP:
			default:
				throw new UnsupportedOperationException();
			}
			if (mPref.dumpAutomata()) {
				for (int i=0; i<mInterpolantAutomata.size(); i++) {
					final String filename = "IncrementalInclusion_Interation" + mIteration + "_InterpolantAutomaton" + i;
					super.writeAutomatonToFile(mInterpolantAutomata.get(i), filename);
				}
			}
		} finally {
//			mCegarLoopBenchmark.addEdgeCheckerData(edgeChecker.getEdgeCheckerBenchmark());
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		}
		if (progress) {
			return true;
		} else {
			return false;
		}
	}
	
	
	private void switchAllInterpolantAutomataToOnTheFlyConstructionMode() {
		for (final AbstractInterpolantAutomaton ia : mInterpolantAutomata) {
			ia.switchToOnDemandConstructionMode();
		}
	}
	
	private void switchAllInterpolantAutomataToReadOnlyMode() {
		for (final AbstractInterpolantAutomaton ia : mInterpolantAutomata) {
			ia.switchToReadonlyMode();
		}
		if (mPref.dumpAutomata()) {
			for (int i=0; i<mInterpolantAutomata.size(); i++) {
				final String filename = "EnhancedInterpolantAutomaton_WhoseConstructionWasStartedIn_Iteration" + mIteration;
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
