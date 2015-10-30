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
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck2;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck2DeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck2DeadEndRemovalAdvanceCover;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck3;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck3_2;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck4;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck4_2;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck5;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck5_2;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.AbstractIncrementalInclusionCheck;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.InclusionViaDifference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;

public class IncrementalInclusionCegarLoop extends BasicCegarLoop {
	
	protected AbstractIncrementalInclusionCheck<CodeBlock, IPredicate> m_InclusionCheck;
	protected final LanguageOperation m_LanguageOperation;
	protected final List<AbstractInterpolantAutomaton> m_InterpolantAutomata = new ArrayList<AbstractInterpolantAutomaton>();
	protected final List<IHoareTripleChecker> m_HoareTripleChecker = new ArrayList<IHoareTripleChecker>();

	public IncrementalInclusionCegarLoop(String name, RootNode rootNode,
			SmtManager smtManager, TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs, INTERPOLATION interpolation,
			boolean computeHoareAnnotation, IUltimateServiceProvider services, 
			IToolchainStorage storage,
			LanguageOperation languageOperation) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, interpolation,
				computeHoareAnnotation, services, storage);
		m_LanguageOperation = languageOperation;
		if (m_ComputeHoareAnnotation) {
			throw new UnsupportedOperationException(
					"while using this CEGAR loop computation of Hoare annotation is unsupported ");
		}
	}
	
	
	

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();
		switch (m_LanguageOperation) {
		case DIFFERENCE:
			throw new AssertionError("wrong cegar loop for this");
		case INCREMENTAL_INCLUSION_VIA_DIFFERENCE: {
			m_InclusionCheck = new InclusionViaDifference(m_Services, 
					m_StateFactoryForRefinement, 
					m_PredicateFactoryInterpolantAutomata, 
					(INestedWordAutomatonSimple) m_Abstraction);
		}
		break;
		case INCREMENTAL_INCLUSION_2: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck2<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck2DeadEndRemoval<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS_MULTIPLECE: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_3: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck3<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_3_2: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck3_2<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_4: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck4<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_4_2: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck4_2<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_5: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck5<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		case INCREMENTAL_INCLUSION_5_2: {
			List<INestedWordAutomatonSimple<CodeBlock, IPredicate>> empty = Collections.emptyList();
			m_InclusionCheck = new IncrementalInclusionCheck5_2<CodeBlock, IPredicate>(
					m_Services, m_StateFactoryForRefinement, 
					(INestedWordAutomatonSimple) m_Abstraction, empty);
		}
		break;
		default:
			throw new AssertionError("unknown case");
		}
	}




	@Override
	protected boolean isAbstractionCorrect() throws OperationCanceledException {
		super.m_Counterexample = m_InclusionCheck.getCounterexample();
//		try {
//				m_Counterexample = emptyWithAI.getNestedRun();
//			} else {
//				m_Counterexample = (new IsEmpty<CodeBlock, IPredicate>((INestedWordAutomatonOldApi) m_Abstraction))
//						.getNestedRun();
//			}
//		} catch (OperationCanceledException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		if (super.m_Counterexample == null) {
			return true;
		} else {
			mLogger.info("Found potential Counterexample");
			return false;
		}
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		m_StateFactoryForRefinement.setIteration(super.m_Iteration);
		// howDifferentAreInterpolants(m_InterpolAutomaton.getStates());

		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AutomataDifference);
		boolean explointSigmaStarConcatOfIA = !m_ComputeHoareAnnotation;

//		EdgeChecker edgeChecker = new EdgeChecker(m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager(),
//				m_TraceChecker.getPredicateUnifier().getCoverageRelation());
		IHoareTripleChecker edgeChecker = new MonolithicHoareTripleChecker(m_SmtManager);
		edgeChecker = new EfficientHoareTripleChecker(edgeChecker, m_ModGlobVarManager, m_InterpolantGenerator.getPredicateUnifier(), m_SmtManager);
		
		boolean progress;
		try {
			mLogger.debug("Start constructing difference");
			// assert(oldAbstraction.getStateFactory() ==
			// m_InterpolAutomaton.getStateFactory());

			IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

			switch (m_Pref.interpolantAutomatonEnhancement()) {
			case PREDICATE_ABSTRACTION:
			case PREDICATE_ABSTRACTION_CONSERVATIVE:
			case PREDICATE_ABSTRACTION_CANNIBALIZE:
			{
				boolean conservativeSuccessorCandidateSelection = 
					(m_Pref.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE);
				boolean cannibalize = 
						(m_Pref.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE);
				DeterministicInterpolantAutomaton determinized = new DeterministicInterpolantAutomaton(m_Services, 
						m_SmtManager, m_ModGlobVarManager, edgeChecker, 
						(INestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction, 
						m_InterpolAutomaton, m_InterpolantGenerator.getPredicateUnifier(), mLogger,
						conservativeSuccessorCandidateSelection, cannibalize);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				m_InclusionCheck.addSubtrahend(determinized);
				m_InterpolantAutomata.add(determinized);
				m_HoareTripleChecker.add(edgeChecker);
				switchAllInterpolantAutomataToReadOnlyMode();
				INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(m_Services, 
						determinized)).getResult();
				assert (new InductivityCheck(m_Services, test, false, true,
						new IncrementalHoareTripleChecker(m_SmtManager, m_ModGlobVarManager))).getResult();
				progress = true;
				break;
			}
			case EAGER:
			case NO_SECOND_CHANCE:
			case EAGER_CONSERVATIVE:
			{
				boolean conservativeSuccessorCandidateSelection = m_Pref.interpolantAutomatonEnhancement() == m_Pref.interpolantAutomatonEnhancement();
				boolean secondChance = (m_Pref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE);;
				NondeterministicInterpolantAutomaton nondet = new NondeterministicInterpolantAutomaton(m_Services, 
						m_SmtManager, m_ModGlobVarManager, edgeChecker, 
						(INestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction, 
						m_InterpolAutomaton, m_InterpolantGenerator.getPredicateUnifier(), mLogger, conservativeSuccessorCandidateSelection, secondChance);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				m_InclusionCheck.addSubtrahend(nondet);
				m_InterpolantAutomata.add(nondet);
				m_HoareTripleChecker.add(edgeChecker);
				switchAllInterpolantAutomataToReadOnlyMode();
				INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(m_Services, 
						nondet)).getResult();
				assert (new InductivityCheck(m_Services, test, false, true,
						new IncrementalHoareTripleChecker(m_SmtManager, m_ModGlobVarManager))).getResult();
				progress = true;
				break;
			}
			case NONE:
				m_InclusionCheck.addSubtrahend(m_InterpolAutomaton);
				boolean acceptedByIA = (new Accepts<CodeBlock, IPredicate>(m_Services, 
						m_InterpolAutomaton,
						(NestedWord<CodeBlock>) m_Counterexample.getWord())).getResult();
				progress = acceptedByIA;
				break;
			case BESTAPPROXIMATION_DEPRECATED:
			case SELFLOOP:
			default:
				throw new UnsupportedOperationException();
			}
			if (m_Pref.dumpAutomata()) {
				for (int i=0; i<m_InterpolantAutomata.size(); i++) {
					String filename = "IncrementalInclusion_Interation" + m_Iteration + "_InterpolantAutomaton" + i;
					super.writeAutomatonToFile(m_InterpolantAutomata.get(i), filename);
				}
			}
		} finally {
//			m_CegarLoopBenchmark.addEdgeCheckerData(edgeChecker.getEdgeCheckerBenchmark());
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AutomataDifference);
		}
		if (progress) {
			return true;
		} else {
			return false;
		}
	}
	
	
	private void switchAllInterpolantAutomataToOnTheFlyConstructionMode() {
		for (AbstractInterpolantAutomaton ia : m_InterpolantAutomata) {
			ia.switchToOnDemandConstructionMode();
		}
	}
	
	private void switchAllInterpolantAutomataToReadOnlyMode() {
		for (AbstractInterpolantAutomaton ia : m_InterpolantAutomata) {
			ia.switchToReadonlyMode();
		}
		if (m_Pref.dumpAutomata()) {
			for (int i=0; i<m_InterpolantAutomata.size(); i++) {
				String filename = "EnhancedInterpolantAutomaton_WhoseConstructionWasStartedIn_Iteration" + m_Iteration;
				super.writeAutomatonToFile(m_InterpolantAutomata.get(i), filename);
				m_InterpolantAutomata.get(i);
			}
		}
	}
	
	@Override
	public void finish() {
		assert m_HoareTripleChecker.size() == m_InterpolantAutomata.size();
		for (IHoareTripleChecker htc : m_HoareTripleChecker) {
			m_CegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
		}
		
	}

	

}
