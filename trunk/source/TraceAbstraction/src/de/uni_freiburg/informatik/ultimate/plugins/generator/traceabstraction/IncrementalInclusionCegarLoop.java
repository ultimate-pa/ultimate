package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck2;
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
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton2;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;

public class IncrementalInclusionCegarLoop extends BasicCegarLoop {
	
	protected AbstractIncrementalInclusionCheck<CodeBlock, IPredicate> m_InclusionCheck;
	protected final LanguageOperation m_LanguageOperation;
	protected final List<DeterministicInterpolantAutomaton2> m_InterpolantAutomata = new ArrayList<DeterministicInterpolantAutomaton2>();

	public IncrementalInclusionCegarLoop(String name, RootNode rootNode,
			SmtManager smtManager, TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs, INTERPOLATION interpolation,
			boolean computeHoareAnnotation, IUltimateServiceProvider services,
			LanguageOperation languageOperation) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, interpolation,
				computeHoareAnnotation, services);
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
		
		boolean acceptedByDeterminized;
		try {
			mLogger.debug("Start constructing difference");
			// assert(oldAbstraction.getStateFactory() ==
			// m_InterpolAutomaton.getStateFactory());

			IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

			switch (m_Pref.determinization()) {
			case CODENAME_PROJECT_BELLWALD:
				DeterministicInterpolantAutomaton2 determinized = new DeterministicInterpolantAutomaton2(m_Services, 
						m_SmtManager, m_ModGlobVarManager, edgeChecker, (INestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction, m_InterpolAutomaton, m_TraceChecker, mLogger);
				switchAllInterpolantAutomataToOnTheFlyConstructionMode();
				m_InclusionCheck.addSubtrahend(determinized);
				m_InterpolantAutomata.add(determinized);
//				determinized.switchToReadonlyMode();
				switchAllInterpolantAutomataToReadOnlyMode();
//				assert (edgeChecker.isAssertionStackEmpty());
				INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(m_Services, 
						determinized)).getResult();
				assert (new InductivityCheck(test, new EdgeChecker(m_SmtManager, m_ModGlobVarManager), false,
						true, mLogger)).getResult();
				acceptedByDeterminized = (new Accepts<CodeBlock, IPredicate>(
						determinized,
						(NestedWord<CodeBlock>) m_Counterexample.getWord())).getResult();
				break;
			case POWERSET:
			case BESTAPPROXIMATION:
			case EAGERPOST:
			case LAZYPOST:
			case SELFLOOP:
			case STRONGESTPOST:
			case NEWEAGER:
			default:
				throw new UnsupportedOperationException();
			}
			if (m_Pref.dumpAutomata()) {
				String filename = "InterpolantAutomaton_Iteration" + m_Iteration;
				super.writeAutomatonToFile(m_InterpolAutomaton, filename);
			}
		} finally {
//			m_CegarLoopBenchmark.addEdgeCheckerData(edgeChecker.getEdgeCheckerBenchmark());
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AutomataDifference);
		}

		if (acceptedByDeterminized) {
			return true;
		} else {
			return false;
		}

	}
	
	
	private void switchAllInterpolantAutomataToOnTheFlyConstructionMode() {
		for (DeterministicInterpolantAutomaton2 ia : m_InterpolantAutomata) {
			ia.switchToOnTheFlyConstructionMode();
		}
	}
	
	private void switchAllInterpolantAutomataToReadOnlyMode() {
		for (DeterministicInterpolantAutomaton2 ia : m_InterpolantAutomata) {
			ia.switchToReadonlyMode();
		}
	}

	

}
