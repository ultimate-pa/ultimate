package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.PostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class CegarLoopConcurrentAutomata extends BasicCegarLoop {

	public CegarLoopConcurrentAutomata(String name, RootNode rootNode, SmtManager smtManager,
			TraceAbstractionBenchmarks timingStatistics, TAPreferences taPrefs, Collection<ProgramPoint> errorLocs,
			IUltimateServiceProvider services) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, INTERPOLATION.Craig_TreeInterpolation, false, services);
		// m_ContentFactory = new TaConcurContentFactory(
		// rootNode.getRootAnnot().getLocNodes(),
		// this,
		// super.m_SmtManager.getTheory(),
		// super.m_HoareAnnotation,
		// false);
	}

	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		StraightLineInterpolantAutomatonBuilder iab = new StraightLineInterpolantAutomatonBuilder(
				m_Services, new InCaReAlphabet<CodeBlock>(m_Abstraction), m_TraceChecker, m_PredicateFactoryInterpolantAutomata);
		m_InterpolAutomaton = iab.getResult();
		mLogger.info("Interpolatants " + m_InterpolAutomaton.getStates());

		m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		assert (accepts(m_InterpolAutomaton, m_Counterexample.getWord())) : "Interpolant automaton broken!";
		assert (new InductivityCheck(m_InterpolAutomaton, new EdgeChecker(m_SmtManager, m_ModGlobVarManager), false,
				true, mLogger)).getResult() : "Not inductive";
	}

	@Override
	protected void getInitialAbstraction() {
		StateFactory<IPredicate> predicateFactory = new PredicateFactory(super.m_SmtManager, m_Pref);
		CFG2Automaton cFG2NestedWordAutomaton = new Cfg2Nwa(m_RootNode, predicateFactory, m_SmtManager, m_Services);
		m_Abstraction = (NestedWordAutomaton<CodeBlock, IPredicate>) cFG2NestedWordAutomaton.getResult();

		if (m_Iteration <= m_Pref.watchIteration()
				&& (m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
	}

	@Override
	protected Collection<Set<IPredicate>> computePartition(INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
		mLogger.info("Start computation of initial partition.");
		Collection<IPredicate> states = automaton.getStates();
		Map<Set<ProgramPoint>, Set<IPredicate>> pp2p = new HashMap<Set<ProgramPoint>, Set<IPredicate>>();
		for (IPredicate p : states) {
			IMLPredicate mp = (IMLPredicate) p;
			pigeonHole(pp2p, mp);
		}
		Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
		for (Set<ProgramPoint> pps : pp2p.keySet()) {
			Set<IPredicate> statesWithSamePP = pp2p.get(pps);
			partition.add(statesWithSamePP);
		}
		mLogger.info("Finished computation of initial partition.");
		return partition;
	}

	/**
	 * Pigeon-hole (german: einsortieren) predicates according to their
	 * ProgramPoint
	 */
	protected void pigeonHole(Map<Set<ProgramPoint>, Set<IPredicate>> pp2p, IMLPredicate mp) {
		Set<IPredicate> statesWithSamePPs = pp2p.get(asHashSet(mp.getProgramPoints()));
		if (statesWithSamePPs == null) {
			statesWithSamePPs = new HashSet<IPredicate>();
			pp2p.put(asHashSet(mp.getProgramPoints()), statesWithSamePPs);
		}
		statesWithSamePPs.add(mp);
	}

	private static <E> Set<E> asHashSet(E[] array) {
		return new HashSet<E>(Arrays.asList(array));
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		m_StateFactoryForRefinement.setIteration(super.m_Iteration);
		// howDifferentAreInterpolants(m_InterpolAutomaton.getStates());

		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AutomataDifference);
		boolean explointSigmaStarConcatOfIA = !m_ComputeHoareAnnotation;

		PredicateFactory predicateFactory = (PredicateFactory) m_Abstraction.getStateFactory();

		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		Map<IPredicate, Set<IPredicate>> removedDoubleDeckers = null;
		Map<IPredicate, IPredicate> context2entry = null;
		EdgeChecker edgeChecker = new EdgeChecker(m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager());
		mLogger.debug("Start constructing difference");
		assert (oldAbstraction.getStateFactory() == m_InterpolAutomaton.getStateFactory());

		IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

		PostDeterminizer epd = new PostDeterminizer(m_Services, edgeChecker, m_ComputeHoareAnnotation, m_InterpolAutomaton, true,
				m_PredicateFactoryInterpolantAutomata);
		if (m_Pref.differenceSenwa()) {
			diff = new DifferenceSenwa<CodeBlock, IPredicate>(m_Services, oldAbstraction, m_InterpolAutomaton, epd, false);
		} else {
			diff = new Difference<CodeBlock, IPredicate>(m_Services, oldAbstraction, m_InterpolAutomaton, epd,
					m_StateFactoryForRefinement, explointSigmaStarConcatOfIA);
		}
		mLogger.info("Internal Transitions: " + epd.m_AnswerInternalAutomaton + " answers given by automaton "
				+ epd.m_AnswerInternalCache + " answers given by cache " + epd.m_AnswerInternalSolver
				+ " answers given by solver");
		mLogger.info("Call Transitions: " + epd.m_AnswerCallAutomaton + " answers given by automaton "
				+ epd.m_AnswerCallCache + " answers given by cache " + epd.m_AnswerCallSolver
				+ " answers given by solver");
		mLogger.info("Return Transitions: " + epd.m_AnswerReturnAutomaton + " answers given by automaton "
				+ epd.m_AnswerReturnCache + " answers given by cache " + epd.m_AnswerReturnSolver
				+ " answers given by solver");
		assert !m_SmtManager.isLocked();
		assert (new InductivityCheck(m_InterpolAutomaton, new EdgeChecker(m_SmtManager, m_ModGlobVarManager), false,
				true, mLogger)).getResult();
		// do the following check only to obtain logger messages of
		// checkInductivity
		assert (new InductivityCheck(epd.getRejectionCache(), new EdgeChecker(m_SmtManager, m_ModGlobVarManager), true,
				false, mLogger).getResult() | true);

		if (m_RemoveDeadEnds) {
			if (m_ComputeHoareAnnotation) {
				Difference<CodeBlock, IPredicate> difference = (Difference<CodeBlock, IPredicate>) diff;
				m_Haf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
			}
			diff.removeDeadEnds();
			if (m_ComputeHoareAnnotation) {
				m_Haf.addDeadEndDoubleDeckers(diff);
			}
		}

		m_Abstraction = (IAutomaton<CodeBlock, IPredicate>) diff.getResult();
		// m_DeadEndRemovalTime = diff.getDeadEndRemovalTime();
		if (m_Pref.dumpAutomata()) {
			String filename = "InterpolantAutomaton_Iteration" + m_Iteration;
			super.writeAutomatonToFile(m_InterpolAutomaton, filename);
		}

		m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AutomataDifference);

		Minimization minimization = m_Pref.minimize();
		switch (minimization) {
		case NONE:
			break;
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			minimizeAbstraction(m_StateFactoryForRefinement, m_PredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}

		boolean stillAccepted = (new Accepts<CodeBlock, IPredicate>(
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction,
				(NestedWord<CodeBlock>) m_Counterexample.getWord())).getResult();
		if (stillAccepted) {
			return false;
		} else {
			return true;
		}
	}
}
