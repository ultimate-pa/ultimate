/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * @author haettigj@informatik.uni-freiburg.de
 * 
 */
public class CegarLoopSequentialWithBackedges extends BasicCegarLoop {

	AutomatonEpimorphism<String> m_epimorphism;
	
	public CegarLoopSequentialWithBackedges(String name, RootNode rootNode, SmtManager smtManager,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs) {

		super(name, rootNode, smtManager, taPrefs, errorLocs);
	}

//	/**
//	 * constructs the interpolant automaton
//	 */
//	@Override
//	protected void constructInterpolantAutomaton() {
//		if (m_Pref.interpolatedLocs() == InterpolatedLocs.GUESS) {
//			NestedWordAutomaton<CodeBlock, Predicate> abstraction = (NestedWordAutomaton<CodeBlock, Predicate>) m_Abstraction;
//			m_InterpolAutomaton = new NestedWordAutomaton<CodeBlock, Predicate>(
//					abstraction.getAlphabet(), abstraction.getCallAlphabet(),
//					abstraction.getReturnAlphabet(),
//					abstraction.getStateFactory());
//			Predicate trueTerm = m_SmtManager.newTruePredicate(null);
//			m_InterpolAutomaton.addState(true, false, trueTerm);
//			Predicate falseTerm = m_SmtManager.newFalsePredicate(null);
//			m_InterpolAutomaton.addState(false, true, falseTerm);
//			for (Predicate sf : m_Interpolants) {
//				m_InterpolAutomaton.addState(false, false, sf);
//			}
//		} else {
//			InterpolantAutomataBuilder iab = new InterpolantAutomataBuilder(
//					m_Counterexample, m_Interpolants, m_Pref.additionalEdges(),
//					m_Pref.edges2True(), m_SmtManager, m_Pref, m_Iteration,
//					m_IterationPW);
//			m_InterpolAutomaton = iab.buildInterpolantAutomaton(m_Abstraction,
//					m_ContentFactory);
//			assert (m_InterpolAutomaton.accepts(m_Counterexample.getWord())) : "Interpolant automaton broken!";
//			assert (m_SmtManager.checkInductivity(m_InterpolAutomaton));
//		}
//
//		s_Logger.info("Interpolant Automaton has "
//				+ m_InterpolAutomaton.getStates().size() + " states");
//
//		if (m_Iteration <= m_Pref.watchIteration()
//				&& m_Pref.artifact() == Artifact.INTERPOLANT_AUTOMATON) {
//			m_ArtifactAutomaton = m_InterpolAutomaton;
//		}
//		if (m_Pref.dumpAutomata()) {
//			new TestFileWriter<String, String>(m_InterpolAutomaton,
//					m_Pref.dumpPath() + "/InterpolantAutomaton_Iteration"
//							+ m_Iteration, m_PrintAutomataLabeling);
//		}
//	}

//	/**
//	 * TODO commentary
//	 */
//	@Override
//	protected boolean refineAbstraction() throws OperationCanceledException {
//		if (m_Pref.minimize()) {
//			m_ContentFactory.beginRefinementOperation(m_Haf);
//		}
//
//		NestedWordAutomaton<CodeBlock, Predicate> abstraction = (NestedWordAutomaton<CodeBlock, Predicate>) m_Abstraction;
//		Map<Predicate, Set<Predicate>> removedDoubleDeckers = null;
//		Map<Predicate, Predicate> context2entry = null;
//
//		s_Logger.debug("Start constructing difference");
//		assert (abstraction.getStateFactory() == m_ContentFactory);
//
//		Difference<CodeBlock, Predicate> diff;
//
//		switch (m_Pref.determinization()) {
//		case POWERSET:
//			PowersetDeterminizer<CodeBlock, Predicate> psd = new PowersetDeterminizer<CodeBlock, Predicate>(
//					m_InterpolAutomaton);
//			diff = new Difference<CodeBlock, Predicate>(abstraction,
//					m_InterpolAutomaton, psd, false);
//			break;
//		case BESTAPPROXIMATION:
//			BestApproximationDeterminizer bed = new BestApproximationDeterminizer(
//					m_SmtManager, m_Pref, m_ContentFactory, m_InterpolAutomaton);
//			diff = new Difference<CodeBlock, Predicate>(abstraction,
//					m_InterpolAutomaton, bed, false);
//
//			s_Logger.info("Internal Transitions: "
//					+ bed.m_AnswerInternalAutomaton
//					+ " answers given by automaton "
//					+ bed.m_AnswerInternalCache + " answers given by cache "
//					+ bed.m_AnswerInternalSolver + " answers given by solver");
//			s_Logger.info("Call Transitions: " + bed.m_AnswerCallAutomaton
//					+ " answers given by automaton " + bed.m_AnswerCallCache
//					+ " answers given by cache " + bed.m_AnswerCallSolver
//					+ " answers given by solver");
//			s_Logger.info("Return Transitions: " + bed.m_AnswerReturnAutomaton
//					+ " answers given by automaton " + bed.m_AnswerReturnCache
//					+ " answers given by cache " + bed.m_AnswerReturnSolver
//					+ " answers given by solver");
//			break;
//
//		case EAGERPOST:
//			PostDeterminizer epd = new PostDeterminizer(m_SmtManager, m_Pref,
//					m_InterpolAutomaton, true);
//			diff = new Difference<CodeBlock, Predicate>(abstraction,
//					m_InterpolAutomaton, epd, false);
//			s_Logger.info("Internal Transitions: "
//					+ epd.m_AnswerInternalAutomaton
//					+ " answers given by automaton "
//					+ epd.m_AnswerInternalCache + " answers given by cache "
//					+ epd.m_AnswerInternalSolver + " answers given by solver");
//			s_Logger.info("Call Transitions: " + epd.m_AnswerCallAutomaton
//					+ " answers given by automaton " + epd.m_AnswerCallCache
//					+ " answers given by cache " + epd.m_AnswerCallSolver
//					+ " answers given by solver");
//			s_Logger.info("Return Transitions: " + epd.m_AnswerReturnAutomaton
//					+ " answers given by automaton " + epd.m_AnswerReturnCache
//					+ " answers given by cache " + epd.m_AnswerReturnSolver
//					+ " answers given by solver");
//			break;
//
//		case LAZYPOST:
//			PostDeterminizer lpd = new PostDeterminizer(m_SmtManager, m_Pref,
//					m_InterpolAutomaton, false);
//			diff = new Difference<CodeBlock, Predicate>(abstraction,
//					m_InterpolAutomaton, lpd, false);
//
//			s_Logger.info("Internal Transitions: "
//					+ lpd.m_AnswerInternalAutomaton
//					+ " answers given by automaton "
//					+ lpd.m_AnswerInternalCache + " answers given by cache "
//					+ lpd.m_AnswerInternalSolver + " answers given by solver");
//			s_Logger.info("Call Transitions: " + lpd.m_AnswerCallAutomaton
//					+ " answers given by automaton " + lpd.m_AnswerCallCache
//					+ " answers given by cache " + lpd.m_AnswerCallSolver
//					+ " answers given by solver");
//			s_Logger.info("Return Transitions: " + lpd.m_AnswerReturnAutomaton
//					+ " answers given by automaton " + lpd.m_AnswerReturnCache
//					+ " answers given by cache " + lpd.m_AnswerReturnSolver
//					+ " answers given by solver");
//			break;
//
//		case SELFLOOP:
//			SelfloopDeterminizer sed = new SelfloopDeterminizer(m_SmtManager,
//					m_Pref, m_ContentFactory, m_InterpolAutomaton);
//			diff = new Difference<CodeBlock, Predicate>(abstraction,
//					m_InterpolAutomaton, sed, false);
//			s_Logger.info("Internal Selfloops: " + sed.m_InternalSelfloop
//					+ " Internal NonSelfloops " + sed.m_InternalNonSelfloop);
//			s_Logger.info("Call Selfloops: " + sed.m_CallSelfloop
//					+ " Call NonSelfloops " + sed.m_CallNonSelfloop);
//			s_Logger.info("Return Selfloops: " + sed.m_ReturnSelfloop
//					+ " Return NonSelfloops " + sed.m_ReturnNonSelfloop);
//			break;
//		case STRONGESTPOST:
//			StrongestPostDeterminizer spd = new StrongestPostDeterminizer(
//					m_SmtManager, m_Pref, m_ContentFactory, m_InterpolAutomaton);
//			diff = new Difference<CodeBlock, Predicate>(abstraction,
//					m_InterpolAutomaton, spd, false);
//			break;
//		default:
//			throw new UnsupportedOperationException();
//		}
//		if (m_Pref.minimize()) {
//			m_ContentFactory.refinementOperationFinished();
//			diff.removeStatesThatCanNotReachFinal(true);
//			removedDoubleDeckers = diff.getRemovedDoubleDeckers();
//			context2entry = diff.getCallSuccOfRemovedDown();
//		}
//		m_Abstraction = diff.getResult();
//
//		if (m_Pref.minimize()) {
//			m_Haf.wipeReplacedContexts();
//			m_Haf.addDoubleDeckers(removedDoubleDeckers,
//					abstraction.getEmptyStackState());
//			m_Haf.addContext2Entry(context2entry);
//		}
//
//		// if (minimizeDelayed) {
//		// if (m_Pref.dumpAutomata()) {
//		// String filename =
//		// m_Pref.dumpPath()+"/AbstractionNonMinimized"+m_Iteration;
//		// new
//		// TestFileWriter<String,String>(m_Abstraction,filename,m_PrintAutomataLabeling);
//		// }
//		// m_Abstraction = new SingleEntryNwaBuilder<TransAnnot,Predicate>(
//		// (INestedWordAutomaton) m_Abstraction, true, false).getResult();
//		// }
//
//		if (m_BiggestAbstractionSize < m_Abstraction.size()) {
//			m_BiggestAbstractionSize = m_Abstraction.size();
//			m_BiggestAbstractionIteration = m_Iteration;
//		}
//
//		if (m_Pref.computeHoareAnnotation()) {
//			assert (m_SmtManager
//					.checkInductivity((INestedWordAutomaton<CodeBlock, Predicate>) m_Abstraction));
//		}
//		s_Logger.info("Abstraction has " + abstraction.sizeInformation());
//		s_Logger.info("Interpolant automaton has "
//				+ m_InterpolAutomaton.sizeInformation());
//
//		if (m_Iteration <= m_Pref.watchIteration()
//				&& (m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref
//						.artifact() == Artifact.RCFG)) {
//			m_ArtifactAutomaton = m_Abstraction;
//		}
//
//		if (m_Pref.dumpAutomata()) {
//			String filename = m_Pref.dumpPath() + "/Abstraction" + m_Iteration;
//			new TestFileWriter<String, String>(m_Abstraction, filename,
//					m_PrintAutomataLabeling);
//		}
//
//		if (m_Abstraction.accepts(m_Counterexample.getWord())) {
//			s_Logger.warn("No progress! Counterexample not eliminated in refined abstraction");
//			assert (m_Pref.interpolatedLocs() == InterpolatedLocs.GUESS) : "Should occur only if interpolants are not inductive for counterexample";
//			return false;
//		} else {
//			return true;
//		}
//		// return true;
//	}
}
