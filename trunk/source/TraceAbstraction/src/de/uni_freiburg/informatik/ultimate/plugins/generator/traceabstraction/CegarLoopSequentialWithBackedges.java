/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.SuperDifference;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

/**
 * @author haettigj@informatik.uni-freiburg.de
 * 
 */
public class CegarLoopSequentialWithBackedges extends BasicCegarLoop
{
	/**
	 * Maps states from the original automaton to corresponding 
	 * states in the new interpolant automaton.
	 */
	protected AutomatonEpimorphism<IPredicate> m_Epimorphism;

	/**
	 * List of states we already added to the new interpolant
	 * automaton.
	 */
	protected ArrayList<IPredicate> m_AddedStates;

	/**
	 * Holds the nodes and edges of the error path
	 */
	protected NestedRun<CodeBlock, IPredicate> m_CounterExamplePath;

	/**
	 * Used for computing the interpolants of additional paths
	 */
	protected TraceChecker m_ExtraTraceChecker;

	/**
	 * Override the abstraction with a version casted to 
	 * NestedWordAutomaton. It is casted in every call of
	 * constructInterpolantAutomaton.
	 */
	private INestedWordAutomaton<CodeBlock, IPredicate> m_Abstraction;

	//	/**
	//	 * This contains a new path if there was found one.
	//	 */
	//	protected NestedWord<CodeBlock> m_ActualPath; 
	//	
	protected IPredicate m_ActualStartingState;

	protected IPredicate m_InitialState;
	protected IPredicate m_FinalState;

	protected PredicateUnifier m_PredicateUnifier;




	public CegarLoopSequentialWithBackedges(String name, RootNode rootNode,
			SmtManager smtManager, TraceAbstractionBenchmarks timingStatistics,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs)
	{
		super(name, rootNode, smtManager, timingStatistics, taPrefs, errorLocs);
	}



	/**
	 * constructs the interpolant automaton
	 */
	@Override
	protected void constructInterpolantAutomaton()
	{
		// cast the abstracten as nested word automaton
		m_Abstraction = (INestedWordAutomaton<CodeBlock, IPredicate>)super.m_Abstraction;

		// cast the path as nested run
		m_CounterExamplePath = (NestedRun<CodeBlock, IPredicate>) m_Counterexample;

		// create an new interpolant automaton
		m_InterpolAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(
				m_Abstraction.getAlphabet(), m_Abstraction.getCallAlphabet(),
				m_Abstraction.getReturnAlphabet(), m_Abstraction.getStateFactory());

		// remember some properties
		m_InitialState = m_TraceChecker.getPrecondition();
		m_FinalState = m_TraceChecker.getPostcondition();
		m_PredicateUnifier = m_TraceChecker.getPredicateUnifier();
		m_Epimorphism = new AutomatonEpimorphism<>();

		// hold an iterable list of all states we added to the new automaton
		m_AddedStates = new ArrayList<IPredicate>();

		// -- initialize interpolant automaton --
		// add the initial state of the error path
		m_AddedStates.add(m_CounterExamplePath.getStateAtPosition(0));
		m_InterpolAutomaton.addState(true, m_InitialState == m_FinalState, m_InitialState);
		m_Epimorphism.insert(m_CounterExamplePath.getStateAtPosition(0), m_InitialState);
		// add the final state of the error path
		m_AddedStates.add(m_CounterExamplePath.getStateAtPosition(m_CounterExamplePath.getLength() - 1));
		m_InterpolAutomaton.addState(m_InitialState == m_FinalState, true, m_FinalState);
		m_Epimorphism.insert(m_CounterExamplePath.getStateAtPosition(m_CounterExamplePath.getLength() - 1), m_FinalState);
		// Add internal states of the error path
		addPath(m_CounterExamplePath.getWord(), 
				m_CounterExamplePath.getStateSequence(), 
				m_TraceChecker.getInterpolants(),
				m_InitialState, m_FinalState);

		// go through each state in the list of states as
		// starting point and find a path to any other annotated state
		for(int i = 0; i < m_AddedStates.size(); i++)
		{
			m_ActualStartingState = m_AddedStates.get(i);
			// go through the automaton in depth first manner
			// this will fill m_ActualPath
			ArrayList<IPredicate> path = new ArrayList<IPredicate>(16);
			path.add(m_ActualStartingState);
			explorePath(m_ActualStartingState, new NestedWord<CodeBlock>(), path);		
		}
	}

	/**
	 * Explore all edges of a node.
	 * If it completes a path feed out:
	 * 	- If the path was accepted by the interpolant generator
	 * 		add the states to the new interpolant automaton
	 *  - If the path was not accepted
	 *    just go back and try other pathes.
   * @param actual s actual state of the algorithm, initially: starting state
   * @param actualWord labels of the edges of the actual path
   * @param actualPath list of the states of the actual path
	 * @return true if path was found, false if there is no path with suitable interpolants found
	 */
	boolean explorePath(IPredicate s, NestedWord<CodeBlock> actualWord, ArrayList<IPredicate> actualPath)
	{
		s_Logger.debug("explore path: " + s.toString() + " wordLen: " + actualWord.length() + " pathLen: " + actualPath.size());
		/// there are three kinds of transitions: call, return, internal 
		// return transitions
		for(OutgoingReturnTransition<CodeBlock, IPredicate> e : m_Abstraction.returnSuccessors(s))
		{
			NestedWord<CodeBlock> newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.MINUS_INFINITY));
		}

		// calls transitions
		for(OutgoingCallTransition<CodeBlock, IPredicate> e : m_Abstraction.callSuccessors(s))
		{
			NestedWord<CodeBlock> newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.PLUS_INFINITY));
		}

		// nested transitions
		for(OutgoingInternalTransition<CodeBlock, IPredicate> e : m_Abstraction.internalSuccessors(s))
		{
			// the next state is the target state of the edge
			IPredicate target = e.getSucc();
			
			// add the letter to the path
			NestedWord<CodeBlock> newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.INTERNAL_POSITION));			
			// try to add the target state of the edge (temporarily)
			actualPath.add(target);

			s_Logger.debug("explore edge: " + e.toString() + " wordLen: " + actualWord.length() + " pathLen: " + actualPath.size());
			
			// if we remembered to add the target state, we completed a path
			if(m_AddedStates.contains(target))
			{
				IPredicate pre = m_Epimorphism.getMapping(m_ActualStartingState);
				IPredicate post = m_Epimorphism.getMapping(target);
				// test if we found a new path which can be added ...
				m_TraceChecker = new TraceChecker(
						pre,
						post, 
						new TreeMap<Integer, IPredicate>(), //TODO 
						newWord,
						m_SmtManager, 
						m_RootNode.getRootAnnot().getModGlobVarManager());
				
				if(m_TraceChecker.isCorrect() == LBool.UNSAT)
				{
					m_TraceChecker.computeInterpolants(new TraceChecker.AllIntegers(), m_PredicateUnifier, m_Pref.interpolation());

					addPath(newWord, actualPath, m_TraceChecker.getInterpolants(), pre, post);
					return true;
				}		
			}
			else
			{
				// if not reached a state on the path, go further
				if(explorePath(target, newWord, actualPath))
				{					
					return true;
				}
			}

			// remove the last element 
			actualPath.remove(actualPath.size() - 1);
		}	

		// if no edge leads to complete an acceptable path
		// return false to try other edges before on the path
		return false;
	}

	/**
	 * Add the path given from the trace checker.
	 * Assumes that the first and last state is already added.
	 * edges  states  interpolants
	 *          s0       pre
	 *   e0 
	 *          s1       I0
	 *   e1
	 *          s2       I1
	 *   e2 
	 *          s3       post
	 * @param edges Contains the edges along the path
	 * @param states Holds all states (0, ..., n-1)
	 * @param interpolants The interpolants along the path for the states 1, ..., n-2
	 * @param pre the formula for the state 0
	 * @param post the formula for the state n-1
	 */
	void addPath(
			NestedWord<CodeBlock> edges,
			ArrayList<IPredicate> states, 
			IPredicate[] interpolants, 
			IPredicate pre, 
			IPredicate post)
	{
		s_Logger.debug("add path: numEdges:" + edges.length() + " numStates:" + states.size() + " numInterpol:" + interpolants.length);
		
		// add all edges except the last one
		for(int i = 0; i < edges.length(); i++)
		{
			CodeBlock e = edges.getSymbolAt(i);
		
			IPredicate targetS = states.get(i + 1); 
			
			IPredicate sourceI = i == 0 ? pre : interpolants[i - 1];
			IPredicate targetI;
			if(i == edges.length() - 1)
			{
				targetI = post;
			}
			else
			{
				targetI = interpolants[i];
				// do not add the last state in the sequence (and not the first)
				m_AddedStates.add(targetS);
				m_Epimorphism.insert(targetS, targetI);
			}
			
			// add the state into the abstraction automaton
			// this must always be checked
			if(!m_InterpolAutomaton.getStates().contains(targetI))
			{
				m_InterpolAutomaton.addState(targetI == m_InitialState, targetI == m_FinalState, targetI);
			}
			
			// add the edge into the abstraction automaton
			if(m_CounterExamplePath.isInternalPosition(i))
			{
				m_InterpolAutomaton.addInternalTransition(sourceI, e, targetI);
			}
			else
			{
				if(m_CounterExamplePath.isCallPosition(i))
				{
					m_InterpolAutomaton.addCallTransition(sourceI, e, targetI);
				}
				else
				{
					IPredicate hier = null; // TODO
					m_InterpolAutomaton.addReturnTransition(sourceI, hier, e, targetI);
				}
			}		
		}
	}
 
	
	/**
	 * Construct the new programm abstraction by subtraction the
	 * interpolant automaton from the abstraction
	 * @return true iff the trace of m_Counterexample (which was accepted by the
	 * old m_Abstraction) is not accepted by the m_Abstraction.
	 */
	@Override
	protected boolean refineAbstraction() throws OperationCanceledException
	{

		SuperDifference<CodeBlock, IPredicate> diff = new SuperDifference<CodeBlock, IPredicate>(
				m_Abstraction, m_InterpolAutomaton, m_Epimorphism, false);

		m_Abstraction = diff.getResult();
	
//		if (m_Pref.minimize())
//		{
//			m_ContentFactory.refinementOperationFinished();
//			diff.removeStatesThatCanNotReachFinal(true);
//			removedDoubleDeckers = diff.getRemovedDoubleDeckers();
//			context2entry = diff.getCallSuccOfRemovedDown();
//		}
		
		if (m_BiggestAbstractionSize < m_Abstraction.size()) {
			m_BiggestAbstractionSize = m_Abstraction.size();
			m_BiggestAbstractionIteration = m_Iteration;
		}

		s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
		s_Logger.info("Interpolant automaton has "
				+ m_InterpolAutomaton.sizeInformation());
		
		return true;
	}
	
	
	//	if (m_Pref.interpolatedLocs() == InterpolatedLocs.GUESS)
	//	{
	//
	//		Predicate trueTerm = m_SmtManager.newTruePredicate(null);
	//		m_InterpolAutomaton.addState(true, false, trueTerm);
	//		Predicate falseTerm = m_SmtManager.newFalsePredicate(null);
	//		m_InterpolAutomaton.addState(false, true, falseTerm);
	//		for (Predicate sf : m_Interpolants)
	//		{
	//			m_InterpolAutomaton.addState(false, false, sf);
	//		}
	//	}
	//	else
	//	{
	//		InterpolantAutomataBuilder iab = new InterpolantAutomataBuilder(
	//				m_Counterexample, m_Interpolants, m_Pref.additionalEdges(),
	//				m_Pref.edges2True(), m_SmtManager, m_Pref, m_Iteration, m_IterationPW);
	//		m_InterpolAutomaton = iab.buildInterpolantAutomaton(m_Abstraction,
	//				m_ContentFactory);
	//		assert (m_InterpolAutomaton.accepts(m_Counterexample.getWord())) :
	//			"Interpolant automaton broken!";
	//		assert (m_SmtManager.checkInductivity(m_InterpolAutomaton));
	//	}
	//
	//	s_Logger.info("Interpolant Automaton has "
	//			+ m_InterpolAutomaton.getStates().size() + " states");
	//
	//	// if (m_Iteration <= m_Pref.watchIteration()
	//	// && m_Pref.artifact() == Artifact.INTERPOLANT_AUTOMATON)
	//	// {
	//	// m_ArtifactAutomaton = m_InterpolAutomaton;
	//	// }
	//	//
	//	// if (m_Pref.dumpAutomata())
	//	// {
	//	// new TestFileWriter<String, String>(m_InterpolAutomaton, m_Pref.dumpPath()
	//	// + "/InterpolantAutomaton_Iteration" + m_Iteration,
	//	// m_PrintAutomataLabeling);
	//	// }
	//}

	/**
	 * TODO commentary
	 */
//	@Override
//	protected boolean refineAbstraction()  
//	{
		//		if (m_Pref.minimize()) {
		//			m_ContentFactory.beginRefinementOperation(m_Haf);
		//		}
		//
		//		NestedWordAutomaton<CodeBlock, Predicate> abstraction =
		//				(NestedWordAutomaton<CodeBlock, Predicate>) m_Abstraction;
		//		Map<Predicate, Set<Predicate>> removedDoubleDeckers = null;
		//		Map<Predicate, Predicate> context2entry = null;
		//
		//		s_Logger.debug("Start constructing difference");
		//		assert (abstraction.getStateFactory() == m_ContentFactory);
		//
		//		Difference<CodeBlock, Predicate> diff;
		//
		//		switch (m_Pref.determinization()) {
		//			case POWERSET:
		//				PowersetDeterminizer<CodeBlock, Predicate> psd = new
		//				PowersetDeterminizer<CodeBlock, Predicate>(
		//						m_InterpolAutomaton);
		//				diff = new Difference<CodeBlock, Predicate>(abstraction,
		//						m_InterpolAutomaton, psd, false);
		//				break;
		//			case BESTAPPROXIMATION:
		//				BestApproximationDeterminizer bed = new BestApproximationDeterminizer(
		//						m_SmtManager, m_Pref, m_ContentFactory, m_InterpolAutomaton);
		//				diff = new Difference<CodeBlock, Predicate>(abstraction,
		//						m_InterpolAutomaton, bed, false);
		//
		//				s_Logger.info("Internal Transitions: "
		//						+ bed.m_AnswerInternalAutomaton
		//						+ " answers given by automaton "
		//						+ bed.m_AnswerInternalCache + " answers given by cache "
		//						+ bed.m_AnswerInternalSolver + " answers given by solver");
		//				s_Logger.info("Call Transitions: " + bed.m_AnswerCallAutomaton
		//						+ " answers given by automaton " + bed.m_AnswerCallCache
		//						+ " answers given by cache " + bed.m_AnswerCallSolver
		//						+ " answers given by solver");
		//				s_Logger.info("Return Transitions: " + bed.m_AnswerReturnAutomaton
		//						+ " answers given by automaton " + bed.m_AnswerReturnCache
		//						+ " answers given by cache " + bed.m_AnswerReturnSolver
		//						+ " answers given by solver");
		//				break;
		//
		//			case EAGERPOST:
		//				PostDeterminizer epd = new PostDeterminizer(m_SmtManager, m_Pref,
		//						m_InterpolAutomaton, true);
		//				diff = new Difference<CodeBlock, Predicate>(abstraction,
		//						m_InterpolAutomaton, epd, false);
		//				s_Logger.info("Internal Transitions: "
		//						+ epd.m_AnswerInternalAutomaton
		//						+ " answers given by automaton "
		//						+ epd.m_AnswerInternalCache + " answers given by cache "
		//						+ epd.m_AnswerInternalSolver + " answers given by solver");
		//				s_Logger.info("Call Transitions: " + epd.m_AnswerCallAutomaton
		//						+ " answers given by automaton " + epd.m_AnswerCallCache
		//						+ " answers given by cache " + epd.m_AnswerCallSolver
		//						+ " answers given by solver");
		//				s_Logger.info("Return Transitions: " + epd.m_AnswerReturnAutomaton
		//						+ " answers given by automaton " + epd.m_AnswerReturnCache
		//						+ " answers given by cache " + epd.m_AnswerReturnSolver
		//						+ " answers given by solver");
		//				break;
		//
		//			case LAZYPOST:
		//				PostDeterminizer lpd = new PostDeterminizer(m_SmtManager, m_Pref,
		//						m_InterpolAutomaton, false);
		//				diff = new Difference<CodeBlock, Predicate>(abstraction,
		//						m_InterpolAutomaton, lpd, false);
		//
		//				s_Logger.info("Internal Transitions: "
		//						+ lpd.m_AnswerInternalAutomaton
		//						+ " answers given by automaton "
		//						+ lpd.m_AnswerInternalCache + " answers given by cache "
		//						+ lpd.m_AnswerInternalSolver + " answers given by solver");
		//				s_Logger.info("Call Transitions: " + lpd.m_AnswerCallAutomaton
		//						+ " answers given by automaton " + lpd.m_AnswerCallCache
		//						+ " answers given by cache " + lpd.m_AnswerCallSolver
		//						+ " answers given by solver");
		//				s_Logger.info("Return Transitions: " + lpd.m_AnswerReturnAutomaton
		//						+ " answers given by automaton " + lpd.m_AnswerReturnCache
		//						+ " answers given by cache " + lpd.m_AnswerReturnSolver
		//						+ " answers given by solver");
		//				break;
		//
		//			case SELFLOOP:
		//				SelfloopDeterminizer sed = new SelfloopDeterminizer(m_SmtManager,
		//						m_Pref, m_ContentFactory, m_InterpolAutomaton);
		//				diff = new Difference<CodeBlock, Predicate>(abstraction,
		//						m_InterpolAutomaton, sed, false);
		//				s_Logger.info("Internal Selfloops: " + sed.m_InternalSelfloop
		//						+ " Internal NonSelfloops " + sed.m_InternalNonSelfloop);
		//				s_Logger.info("Call Selfloops: " + sed.m_CallSelfloop
		//						+ " Call NonSelfloops " + sed.m_CallNonSelfloop);
		//				s_Logger.info("Return Selfloops: " + sed.m_ReturnSelfloop
		//						+ " Return NonSelfloops " + sed.m_ReturnNonSelfloop);
		//				break;
		//			case STRONGESTPOST:
		//				StrongestPostDeterminizer spd = new StrongestPostDeterminizer(
		//						m_SmtManager, m_Pref, m_ContentFactory, m_InterpolAutomaton);
		//				diff = new Difference<CodeBlock, Predicate>(abstraction,
		//						m_InterpolAutomaton, spd, false);
		//				break;
		//			default:
		//				throw new UnsupportedOperationException();
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
		//		//
		//		TestFileWriter<String,String>(m_Abstraction,filename,m_PrintAutomataLabeling);
		//		// }
		//		// m_Abstraction = new SingleEntryNwaBuilder<TransAnnot,Predicate>(
		//		// (INestedWordAutomaton) m_Abstraction, true, false).getResult();
		//		// }
		//

		//
		//		if (m_Pref.computeHoareAnnotation()) {
		//			assert (m_SmtManager
		//					.checkInductivity((INestedWordAutomaton<CodeBlock, Predicate>)
		//							m_Abstraction));
		//		}
		//		s_Logger.info("Abstraction has " + abstraction.sizeInformation());
		//		s_Logger.info("Interpolant automaton has "
		//				+ m_InterpolAutomaton.sizeInformation());
		//
		//		if (m_Iteration <= m_Pref.watchIteration()
		//				&& (m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref
		//				.artifact() == Artifact.RCFG)) {
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
		//			assert (m_Pref.interpolatedLocs() == InterpolatedLocs.GUESS) :
		//				"Should occur only if interpolants are not inductive for counterexample";
		//			return false;
		//		} else {
		//			return true;
		//		}
//		return true;
//	}
}
