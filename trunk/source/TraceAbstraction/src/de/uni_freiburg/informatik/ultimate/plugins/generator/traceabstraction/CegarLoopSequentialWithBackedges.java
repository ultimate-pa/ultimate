/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.SuperDifference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
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
	 * We need to keep track of the edges we already visited.
	 * This is only needed for self-loops and edges along states
	 * already taken
	 */
	protected HashSet<Transitionlet<CodeBlock, IPredicate>> m_VisitedSingleEdges;

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
	private INestedWordAutomaton<CodeBlock, IPredicate> m_NestedAbstraction;

	/**
	 * When adding additional sub paths to the interpolant automaton.
	 * We always start from a state which is already added.
	 * This holds that starting point. 
	 */
	protected IPredicate m_ActualStartingState;

	/**
	 * When adding additional sub paths to the interpolant automaton
	 * This will hold the actual path.
	 */
	protected ArrayList<IPredicate> m_ActualPath;
	
	/**
	 * Points to the initial state of the abstraction, i.e. true
	 */
	protected IPredicate m_InitialState;

	/**
	 * Points to the final state of the abstraction, i.e. false
	 */
	protected IPredicate m_FinalState;

	/**
	 * This is used to merge states
	 */
	protected PredicateUnifier m_PredicateUnifier;

	/**
	 * Holds the error paths, for debuging.
	 */
	private ArrayList<String> m_ErrorPathHistory;


	
	
	public CegarLoopSequentialWithBackedges(String name, RootNode rootNode,
			SmtManager smtManager, TraceAbstractionBenchmarks timingStatistics,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs)
	{
		super(name, rootNode, smtManager, timingStatistics, taPrefs, errorLocs);
		m_ErrorPathHistory = new ArrayList<String>(); 	
	}



	/**
	 * constructs the interpolant automaton
	 */
	@Override
	protected void constructInterpolantAutomaton()
	{
		s_Logger.debug("Start constructing interpolant automaton.");
		
		// cast the abstracten as nested word automaton
		m_NestedAbstraction = (INestedWordAutomaton<CodeBlock, IPredicate>)m_Abstraction;

		// cast the path as nested run
		m_CounterExamplePath = (NestedRun<CodeBlock, IPredicate>) m_Counterexample;

		// create an new interpolant automaton
		m_InterpolAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(
				m_NestedAbstraction.getAlphabet(), m_NestedAbstraction.getCallAlphabet(),
				m_NestedAbstraction.getReturnAlphabet(), m_NestedAbstraction.getStateFactory());

		// remember some properties
		m_InitialState = m_TraceChecker.getPrecondition();
		m_FinalState = m_TraceChecker.getPostcondition();
		m_PredicateUnifier = m_TraceChecker.getPredicateUnifier();
		m_Epimorphism = new AutomatonEpimorphism<>();

		String h = "";
		for(int i = 0; i < m_CounterExamplePath.getLength() - 1; i++)
		{
			h = h + "<[" + m_CounterExamplePath.getStateAtPosition(i) + "]>" 
					+ "--{" + m_CounterExamplePath.getSymbol(i).toString() + "}-->";
		}
		h = h + "[" + m_CounterExamplePath.getStateAtPosition(m_CounterExamplePath.getLength() - 1) + "]";
		m_ErrorPathHistory.add(h);

		// hold an iterable list of all states we added to the new automaton
		m_AddedStates = new ArrayList<IPredicate>();
		m_VisitedSingleEdges = new HashSet<Transitionlet<CodeBlock, IPredicate>>();
	
		// counter example components
		ArrayList<IPredicate> ce_states = m_CounterExamplePath.getStateSequence(); 
		NestedWord<CodeBlock> ce_edges = m_CounterExamplePath.getWord();
		IPredicate[] ce_interp = m_TraceChecker.getInterpolants();
		
		// -- initialize interpolant automaton --
		// add the initial state of the error path
		m_AddedStates.add(ce_states.get(0));
		m_InterpolAutomaton.addState(true, m_InitialState == m_FinalState, m_InitialState);
		m_Epimorphism.insert(ce_states.get(0), m_InitialState);
			
		// Add internal states of the error path
		addPath(ce_edges, ce_states, ce_interp, m_InitialState, m_FinalState);

		// add the final state of the error path
		m_AddedStates.add(ce_states.get(ce_states.size() - 1));
		m_InterpolAutomaton.addState(m_InitialState == m_FinalState, true, m_FinalState);
		m_Epimorphism.insert(ce_states.get(ce_states.size() - 1), m_FinalState);

		// Add the edges of the counter example to the visited edges
		//markEdgesAsVisited(ce_edges, ce_states);
		
		s_Logger.debug("States in the one-error-path-automaton:");
		for(int i = 0; i < m_AddedStates.size(); i++)
		{
			s_Logger.debug(i + ": " + m_AddedStates.get(i));	
		}
		
		s_Logger.debug("--- Try to add additional paths ---");
		// go through each state in the list of states as
		// starting point and find a path to any other annotated state
		// m_AddedStates will grow 
		for(int i = 0; i < m_AddedStates.size(); i++)
		{
			m_ActualStartingState = m_AddedStates.get(i);
			while(true)
			{
				// go through the automaton in depth first manner
				// this will fill m_ActualPath
				m_ActualPath = new ArrayList<IPredicate>(16);
				// remember the path, we follow
				m_ActualPath.add(m_ActualStartingState);
				s_Logger.debug("start with: " + m_ActualStartingState.toString());
				
				if(!explorePath(m_ActualStartingState, new NestedWord<CodeBlock>()))
				{
					s_Logger.debug("No more paths to explore.");
					break;
				}
			}
		}
		
		s_Logger.debug("Epimorphism:");
		m_Epimorphism.Print();
	}


	/**
	 * Explores all edges of a node.
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
	boolean explorePath(IPredicate s, NestedWord<CodeBlock> actualWord)
	{
		s_Logger.debug("Explore path: " + s.toString() + " wordLen: " + actualWord.length() + " pathLen: " + m_ActualPath.size());

		// Check if we have already been here. 
		// This prevents the addition of path-internal loops.
		// Do not check with the actual state, so self-loops are OK.
		for(int i = 0; i < m_ActualPath.size() - 1; i++)
		{
			if(s == m_ActualPath.get(i))
			{
				s_Logger.debug("The state is already in the path.");
				return false;
			}
		}

		/// there are three kinds of transitions: call, return, internal 
		// return transitions
		for(OutgoingReturnTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.returnSuccessors(s))
		{
			NestedWord<CodeBlock> newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.MINUS_INFINITY));
			// TODO
		}

		// calls transitions
		for(OutgoingCallTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.callSuccessors(s))
		{
			NestedWord<CodeBlock> newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.PLUS_INFINITY));
			// TODO
		}

		// nested transitions
		for(OutgoingInternalTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.internalSuccessors(s))
		{
			// TODO: !!! Add the equals method to the other kinds of transitions(OutgoingCallTransition, OutgoingReturnTransition) !!!
					
			// the next state is the target state of the edge
			IPredicate target = e.getSucc();
			
			// add the letter to the path
			NestedWord<CodeBlock> newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.INTERNAL_POSITION));			

			// try to add the target state of the edge (temporarily)
			// Do not forget to remove, when exiting loop and not exiting explorePath(...)!
			m_ActualPath.add(target);

			s_Logger.debug("Explore edge: " + e.toString() + " wordLen: " + newWord.length() + " pathLen: " + m_ActualPath.size());
					

			// if the target state is already added, we completed a path ...
			if(m_AddedStates.contains(target))
			{
				// ... except ...
				if(m_ActualPath.size() == 2)
				{
					// this can be a self-loop or an edge along two
					// states which are already added
					// in both cases we have to take care that we only 
					// consider this edge once
					if(m_VisitedSingleEdges.contains(e))
					{
						  s_Logger.debug("Edge was already visited.");
						  m_ActualPath.remove(m_ActualPath.size() - 1);
							continue;
					}
					m_VisitedSingleEdges.add(e);
//						if(m_ActualPath.get(0) != m_ActualPath.get(1))
//						{
//							// ... edge from state in the path to another
//							s_Logger.debug("Edge does belong to already existing path.");
//						}
//						else
//						{
//							// ... selfloop, this may be done once
//							s_Logger.debug("Mark edge as visited: " + e.toString());							
//						}
						
				}
				
				s_Logger.debug("Found an annotated state");
				IPredicate pre = m_Epimorphism.getMapping(m_ActualStartingState);
				IPredicate post = m_Epimorphism.getMapping(target);				
				s_Logger.debug("Try to add trace: " + pre.toString() + " :: " + newWord + " :: " + post);

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
					s_Logger.debug("Accepted");
					m_TraceChecker.computeInterpolants(new TraceChecker.AllIntegers(), m_PredicateUnifier, m_Pref.interpolation());

					addPath(newWord, m_ActualPath, m_TraceChecker.getInterpolants(), pre, post);
					return true;
				}		
				else
				{
					s_Logger.debug("Declined");
				}
			}
			else
			{
				// if not reached a state on the path, go further
				if(explorePath(target, newWord))
				{					
					return true;
				}
			}

			// remove the last element, since it did not work
			m_ActualPath.remove(m_ActualPath.size() - 1);
		}	

		// if no edge leads to complete an acceptable path
		// return false to try other edges before on the path
		return false;
	}

	
	/**
	 * Adds the path given from the trace checker.
	 * Assumes that the first and last state is already added.
	 * Adds edges 
	 * edges  states  interpolants
	 * 
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
		s_Logger.debug("Add path: numEdges:" + edges.length() + " numStates:" + states.size() + " numInterpol:" + interpolants.length);
		s_Logger.debug("edges:");
		for(int i = 0; i < edges.length(); i++) s_Logger.debug("<" + edges.getSymbol(i).toString() + ">"); 
		s_Logger.debug("states:");
		for(int i = 0; i < states.size(); i++) s_Logger.debug("<" + states.get(i).toString() + ">");
		s_Logger.debug("interp:");
		for(int i = 0; i < interpolants.length; i++) s_Logger.debug("<" + interpolants[i].toString() + ">"); 
		
		// add all edges 
		for(int i = 0; i < edges.length(); i++)
		{
			CodeBlock e = edges.getSymbolAt(i);
			IPredicate sourceS = states.get(i); 
			IPredicate targetS = states.get(i + 1); 

			IPredicate sourceI = (i == 0) ? pre : interpolants[i - 1];
			IPredicate targetI = (i == edges.length() - 1) ? post : interpolants[i];

			// Add all states in the sequence, but the first and last.
			if(i < edges.length() - 1)
			{
				// targetS can(may) not be in m_AddedStates 
				m_AddedStates.add(targetS);
				// since the interpolant formular might not be unique
				if(!m_InterpolAutomaton.getStates().contains(targetI))
				{
					m_InterpolAutomaton.addState(targetI == m_InitialState, targetI == m_FinalState, targetI);
				}
				m_Epimorphism.insert(targetS, targetI);
			}

			// add the respective edge into the abstraction automaton
			if(edges.isInternalPosition(i)) // TODO: check if this is doing what its meant to
			{
				boolean exists = false;
				if(!exists)
				{
					m_InterpolAutomaton.addInternalTransition(sourceI, e, targetI);
				}
			}
			else
			{
				if(edges.isCallPosition(i))
				{
					m_InterpolAutomaton.addCallTransition(sourceI, e, targetI);
				}
				else // isReturnPosition(i)
				{
					IPredicate hier = null; // TODO
					m_InterpolAutomaton.addReturnTransition(sourceI, hier, e, targetI);
				}
			}

			for(OutgoingInternalTransition<CodeBlock, IPredicate> t : m_NestedAbstraction.internalSuccessors(sourceS, e))
			{
				if(t.getSucc() == targetS)
				{
					m_VisitedSingleEdges.add(t);
				}
			}
			for(OutgoingCallTransition<CodeBlock, IPredicate> t : m_NestedAbstraction.callSuccessors(sourceS, e))
			{
				if(t.getSucc() == targetS)
				{
					m_VisitedSingleEdges.add(t);
				}
			}
			for(OutgoingReturnTransition<CodeBlock, IPredicate> t : m_NestedAbstraction.returnSuccessors(sourceS, e))
			{
				if(t.getSucc() == targetS)
				{
					m_VisitedSingleEdges.add(t);
				}
			}
		}
	}


//	/**
//	 * Takes a path of states and edges, marks all respective edges in the abstraction as visited
//	 * @param edges edges of the path in the abstraction automaton
//	 * @param states states of the path in the abstraction automaton
//	 */
//	private void markEdgesAsVisited(NestedWord<CodeBlock> edges,
//			ArrayList<IPredicate> states,
//			IPredicate source,
//			CodeBlock edge,
//			IPredicate target)
//	{
//		//s_Logger.debug("Mark path as visited; nofEdges: " + edges.length() + " nofStates: " + states.size());
//		for(int i = 0; i < edges.length(); i++)
//		{
//			for(OutgoingInternalTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.internalSuccessors(states.get(i), edges.getSymbolAt(i)))
//			{
//				if(e.getSucc() == states.get(i + 1))
//				{
//					m_VisitedSingleEdges.add(e);
//				}
//			}
//			for(OutgoingCallTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.callSuccessors(states.get(i), edges.getSymbolAt(i)))
//			{
//				if(e.getSucc() == states.get(i + 1))
//				{
//					m_VisitedSingleEdges.add(e);
//				}
//			}
//			for(OutgoingReturnTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.returnSuccessors(states.get(i), edges.getSymbolAt(i)))
//			{
//				if(e.getSucc() == states.get(i + 1))
//				{
//					m_VisitedSingleEdges.add(e);
//				}
//			}
//		}		
//	}

	
	/**
	 * Construct the new programm abstraction by subtraction the
	 * interpolant automaton from the abstraction
	 * 
	 * @return true if the trace of m_Counterexample (which was accepted by the
	 * 							old m_Abstraction) is not accepted by the m_Abstraction.
	 * @throws AutomataLibraryException 
	 */
	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException
	{

		SuperDifference<CodeBlock, IPredicate> diff = new SuperDifference<CodeBlock, IPredicate>(
				m_NestedAbstraction, m_InterpolAutomaton, m_Epimorphism, false);

		m_Abstraction = diff.getResult();

		s_Logger.debug("Actualized abstraction.");

		s_Logger.debug("ERROR_PATH_HISTORY");
		for(int i = 0; i < m_ErrorPathHistory.size(); i++)
		{
			s_Logger.debug("[" + i + "]: " + m_ErrorPathHistory.get(i));
		}
		
		s_Logger.debug("");

		//		if (m_Pref.minimize())
		//		{
		//			m_ContentFactory.refinementOperationFinished();
		//			diff.removeStatesThatCanNotReachFinal(true);
		//			removedDoubleDeckers = diff.getRemovedDoubleDeckers();
		//			context2entry = diff.getCallSuccOfRemovedDown();
		//		}

		if (m_BiggestAbstractionSize < m_NestedAbstraction.size()) {
			m_BiggestAbstractionSize = m_NestedAbstraction.size();
			m_BiggestAbstractionIteration = m_Iteration;
		}

		s_Logger.info("Abstraction has " + m_NestedAbstraction.sizeInformation());
		s_Logger.info("Interpolant automaton has "
				+ m_InterpolAutomaton.sizeInformation());

		//MinimizeAbstraction();
		
		return true;
	}

	
	
	
	/**
	 * Minimizes the actual abstraction automaton
	 * @throws AutomataLibraryException 
	 */
	void MinimizeAbstraction() throws AutomataLibraryException
	{
		// TODO: move this function to basic cegar loop and replace 
		//       its columns from #123 to #1234 with a function call to this
		s_Logger.debug("Minimize Automaton.");
		int oldSize = m_Abstraction.size();
		
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction =
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		Collection<Set<IPredicate>> partition = computePartition(newAbstraction);
		boolean shrinkNwa = m_Pref.cutOffRequiresSameTransition();
		
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimized;
		if (shrinkNwa) 
		{
			ShrinkNwa<CodeBlock, IPredicate> minimizeOp = new ShrinkNwa<CodeBlock, IPredicate>(
					newAbstraction, partition, m_StateFactoryForRefinement, true, false, false, 200, false, 0, false, false);
			assert minimizeOp.checkResult(m_Abstraction.getStateFactory());
			minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(minimizeOp.getResult())).getResult();
			if (m_Pref.computeHoareAnnotation()) 
			{
				Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
				m_Haf.updateOnMinimization(oldState2newState, minimized);			
			}
		} 
		else 
		{
			MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = new MinimizeSevpa<CodeBlock, IPredicate>(newAbstraction, partition, false, false, m_StateFactoryForRefinement);
			assert minimizeOp.checkResult(m_Abstraction.getStateFactory());
			minimized = minimizeOp.getResult();
			if (m_Pref.computeHoareAnnotation()) 
			{
				Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
				m_Haf.updateOnMinimization(oldState2newState, minimized);
			}
		}
		int newSize = minimized.size();
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
