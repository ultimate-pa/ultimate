/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.SuperDifference;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
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
	protected ArrayList<IPredicate> m_AnnotatedStates;
	
	/**
	 * Holds the nodes and edges of the error path
	 */
	protected NestedRun<CodeBlock, IPredicate> m_CounterExamplePath;

	/**
	 * Used for computing the interpolants of additional paths
	 */
	protected TraceChecker m_ExtraTraceChecker;

	/**
	 * Version of the abstraction, casted as
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

	/***
	 * Precondition of the actual search, corresponds to the actual
	 * starting state.
	 */
	protected IPredicate m_ActualPrecondition;
	
	/**
	 * When adding additional sub paths to the interpolant automaton
	 * This will hold the actual path.
	 */
	protected ArrayList<IPredicate> m_ActualPath;
		
	/**
	 * Points to the initial state of the abstraction, i.e. true
	 */
	protected IPredicate m_AbstractionInitialState;

	/**
	 * Points to the final state of the abstraction, i.e. false
	 */
	protected IPredicate m_AbstractionFinalState;

	/**
	 * This is used to merge states
	 */
	protected PredicateUnifier m_PredicateUnifier;

	
	/// ------- debugging -------
	/**
	 * Holds the error paths, for debbuging.
	 */
	private ArrayList<String> m_ErrorPathHistory;


	
	/**
	 * Create and initialize Cegar-Loop.
	 * @param name
	 * @param rootNode
	 * @param smtManager
	 * @param timingStatistics
	 * @param taPrefs
	 * @param errorLocs
	 */
	public CegarLoopSequentialWithBackedges(String name, RootNode rootNode,
			SmtManager smtManager, TraceAbstractionBenchmarks timingStatistics,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs,
			INTERPOLATION interpolation, boolean computeHoareAnnotation)
	{
		super(name, rootNode, smtManager, timingStatistics, taPrefs, errorLocs,
				interpolation, computeHoareAnnotation);
		m_ErrorPathHistory = new ArrayList<String>(); 	
	}


	/**
	 * constructs the interpolant automaton.
	 */
	@Override
	protected void constructInterpolantAutomaton()
	{
		s_Logger.debug("Start constructing interpolant automaton.");
		
		// cast the abstraction automaton as nested word automaton
		m_NestedAbstraction = (INestedWordAutomaton<CodeBlock, IPredicate>)m_Abstraction;

		// cast the path as nested run
		m_CounterExamplePath = (NestedRun<CodeBlock, IPredicate>) m_Counterexample;

		// create an new interpolant automaton
		m_InterpolAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(
				m_NestedAbstraction.getAlphabet(), m_NestedAbstraction.getCallAlphabet(),
				m_NestedAbstraction.getReturnAlphabet(), m_NestedAbstraction.getStateFactory());

		// remember some of its properties
		m_AbstractionInitialState = m_TraceChecker.getPrecondition();
		m_AbstractionFinalState = m_TraceChecker.getPostcondition();
		m_PredicateUnifier = m_TraceChecker.getPredicateUnifier();
		m_Epimorphism = new AutomatonEpimorphism<>();

		
		/// debugging
		{
			String h = "";
			for(int i = 0; i < m_CounterExamplePath.getLength() - 1; i++)
			{
				h = h + "<[" + m_CounterExamplePath.getStateAtPosition(i) + "]>" 
						+ "--{" + m_CounterExamplePath.getSymbol(i).toString() + "}-->";
			}
			h = h + "[" + m_CounterExamplePath.getStateAtPosition(m_CounterExamplePath.getLength() - 1) + "]";
			m_ErrorPathHistory.add(h);
		}

		// hold an iterable list of all states we added to the new automaton
		m_AnnotatedStates = new ArrayList<IPredicate>();
			
		// counter example components
		ArrayList<IPredicate> ce_states = m_CounterExamplePath.getStateSequence(); 
		NestedWord<CodeBlock> ce_edges = m_CounterExamplePath.getWord();
		IPredicate[] ce_interp = m_TraceChecker.getInterpolants();
		
		// -- initialize interpolant automaton --
		// add the initial state of the error path
		m_AnnotatedStates.add(ce_states.get(0));
		m_InterpolAutomaton.addState(true, m_AbstractionInitialState == m_AbstractionFinalState, m_AbstractionInitialState);
		m_Epimorphism.insert(ce_states.get(0), m_AbstractionInitialState);
			
		// Add internal states of the error path
		addPath(ce_edges, ce_states, ce_interp, m_AbstractionInitialState, m_AbstractionFinalState);

		// add the final state of the error path
		if(m_AnnotatedStates.contains(ce_states.get(ce_states.size() - 1))) throw new Error();
		m_AnnotatedStates.add(ce_states.get(ce_states.size() - 1));
		if(!m_InterpolAutomaton.getStates().contains(m_AbstractionFinalState))
		{
			m_InterpolAutomaton.addState(m_AbstractionInitialState == m_AbstractionFinalState, true, m_AbstractionFinalState);
		}
		m_Epimorphism.insert(ce_states.get(ce_states.size() - 1), m_AbstractionFinalState);

		/// debugging
		{
			s_Logger.debug("States in the one-error-path-automaton:");
			for(int i = 0; i < m_AnnotatedStates.size(); i++)
			{
				s_Logger.debug(i + ": " + m_AnnotatedStates.get(i));	
			}
		}
		
		s_Logger.debug("--- Try to add additional paths ---");
		// go through each state in the list of states as
		// starting point and find a path to any other annotated state
		// m_AddedStates will grow 
		for(int i = 0; i < m_AnnotatedStates.size(); i++)
		{
			m_ActualStartingState = m_AnnotatedStates.get(i);
			
			s_Logger.debug("Start with: " + m_ActualStartingState.toString());
			
			m_ActualPrecondition = m_Epimorphism.getMapping(m_ActualStartingState);
			
			// return transitions
			for(OutgoingReturnTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.returnSuccessors(m_ActualStartingState))
			{
				// the next state is the target state of the edge
				IPredicate target = e.getSucc();
				
  			exploreInitialEdge(e, target, new NestedWord<CodeBlock>(e.getLetter(), NestedWord.MINUS_INFINITY));
			}

			// calls transitions
			for(OutgoingCallTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.callSuccessors(m_ActualStartingState))
			{
				// the next state is the target state of the edge
				IPredicate target = e.getSucc();
				
  			exploreInitialEdge(e, target, new NestedWord<CodeBlock>(e.getLetter(), NestedWord.PLUS_INFINITY));
			}
			
			// start the depth first search procedure for every state edge going out from the
			// actual starting state, ignoring if a path was find or not (i.e. the return value of exploreState)
			for(OutgoingInternalTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.internalSuccessors(m_ActualStartingState))
			{
				// the next state is the target state of the edge
				IPredicate target = e.getSucc();
				
  			exploreInitialEdge(e, target, new NestedWord<CodeBlock>(e.getLetter(), NestedWord.INTERNAL_POSITION));
			}
		}
		
		s_Logger.debug("Epimorphism:");
		m_Epimorphism.Print();
	}

	
	/**
	 * Explore the first edge. If we can already reach an annotated state
	 * we must check if the edge is already in one of the added paths. 
	 * 
	 * @param e The edge to be taken (firstly)
	 * @param target The target of the edge
	 * @param initialWord Word consisting of the label of the edge
	 */
	private void exploreInitialEdge(
			Transitionlet<CodeBlock, IPredicate> e, 
			IPredicate target,
			NestedWord<CodeBlock> initialWord)
	{
		m_ActualPath = new ArrayList<IPredicate>(16);
		// remember the path, we follow
		m_ActualPath.add(m_ActualStartingState);
		m_ActualPath.add(target);
		
		//s_Logger.debug("Explore primary edge: " + e.toString() + " wordLen: " + initialWord.length() + " pathLen: " + m_ActualPath.size());
		
		// check if the edge points to an already annotated state
		// if the target state is already added, we completed a path ...
		if(m_AnnotatedStates.contains(target))
		{
			s_Logger.debug("Found an annotated state.");
			// check if this is an edge which is already in the automaton
			if(!m_InterpolAutomaton.succInternal(m_Epimorphism.getMapping(m_ActualStartingState), e.getLetter()).contains(m_Epimorphism.getMapping(target)))
			{
				// we have either a self-loop or another separate edge			
				checkAndAddPath(initialWord, m_ActualPrecondition, m_Epimorphism.getMapping(target));
			} 		
		}
		else
		{
			exploreState(target, initialWord);					
		}
	}

		
	/**
	 * Explores all edges of a node.
	 * If it completes a path feed out:
	 * 	- If the path was accepted by the interpolant generator
	 * 		add the states to the new interpolant automaton
	 *  - If the path was not accepted
	 *    just go back and try other paths.
	 * @param s Actual state of the algorithm, initially: starting state
	 * @param actualWord Labels of the edges of the actual path
	 * @return True if path was found, false if there is no path with suitable interpolants found
	 */
	private boolean exploreState(IPredicate s, NestedWord<CodeBlock> actualWord)
	{	
		//s_Logger.debug("Explore path: " + s.toString() + " wordLen: " + actualWord.length() + " pathLen: " + m_ActualPath.size());
		
		// Check if we have already been here. 
		// This prevents the addition of path-internal loops.
		// Do not check with the actual state, so self-loops are OK.
		for(int i = 0; i < m_ActualPath.size() - 1; i++)
		{
			if(s == m_ActualPath.get(i))
			{
				//s_Logger.debug("The state is already in the path.");
				return false;
			}
		}

		/// there are three kinds of transitions: call, return, internal 
		// return transitions
		for(OutgoingReturnTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.returnSuccessors(s))
		{				
			// add the letter to the path and explore edge
			if(exploreEdge(e, e.getSucc(), actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.MINUS_INFINITY))))
			{
				return true;
			}
		}

		// calls transitions
		for(OutgoingCallTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.callSuccessors(s))
		{
			if(exploreEdge(e, e.getSucc(), actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.PLUS_INFINITY))))
			{
				return true;
			}
		}

		// nested transitions
		for(OutgoingInternalTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.internalSuccessors(s))
		{
			// add the letter to the path and explore edge
			if(exploreEdge(e, e.getSucc(), actualWord.concatenate(new NestedWord<CodeBlock>(e.getLetter(), NestedWord.INTERNAL_POSITION))))
			{
				return true;
			}
		}	
		// if no edge leads to complete an acceptable path
		// return false to try other edges before on the path
		return false;
	}


/**
 * Explore an edge in depth first manner, 
 * @param e The last edge and the actual edge to explore
 * @param target The target state of the edge
 * @param newWord The word, which was collected on the edges along the path
 * @return True if a path back to an annotated state was found, which can be annotated with interpolants
 */
	private boolean exploreEdge(
			Transitionlet<CodeBlock, IPredicate> e,
			IPredicate target,
			NestedWord<CodeBlock> newWord)
	{		
		// Try to add the target state of the edge (temporarily).
		// Do not forget to remove it, when exiting loop and not exiting explorePath(...)!
		m_ActualPath.add(target);

		//s_Logger.debug("Explore edge: " + e.toString() + " wordLen: " + newWord.length() + " pathLen: " + m_ActualPath.size());					

		// if the target state is already added, we completed a path ...
		if(m_AnnotatedStates.contains(target))
		{
			s_Logger.debug("Found an annotated state");
			IPredicate pre = m_Epimorphism.getMapping(m_ActualStartingState);
			IPredicate post = m_Epimorphism.getMapping(target);				
			
			if(checkAndAddPath(newWord, pre, post))
			{
				return true; // (instead of removing the last state from the path, 
										 // it will be reset inconstructInterpolantAutomaton)
			}
		}
		else
		{
			// if not reached a state on the path, go further
			if(exploreState(target, newWord))
			{					
				return true; // (instead of removing the last state from the path, 
										 // it will be reset inconstructInterpolantAutomaton)
			}
		}

		// remove the last element, since it did not "work"
		m_ActualPath.remove(m_ActualPath.size() - 1);
		
		return false;
	}


	/**
	 * Check if the actual path is feasible to add into the interpolant
	 * automaton and return true if it was possible. 
	 * @param word the edges along the path 
	 * @param pre the precondition of the path
	 * @param post the postcondition of the path
	 * @return true if interpolants were found
	 */
	private boolean checkAndAddPath(NestedWord<CodeBlock> word, IPredicate pre, IPredicate post)
	{
		//s_Logger.debug("Try to add trace: " + pre.toString() + " :: " + word + " :: " + post);

		// test if we found a new path which can be added ...
		m_TraceChecker = new TraceChecker(
				pre,
				post, 
				null, //TODO 
				word,
				m_SmtManager, 
				m_RootNode.getRootAnnot().getModGlobVarManager());

		if(m_TraceChecker.isCorrect() == LBool.UNSAT)
		{
			s_Logger.debug("Accepted");
			m_TraceChecker.computeInterpolants(new TraceChecker.AllIntegers(), m_PredicateUnifier, m_Pref.interpolation());
			
			addPath(word, m_ActualPath, m_TraceChecker.getInterpolants(), pre, post);
			return true;
		}		
		else
		{
			s_Logger.debug("Declined");
			m_TraceChecker.finishTraceCheckWithoutInterpolantsOrProgramExecution();
			return false;
		}
	}


	/**
	 * Adds the path given from the trace checker.
	 * Assumes that the first and last state is already added.
	 * Adds edges 
	 * edges  states  interpolants
	 * 
	 *          s0       <pre>
	 *   e0 
	 *          s1       I0
	 *   e1
	 *          s2       I1
	 *   e2 
	 *          s3       <post>
	 * @param edges Contains the edges along the path
	 * @param states Holds all states (0, ..., n-1)
	 * @param interpolants The interpolants along the path for the states 1, ..., n-2
	 * @param pre the formula for the state 0
	 * @param post the formula for the state n-1
	 */
	private void addPath(
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
			IPredicate targetS = states.get(i + 1); 

			IPredicate sourceI = (i == 0) ? pre : interpolants[i - 1];
			IPredicate targetI = (i == edges.length() - 1) ? post : interpolants[i];

			// Add all states in the sequence, but the first and last.
			if(i < edges.length() - 1)
			{
				// targetS can(may) not be in m_AddedStates 
				m_AnnotatedStates.add(targetS);
				// since the interpolant formula might not be unique
				if(!m_InterpolAutomaton.getStates().contains(targetI))
				{
					m_InterpolAutomaton.addState(targetI == m_AbstractionInitialState, targetI == m_AbstractionFinalState, targetI);
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
		}
	}

	
	/**
	 * Construct the new program abstraction by subtraction the
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

		if (m_BiggestAbstractionSize < m_NestedAbstraction.size())
		{
			m_BiggestAbstractionSize = m_NestedAbstraction.size();
			m_BiggestAbstractionIteration = m_Iteration;
		}

		s_Logger.info("Abstraction has " + m_NestedAbstraction.sizeInformation());
		s_Logger.info("Interpolant automaton has "
				+ m_InterpolAutomaton.sizeInformation());
		
		Minimization minimization = m_Pref.minimize();
		switch (minimization) {
		case NONE:
			break;
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			s_Logger.debug("Minimizing interpolant automaton.");

			RemoveUnreachable<CodeBlock, IPredicate> removeUnreachable = new RemoveUnreachable<CodeBlock, IPredicate>((INestedWordAutomatonSimple<CodeBlock, IPredicate>) m_Abstraction); 
			m_Abstraction = removeUnreachable.getResult();
			
			RemoveDeadEnds<CodeBlock, IPredicate> removeDeadEnds = new RemoveDeadEnds<CodeBlock, IPredicate>((INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction);
			m_Abstraction = removeDeadEnds.getResult();
					
			minimizeAbstraction(m_StateFactoryForRefinement, m_PredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}
		
		return true;
	}
}
