/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
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
public class CegarLoopSWBnonRecursive extends BasicCegarLoop
{
	/**
	 * Maps states from the original automaton to corresponding states in the new
	 * interpolant automaton.
	 */
	protected AutomatonEpimorphism<IPredicate> m_Epimorphism;

	/**
	 * List of states we already added to the new interpolant automaton.
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
	 * Version of the abstraction, casted as NestedWordAutomaton. It is casted in
	 * every call of constructInterpolantAutomaton.
	 */
	private INestedWordAutomaton<CodeBlock, IPredicate> m_NestedAbstraction;

	/**
	 * Version of the abstraction, castet as DoubleDeckerAutomaton. Must be castet
	 * in every call of constructInterpolantAutomaton
	 */
	private IDoubleDeckerAutomaton<CodeBlock, IPredicate> m_DoubleDeckerAbstraction;

	/**
	 * When adding additional sub paths to the interpolant automaton. We always
	 * start from a state which is already added. This holds that starting point.
	 */
	protected IPredicate m_ActualStartingState;

	/***
	 * Precondition of the actual search, corresponds to the actual starting
	 * state.
	 */
	protected IPredicate m_ActualPrecondition;

	/**
	 * When adding additional sub paths to the interpolant automaton This will
	 * hold the actual path.
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

	/**
	 * Count how many paths other than the initial path
	 * have been added in the actual iteration.
	 */
	protected int m_nofAdditionalPaths;
	
	/**
	 * Counts how many paths have been explored, but could not be added.
	 */
	protected int m_nofDeclinedPaths;
	
	// / ------- debugging -------
	/**
	 * Holds the error paths, for debbuging.
	 */
	private ArrayList<String> m_ErrorPathHistory;

	// private int m_nofVisitedCalls;
	// private int m_nofVisitedReturns;

	/**
	 * Create and initialize Cegar-Loop.
	 * 
	 * @param name
	 * @param rootNode
	 * @param smtManager
	 * @param traceAbstractionBenchmarks
	 * @param taPrefs
	 * @param errorLocs
	 * @param interpolation
	 * @param computeHoareAnnotation
	 */
	public CegarLoopSWBnonRecursive(String name, RootNode rootNode,
			SmtManager smtManager,
			TraceAbstractionBenchmarks traceAbstractionBenchmarks,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs,
			INTERPOLATION interpolation, boolean computeHoareAnnotation)
	{
		super(name, rootNode, smtManager, taPrefs, errorLocs,
				interpolation, computeHoareAnnotation);
		m_ErrorPathHistory = new ArrayList<String>();
	}

	/**
	 * constructs the interpolant automaton.
	 * 
	 * @throws OperationCanceledException
	 */
	@Override
	protected void constructInterpolantAutomaton()
			throws OperationCanceledException
	{
		s_Logger.debug("Start constructing interpolant automaton.");

		m_nofAdditionalPaths = 0;
		m_nofDeclinedPaths = 0;
		
		// cast the abstraction automaton as nested word and double decker automaton
		m_NestedAbstraction = (INestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction;

		m_DoubleDeckerAbstraction = (new RemoveUnreachable<CodeBlock, IPredicate>(
				(INestedWordAutomatonSimple<CodeBlock, IPredicate>) m_Abstraction))
				.getResult();
		// (IDoubleDeckerAutomaton<CodeBlock, IPredicate>) m_Abstraction.get;

		// cast the path as nested run
		m_CounterExamplePath = (NestedRun<CodeBlock, IPredicate>) m_Counterexample;

		// create an new interpolant automaton
		m_InterpolAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(
				m_NestedAbstraction.getAlphabet(),
				m_NestedAbstraction.getCallAlphabet(),
				m_NestedAbstraction.getReturnAlphabet(),
				m_NestedAbstraction.getStateFactory());

		// remember some of its properties
		m_AbstractionInitialState = m_TraceChecker.getPrecondition();
		m_AbstractionFinalState = m_TraceChecker.getPostcondition();
		m_PredicateUnifier = m_TraceChecker.getPredicateUnifier();
		m_Epimorphism = new AutomatonEpimorphism<>();

		// / debugging
		{
			String h = "";
			for (int i = 0; i < m_CounterExamplePath.getLength() - 1; i++)
			{
				h = h + "<[" + m_CounterExamplePath.getStateAtPosition(i) + "]>"
						+ "--{" + m_CounterExamplePath.getSymbol(i).toString() + "}-->";
			}
			h = h
					+ "["
					+ m_CounterExamplePath.getStateAtPosition(m_CounterExamplePath
							.getLength() - 1) + "]";
			m_ErrorPathHistory.add(h);
		}

		// hold an iterable list of all states we added to the new automaton
		m_AnnotatedStates = new ArrayList<IPredicate>();

		// counter example components
		ArrayList<IPredicate> ce_states = m_CounterExamplePath.getStateSequence();
		NestedWord<CodeBlock> ce_edges = m_CounterExamplePath.getWord();
		IPredicate[] ce_interp = m_TraceChecker.getInterpolants();

		// -- initialize interpolant automaton --
		// Add the initial state of the error path
		s_Logger.debug("Add the initial state of the error path");
		m_AnnotatedStates.add(ce_states.get(0));
		m_InterpolAutomaton.addState(true,
				m_AbstractionInitialState == m_AbstractionFinalState,
				m_AbstractionInitialState);
		m_Epimorphism.insert(ce_states.get(0), m_AbstractionInitialState);

		// ichadd the final state of the error path
		s_Logger.debug("add the final state of the error path");
		if (m_AnnotatedStates.contains(ce_states.get(ce_states.size() - 1)))
			throw new Error();
		m_AnnotatedStates.add(ce_states.get(ce_states.size() - 1));
		if (!m_InterpolAutomaton.getStates().contains(m_AbstractionFinalState))
		{
			m_InterpolAutomaton.addState(
					m_AbstractionInitialState == m_AbstractionFinalState, true,
					m_AbstractionFinalState);
		}
		m_Epimorphism.insert(ce_states.get(ce_states.size() - 1),
				m_AbstractionFinalState);
			
		// Add internal states of the error path
		s_Logger.debug("Add internal states and edges of the error path");
		addPath(ce_edges, ce_states, ce_interp, m_AbstractionInitialState,
				m_AbstractionFinalState, new TreeMap<Integer, IPredicate>());
		
		// // debugging
		{
			s_Logger.debug("States in the one-error-path-automaton:");
			for (int i = 0; i < m_AnnotatedStates.size(); i++)
			{
				s_Logger.debug(i + ": " + m_AnnotatedStates.get(i));
			}
		}

		// -- Try to add additional paths --
		s_Logger.debug("--- Try to add additional paths ---");
		// go through each state in the list of states as
		// starting point and find a path to any other annotated state
		// m_AddedStates will grow
		for (int i = 0; i < m_AnnotatedStates.size(); i++)
		{
			m_ActualStartingState = m_AnnotatedStates.get(i);

			s_Logger.debug("Start with: " + m_ActualStartingState.toString());

			m_ActualPrecondition = m_Epimorphism.getMapping(m_ActualStartingState);

			// return transitions
			for (IPredicate hier : m_DoubleDeckerAbstraction.getDownStates(m_ActualStartingState))
			{
				// if we did not annotate the hierarchical predecessor we cannot test
				// the path yet
				// so we just do not
				if (m_AnnotatedStates.contains(hier))
				{
					for (OutgoingReturnTransition<CodeBlock, IPredicate> e : m_NestedAbstraction.returnSuccessorsGivenHier(m_ActualStartingState, hier))
					{
						// the next state is the target state of the edge
						IPredicate target = e.getSucc();
						exploreInitialEdge(e, target, new NestedWord<CodeBlock>(e.getLetter(), NestedWord.MINUS_INFINITY));
					}
				}
			}

			// calls transitions
			for (OutgoingCallTransition<CodeBlock, IPredicate> e : m_NestedAbstraction
					.callSuccessors(m_ActualStartingState))
			{
				// the next state is the target state of the edge
				IPredicate target = e.getSucc();
				exploreInitialEdge(e, target, new NestedWord<CodeBlock>(e.getLetter(), NestedWord.PLUS_INFINITY));
			}

			// start the depth first search procedure for every state edge going out
			// from the
			// actual starting state, ignoring if a path was find or not (i.e. the
			// return value of exploreState)
			for (OutgoingInternalTransition<CodeBlock, IPredicate> e : m_NestedAbstraction
					.internalSuccessors(m_ActualStartingState))
			{
				// the next state is the target state of the edge
				IPredicate target = e.getSucc();

				exploreInitialEdge(e, target, new NestedWord<CodeBlock>(e.getLetter(),
						NestedWord.INTERNAL_POSITION));
			}
		}

		s_Logger.info("Explored paths: " + (m_nofDeclinedPaths + m_nofAdditionalPaths));
		s_Logger.info("Added paths   : " + m_nofAdditionalPaths);
		s_Logger.info("Declined paths: " + m_nofDeclinedPaths);
		//s_Logger.debug("Epimorphism:");
		//m_Epimorphism.Print();
		
		assert (m_SmtManager.checkInductivity(m_InterpolAutomaton, false, true)) : "Not inductive";
	}

	/**
	 * Explore the first edge. If we can already reach an annotated state we must
	 * check if the edge is already in one of the added paths.
	 * 
	 * @param e
	 *          The edge to be taken (firstly)
	 * @param target
	 *          The target of the edge
	 * @param initialWord
	 *          Word consisting of the label of the edge
	 */
	private void exploreInitialEdge(Transitionlet<CodeBlock, IPredicate> e,
			IPredicate target, NestedWord<CodeBlock> initialWord)
	{
		m_ActualPath = new ArrayList<IPredicate>(16);
		// remember the path, we follow
		m_ActualPath.add(m_ActualStartingState);
		m_ActualPath.add(target);

		// s_Logger.debug("Explore primary edge: " + e.toString() + " wordLen: " +
		// initialWord.length() + " pathLen: " + m_ActualPath.size());

		// check if the edge points to an already annotated state
		// if the target state is already added, we completed a path ...
		if (m_AnnotatedStates.contains(target))
		{
			s_Logger.debug("Found an annotated state.");
			// check if this is an edge which is already in the automaton
			if (!m_InterpolAutomaton.succInternal(
					m_Epimorphism.getMapping(m_ActualStartingState), e.getLetter())
					.contains(m_Epimorphism.getMapping(target)))
			{
				// we have either a self-loop or another separate edge
				checkAndAddPath(initialWord, m_ActualPrecondition,
						m_Epimorphism.getMapping(target));
			}
		}
		else
		{
			exploreState(target, initialWord);
		}
	}

	// Variable stacks to emulate recursion
	private ArrayList<IPredicate> m_StackState;
	private ArrayList<Integer> m_StackEdgeType;
	private ArrayList<Iterator<Transitionlet<CodeBlock, IPredicate>>> m_StackIterator;
	private ArrayList<Iterator<IPredicate>> m_StackHier;
	private ArrayList<NestedWord<CodeBlock>> m_StackWord;

	/**
	 * Explores all edges of a node. If it completes a path feed out: - If the
	 * path was accepted by the interpolant generator add the states to the new
	 * interpolant automaton - If the path was not accepted just go back and try
	 * other paths.
	 * 
	 * @param state
	 *          Actual state of the algorithm, initially: starting state
	 * @param word
	 *          Labels of the edges of the actual path
	 * @param actualPath
	 *          List of the states of the actual path
	 */
	@SuppressWarnings("unchecked")
	private void exploreState(IPredicate state, NestedWord<CodeBlock> word)
	{
		s_Logger.debug("Explore path: " + state.toString() + " wordLen: "
				+ word.length() + " pathLen: " + m_ActualPath.size());
		m_StackState = new ArrayList<IPredicate>();
		m_StackIterator = new ArrayList<Iterator<Transitionlet<CodeBlock, IPredicate>>>();
		m_StackEdgeType = new ArrayList<Integer>();
		m_StackHier = new ArrayList<Iterator<IPredicate>>();
		m_StackWord = new ArrayList<NestedWord<CodeBlock>>();

		// determins if we found a path, then we back off
		IPredicate s = state;
		// hierarchical predecessors
		Iterator<IPredicate> hierPreds = null;
		@SuppressWarnings("rawtypes")
		Iterator iter = m_NestedAbstraction.internalSuccessors(s).iterator();
		Integer edgeType = 0;
		NestedWord<CodeBlock> actualWord = word;

		while (true)
		{
			s_Logger.debug("iterate: " + s.toString() + " wordLen: "
					+ actualWord.length() + " pathLen: " + m_ActualPath.size());

			// check if there is another undiscovered edge
			if (!iter.hasNext())
			{
				edgeType++;
				switch (edgeType)
				{
					case 1:
						if (hierPreds == null)
						{
							// if we have not looked at the hierarchical predecessors yet
							hierPreds = m_DoubleDeckerAbstraction.getDownStates(s).iterator();
						}
						if (hierPreds.hasNext())
						{
							IPredicate hier = hierPreds.next();
							if (m_AnnotatedStates.contains(hier))
							{
								s_Logger.debug("iterate through hier" + hier.toString());
								iter = m_NestedAbstraction.returnSuccessorsGivenHier(s, hier).iterator();
								edgeType = 0; // there might still be hierPreds left								
							}
							else
							{
								continue;
							}
						}
						else
						{
							// if we gone through all hierPreds we set to null for the next
							// iteration
							hierPreds = null;
							continue;
						}
					case 2:
						iter = m_NestedAbstraction.callSuccessors(s).iterator();
						continue;
					case 3:
						// go back
						int index = m_StackState.size() - 1;
						if (index < 0)
						{
							// no state to go back, we explored everything
							return;
						}
						s = m_StackState.get(index);
						hierPreds = m_StackHier.get(index);
						iter = m_StackIterator.get(index);
						edgeType = m_StackEdgeType.get(index);
						actualWord = m_StackWord.get(index);
						m_StackState.remove(index);
						m_StackHier.remove(index);
						m_StackIterator.remove(index);
						m_StackEdgeType.remove(index);
						m_StackWord.remove(index);
						// remove the last element, since it did not "work"
						m_ActualPath.remove(m_ActualPath.size() - 1);
						continue;
				}
			}

			// obtain the next edge
			// and add the letter to the path and explore edge
			IPredicate target;
			NestedWord<CodeBlock> newWord;
			switch (edgeType)
			{
				case 0:
					OutgoingInternalTransition<CodeBlock, IPredicate> e_int = (OutgoingInternalTransition<CodeBlock, IPredicate>) iter.next();
					target = e_int.getSucc();
					newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e_int.getLetter(), NestedWord.INTERNAL_POSITION));
					break;
				case 1:
					OutgoingReturnTransition<CodeBlock, IPredicate> e_out = (OutgoingReturnTransition<CodeBlock, IPredicate>) iter.next();
					target = e_out.getSucc();
					newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e_out.getLetter(), NestedWord.MINUS_INFINITY));
					break;
				case 2:
					OutgoingCallTransition<CodeBlock, IPredicate> e_ret = (OutgoingCallTransition<CodeBlock, IPredicate>) iter.next();
					target = e_ret.getSucc();
					newWord = actualWord.concatenate(new NestedWord<CodeBlock>(e_ret.getLetter(), NestedWord.PLUS_INFINITY));
					break;
				default:
					throw new Error();
			}

			// Check if we have already been here.
			// This prevents the addition of path-internal loops.
			// Do not check with the actual state, so self-loops are OK.
			boolean ignoreEdge = false;
			for (int i = 0; i < m_ActualPath.size() - 1; i++)
			{
				if (s == m_ActualPath.get(i))
				{
					ignoreEdge = true;
					break;
				}
			}
			if (ignoreEdge)
				continue;

			// Try to add the target state of the edge (temporarily).
			// Do not forget to remove it, when exiting loop and not exiting
			// explorePath(...)!
			m_ActualPath.add(target);

			// if the target state is already added, we completed a path ...
			if (m_AnnotatedStates.contains(target))
			{
				s_Logger.debug("Found an annotated state");
				IPredicate pre = m_Epimorphism.getMapping(m_ActualStartingState);
				IPredicate post = m_Epimorphism.getMapping(target);

				if (checkAndAddPath(newWord, pre, post))
				{
					// If we found a path, we can stop the search here, we will
					// return soon, bc the actual state was added in m_annotatedStates
					return;
				}

				// remove the last element, since it did not "work"
				m_ActualPath.remove(m_ActualPath.size() - 1);
			} else
			{
				// if not reached a state on the path, go further
				// save actual state on the stack
				m_StackState.add(s);
				m_StackHier.add(hierPreds);
				m_StackIterator.add(iter);
				m_StackEdgeType.add(edgeType);
				m_StackWord.add(actualWord);
				s = target;
				iter = m_NestedAbstraction.internalSuccessors(target).iterator();
				edgeType = 0;
				actualWord = newWord;
			}
		}
	}

	/**
	 * Check if the actual path is feasible to add into the interpolant automaton
	 * and return true if it was possible.
	 * 
	 * @param word
	 *          the edges along the path
	 * @param pre
	 *          the precondition of the path
	 * @param post
	 *          the postcondition of the path
	 * @return true if interpolants were found
	 */
	private boolean checkAndAddPath(NestedWord<CodeBlock> word, IPredicate pre, IPredicate post)
	{
		s_Logger.debug("Try to add trace: " + pre.toString() + " -- " + word + " --> " + post);

		SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<Integer, IPredicate>();
		for(Entry<Integer, CodeBlock> e : word.getPendingReturns().entrySet())
		{
			int pos = e.getKey();
			IPredicate target = m_ActualPath.get(pos + 1);
			for(IncomingReturnTransition<CodeBlock, IPredicate> irt : m_NestedAbstraction.returnPredecessors(word.getSymbolAt(pos), target))
			{
				if(irt.getLinPred() == m_ActualPath.get(pos))
				{
					IPredicate interp = m_Epimorphism.getMapping(irt.getHierPred());
					pendingContexts.put(pos, interp);
				}
			}
		}
		
		// test if we found a new path which can be added
		m_TraceChecker = new TraceChecker(
				pre,
				post, 
				pendingContexts, 
				word,
				m_SmtManager, 
				m_RootNode.getRootAnnot().getModGlobVarManager());

		if(m_TraceChecker.isCorrect() == LBool.UNSAT)
		{
			s_Logger.debug("Accepted");
			m_TraceChecker.computeInterpolants(new TraceChecker.AllIntegers(), m_PredicateUnifier, m_Pref.interpolation());

			addPath(word, m_ActualPath, m_TraceChecker.getInterpolants(), pre, post, pendingContexts);
			m_nofAdditionalPaths++;
			return true;
		}		
		else
		{
			s_Logger.debug("Declined");
			m_TraceChecker.finishTraceCheckWithoutInterpolantsOrProgramExecution();
			m_nofDeclinedPaths++;
			return false;
		}
	}

	/**
	 * Adds the path given from the trace checker. Assumes that the first and last
	 * state is already added. Adds edges states and interpolants
	 * 
	 *          s0      <pre>
	 *   e0 
	 *          s1       I0
	 *   e1
	 *          s2       I1
	 *   e2 
	 *          s3      <post>
	 * @param edges Contains the edges along the path
	 * @param states Holds all states (0, ..., n-1)
	 * @param interpolants The interpolants along the path for the states 1, ..., n-2
	 * @param pre the formula for the state 0
	 * @param post the formula for the state n-1
	 */
	private void addPath(NestedWord<CodeBlock> edges,
			ArrayList<IPredicate> states, IPredicate[] interpolants, IPredicate pre,
			IPredicate post, SortedMap<Integer, IPredicate> pendingContexts)
	{
		s_Logger.debug("Add path: numEdges:" + edges.length() + " numStates:"
				+ states.size() + " numInterpol:" + interpolants.length);
		s_Logger.debug("edges:");
		for (int i = 0; i < edges.length(); i++)
			s_Logger.debug("<" + edges.getSymbol(i).toString() + ">");
		s_Logger.debug("states:");
		for (int i = 0; i < states.size(); i++)
			s_Logger.debug("<" + states.get(i).toString() + ">");
		s_Logger.debug("interp:");
		for (int i = 0; i < interpolants.length; i++)
			s_Logger.debug("<" + interpolants[i].toString() + ">");

		// Add all edges
		for (int i = 0; i < edges.length(); i++)
		{
			CodeBlock e = edges.getSymbolAt(i);
			IPredicate targetS = states.get(i + 1);

			IPredicate sourceI = (i == 0) ? pre : interpolants[i - 1];
			IPredicate targetI = (i == edges.length() - 1) ? post : interpolants[i];

			// Add all states in the sequence, but the first and last.
			if (i < edges.length() - 1)
			{
				// targetS can(may) not be in m_AddedStates
				m_AnnotatedStates.add(targetS);
				// since the interpolant formula might not be unique
				if (!m_InterpolAutomaton.getStates().contains(targetI))
				{
					m_InterpolAutomaton.addState(targetI == m_AbstractionInitialState, targetI == m_AbstractionFinalState, targetI);
				}
				m_Epimorphism.insert(targetS, targetI);
			}

			// add the respective edge into the abstraction automaton
			if (edges.isInternalPosition(i)) 																				
			{
				boolean exists = false;
				for (OutgoingInternalTransition<CodeBlock, IPredicate> t : m_InterpolAutomaton.internalSuccessors(sourceI, e))
				{
						if(t.getSucc().equals(targetI))
						{
								exists = true;
						}
						break;
				}
				if(!exists)
				{
					m_InterpolAutomaton.addInternalTransition(sourceI, e, targetI);
				}
			} 
			else
			{
				if (edges.isCallPosition(i))
				{
					m_InterpolAutomaton.addCallTransition(sourceI, e, targetI);
				} 
				else // isReturnPosition(i)
				{
					IPredicate hier = pendingContexts.get(i);
					m_InterpolAutomaton.addReturnTransition(sourceI, hier, e, targetI);
				}
			}
		}
	}

	/**
	 * Construct the new program abstraction by subtraction the interpolant
	 * automaton from the abstraction
	 * 
	 * @return true if the trace of m_Counterexample (which was accepted by the
	 *         old m_Abstraction) is not accepted by the m_Abstraction.
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
		for (int i = 0; i < m_ErrorPathHistory.size(); i++)
		{
			s_Logger.debug("[" + i + "]: " + m_ErrorPathHistory.get(i));
		}

		m_CegarLoopBenchmark.reportAbstractionSize(m_Abstraction.size(), m_Iteration);

		s_Logger.info("Abstraction has " + m_NestedAbstraction.sizeInformation());
		s_Logger.info("Interpolant automaton has "
				+ m_InterpolAutomaton.sizeInformation());

		Minimization minimization = m_Pref.minimize();
		switch (minimization)
		{
			case NONE:
				break;
			case MINIMIZE_SEVPA:
			case SHRINK_NWA:
				s_Logger.debug("Minimizing interpolant automaton.");

				RemoveUnreachable<CodeBlock, IPredicate> removeUnreachable = new RemoveUnreachable<CodeBlock, IPredicate>(
						(INestedWordAutomatonSimple<CodeBlock, IPredicate>) m_Abstraction);
				m_Abstraction = removeUnreachable.getResult();

				RemoveDeadEnds<CodeBlock, IPredicate> removeDeadEnds = new RemoveDeadEnds<CodeBlock, IPredicate>(
						(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction);
				m_Abstraction = removeDeadEnds.getResult();

				minimizeAbstraction(m_StateFactoryForRefinement,
						m_PredicateFactoryResultChecking, minimization);
				break;
			default:
				throw new AssertionError();
		}

		return true;
	}
}
