package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2;

import java.io.File;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.*;
import java.util.Map.Entry;

import org.apache.log4j.Logger;


import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.preferences.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.*;	
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
import de.uni_freiburg.informatik.ultimate.result.*;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

/**
 * @author Jan Hättig
 * 
 */
public class AbstractInterpreter
{
	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;

	/**
	 * Symbol table of the given program
	 */
	private BoogieSymbolTable mSymbolTable;

	/**
	 * The domain which is used to represent abstract states
	 */
	private IAbstractDomain<?> mDomain;

	/**
	 * Nodes which have to be processed
	 */
	private final LinkedList<RCFGNode> mNodesToVisit = new LinkedList<RCFGNode>();

	/**
	 * Maps each node in the RCFG to a set of sates.
	 */
	private final Map<RCFGNode, List<StackState>> mStates = new HashMap<RCFGNode, List<StackState>>();


	private final Set<ProgramPoint> mRecursionEntryNodes = new HashSet<ProgramPoint>();
	private final Set<IAbstractStateChangeListener> mStateChangeListeners = new HashSet<IAbstractStateChangeListener>();
	private final Set<ProgramPoint> mErrorLocs = new HashSet<ProgramPoint>();
	private final Set<ProgramPoint> mReachedErrorLocs = new HashSet<ProgramPoint>();
	

	/**
	 * Caches all loop entry points.
	 */
	private HashMap<ProgramPoint, HashMap<RCFGEdge, RCFGEdge>> mLoopEntryNodes;

	// Lists of call statements to check if there is any node with a summary
	// that has no corresponding regular call
	private List<CallStatement> mCallStatementsAtCalls = new LinkedList<CallStatement>();
	private List<CallStatement> mCallStatementsAtSummaries = new LinkedList<CallStatement>();

	private AIPreferences mPreferences;

	/**
	 * Visits the edges and statements to
	 * apply the actions on the states using
	 * the domain
	 */
	private AIVisitor mVisitor;
	
	/**
	 * Execution will stop if there is a syntax error
	 * or after each edge the visitor can stop the execution 
	 */
	private boolean mContinueProcessing;
	
	

	/**
	 * Constructor
	 * 
	 * @param services
	 */
	public AbstractInterpreter(IUltimateServiceProvider services)
	{
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(AIActivator.s_PLUGIN_ID);

		mPreferences = new AIPreferences();
		mPreferences.fetchPreferences();
	}

	/**
	 * Adds an AbstractInterpretationAnnotation with states at the given
	 * location IElement
	 * 
	 * @param element
	 *            The location of the given states
	 * @param states
	 *            The states at the given location
	 */
	private void annotateElement(IElement element, List<StackState> states)
	{
		AbstractInterpretationAnnotations anno = new AbstractInterpretationAnnotations(states);
		anno.annotate(element);
	}

	/**
	 * Adds a program state to a node's list of states
	 * 
	 * @param node
	 *            The node that state belongs to
	 * @param state
	 *            The program state to put on the node
	 * @return True if the state was added, false if not (when a superstate is
	 *         at the node)
	 */
	private boolean putStateToNode(StackState state, RCFGNode node, RCFGEdge fromEdge)
	{
		mLogger.debug("Put state to node?");

		List<StackState> statesAtNode = mStates.get(node);
		if (statesAtNode == null)
		{
			statesAtNode = new LinkedList<StackState>();
			mStates.put(node, statesAtNode);
		}

		StackState newState = state;
		List<StackState> statesAtNodeBackup = new ArrayList<StackState>(statesAtNode);

		// check for loop entry / widening
		boolean applyLoopWidening = false;
		ProgramPoint pp = (ProgramPoint) node;
		if ((pp != null) && mLoopEntryNodes.containsKey(pp))
		{
			LoopStackElement le = newState.popLoopEntry();
			while ((le != null)
					&& (le.getLoopNode() != null)
					&& (le.getLoopNode() != node)
					&& (le.getExitEdge() == fromEdge))
			{
				le = newState.popLoopEntry();
			}
			if ((le != null)
					&& (newState.peekLoopEntry().getIterationCount(pp) >= mPreferences.getIterationsUntilWidening()))
			{
				applyLoopWidening = true;
			}
		}

		// check for recursive method exit / widening
		boolean applyRecursionWidening = false;
		if (mRecursionEntryNodes.contains(node))
		{
			applyRecursionWidening = newState.getRecursionCount() >= mPreferences.getIterationsUntilWidening();
		}

		// check existing states: super/sub/widening/merging
		Set<StackState> unprocessedStates = new HashSet<StackState>();
		Set<StackState> statesToRemove = new HashSet<StackState>();
		for (StackState s : statesAtNode)
		{
			// TODO: FIX (?)
			if (!(fromEdge instanceof Return)
					&& s.isSuper(newState))
			{
				mLogger.debug("NO! (fix ??)");
				return false; // abort if a superstate exists
			}

			if (s.isProcessed())
			{
				if (newState.isSuccessor(s))
				{
					// widen after loop if possible
					if (applyLoopWidening && (s.peekLoopEntry().getIterationCount(pp) > 0))
					{
						newState = s.widen(newState, false);
						mLogger.debug(String.format("Widening at %s", pp));
					}
					// widen at new recursive call if possible
					if (applyRecursionWidening)
					{
						newState = s.widen(newState, false);
						mLogger.debug(String.format(
								"Widening after recursion at %s", pp));
					}

					statesToRemove.add(s); // remove old obsolete nodes
				}
			}
			else if (newState.isSuper(s))
			{
				// remove unprocessed substates of the new state
				statesToRemove.add(s);
			}
			else
			{
				unprocessedStates.add(s); // collect unprocessed states
			}
		}

		for (StackState s : statesToRemove)
		{
			statesAtNode.remove(s);
		}
		if (unprocessedStates.size() >= mPreferences.getParallelStatesUntilMerge())
		{
			// merge states
			mLogger.debug(String.format("Merging at %s", node.toString()));
			for (StackState s : unprocessedStates)
			{
				StackState mergedState = s.merge(newState, false);
				if (mergedState != null)
				{
					statesAtNode.remove(s);
					newState = mergedState;
				}
			}
		}
		statesAtNode.add(newState);
		mLogger.debug("Yes!!");
		notifyStateChangeListeners(fromEdge, statesAtNodeBackup, state, newState);

		if (mPreferences.getGenerateStateAnnotations())
		{
			annotateElement(node, statesAtNode);
		}
		return true;
	}

	/**
	 * Provide the RootNode from where to start and the RCFG will be processed.
	 * 
	 * @param root
	 *            The node to start from. RootAnnotations are required for loop
	 *            detection etc.
	 */
	public void processRcfg(RootNode root)
	{
		mErrorLocs.clear();
		mReachedErrorLocs.clear();
		mRecursionEntryNodes.clear();

		// state change logger
		if (mPreferences.getStateChangeLogConsole() || mPreferences.getStateChangeLogFile())
		{
			String fileDir = "";
			String fileName = "";
			if (mPreferences.getStateChangeLogFile())
			{
				File sourceFile = new File(root.getFilename());
				DateFormat dfm = new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss");
				fileName = sourceFile.getName() + "_AI_" + dfm.format(new Date()) + ".txt";
				
				
				
				
				
				
				
				// DEFECT FILE STARTED HERE:
				if (mPreferences.getStateChangeLogUseSourcePath())
				{
					fileDir = sourceFile.getParent();
				}
				else
				{
					fileDir = null;
				}
				if (fileDir == null)
				{
					fileDir = new File(mPreferences.getStateChangeLogPath()).getAbsolutePath();
				}
			}
			StateChangeLogger scl = new StateChangeLogger(mLogger,
					mPreferences.getStateChangeLogConsole(), mPreferences.getStateChangeLogFile(), fileDir
							+ File.separatorChar + fileName);
			this.registerStateChangeListener(scl);
		}

		// numbers for widening
		Set<String> numbersForWidening = new HashSet<String>();
		numbersForWidening.addAll(mPreferences.getNumbersForWidening());
		// collect literals if preferences say so
		if (mPreferences.getWideningAutoNumbers())
		{
			LiteralCollector literalCollector = new LiteralCollector(root, mLogger);
			numbersForWidening.addAll(literalCollector.getResult());
		}

		// preprocessor annotation: get symbol table
		PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null)
		{
			mLogger.error("No symbol table found on given RootNode.");
			return;
		}
		mSymbolTable = pa.getSymbolTable();

		// Create the domain
		AIDomainFactory domainFactory = new AIDomainFactory(mLogger);
		mDomain = domainFactory.createDomain(mPreferences);

		mVisitor = new AIVisitor(mLogger, mServices, mSymbolTable, mDomain, numbersForWidening);	
		
		// fetch loop nodes with their entry/exit edges
		RCFGLoopDetector loopDetector = new RCFGLoopDetector(mServices);
		try
		{
			loopDetector.process(root);
		}
		catch (Throwable e1)
		{
			e1.printStackTrace();
		}
		mLoopEntryNodes = loopDetector.getResult();

		mLogger.debug("Loop information:");
		for (ProgramPoint pp : mLoopEntryNodes.keySet())
		{
			Map<RCFGEdge, RCFGEdge> loopsie = mLoopEntryNodes.get(pp);
			for (Entry<RCFGEdge, RCFGEdge> e : loopsie.entrySet())
			{
				mLogger.debug(String.format(
						"Loop: %s -> %s -> ... -> %s -> %s", pp,
						(ProgramPoint) e.getKey().getTarget(), (ProgramPoint) e
								.getValue().getSource(), pp));
			}
		}

		// root annotation: get location list, error locations
		RootAnnot ra = root.getRootAnnot();

		Map<String, ProgramPoint> entryNodes = ra.getEntryNodes();

		ProgramPoint mainEntry = entryNodes.get(mPreferences.getMainMethodName());

		// check for ULTIMATE.start and recursive methods
		for (String s : entryNodes.keySet())
		{
			ProgramPoint entryNode = entryNodes.get(s);
			// check for ULTIMATE.start
			if (entryNode.getProcedure().startsWith(mPreferences.getUltimateStartProcName()))
			{
				mainEntry = entryNode;
			}

			// check for recursive methods
			Collection<ProgramPoint> methodNodes = ra.getProgramPoints().get(s).values();

			for (RCFGEdge e : entryNode.getIncomingEdges())
			{
				if (methodNodes.contains(e.getSource()))
				{
					// entryNode belongs to recursive method
					mRecursionEntryNodes.add(entryNode);
				}
			}
		}

		Map<String, Collection<ProgramPoint>> errorLocMap = ra.getErrorNodes();
		for (String s : errorLocMap.keySet())
		{
			mErrorLocs.addAll(errorLocMap.get(s));
		}

		// add entry node of Main procedure / any if no Main() exists
		for (RCFGEdge e : root.getOutgoingEdges())
		{
			if (e instanceof RootEdge)
			{
				RCFGNode target = e.getTarget();
				if ((mainEntry == null) || (target == mainEntry))
				{
					StackState state = new StackState(mDomain, mLogger);

					if (target instanceof ProgramPoint)
					{
						CallStatement mainProcMockStatement = new CallStatement(
								null, false, null,
								((ProgramPoint) target).getProcedure(), null);

						state.pushStackLayer(mainProcMockStatement); // layer
																		// for
																		// main
																		// method
					}
					putStateToNode(state, target, e);
					mNodesToVisit.add(target);
				}
			}
		}

		visitNodes();

		/*
		 * report as safe if the analysis terminated after having explored the
		 * whole reachable state space without finding an error
		 */
		if (mReachedErrorLocs.isEmpty())
		{
			if (mVisitor.getContinueProcessing())
			{
				reportSafeResult();
			}
			else if (!mServices.getProgressMonitorService().continueProcessing()) 
			{
				reportTimeoutResult();
			}
		}
	}

	/**
	 * Visit edges as long as there are edges in m_edgesToVisit
	 */
	protected void visitNodes()
	{
		while (!mNodesToVisit.isEmpty())
		{
			RCFGNode node = (RCFGNode) mNodesToVisit.poll();
			if (node != null)
			{
				mCallStatementsAtCalls.clear();
				mCallStatementsAtSummaries.clear();

				List<StackState> statesAtNode = mStates.get(node);
				mLogger.debug(String.format("---- PROCESSING NODE %S ----", (ProgramPoint) node));

				// process all unprocessed states at the node
				boolean hasUnprocessed = true;
				while (hasUnprocessed && mVisitor.getContinueProcessing())
				{
					StackState unprocessedState = null;
					for (StackState s : statesAtNode)
					{
						if (!s.isProcessed())
						{
							unprocessedState = s;
							break;
						}
					}
					if (unprocessedState != null)
					{
						unprocessedState.setProcessed(true);
						
						mVisitor.setCurrentNode(node);						
						
						// process the state using each edge
						for (RCFGEdge e : node.getOutgoingEdges())
						{						
							mVisitor.setCurrentState(unprocessedState); 
							
							e.accept(mVisitor);
							
							
							if(!mVisitor.getError().isEmpty())
							{								
								reportUnsupportedSyntaxResult(e, mVisitor.getError());
							}
							
							StackState resultingState = mVisitor.getResultingState(); 
							if(resultingState == null)
							{
								if(mVisitor.violatedAssert())
								{
									reportUnSafeResult(mVisitor.getResult());
								}
								return;								
							}
							
							// if everything went fine, put node to state
							Map<RCFGEdge, RCFGEdge> loopEdges = mLoopEntryNodes.get(resultingState);
							if (loopEdges != null)
							{
								RCFGEdge exitEdge = loopEdges.get(e);
								if (exitEdge != null) 
								{
									resultingState.pushLoopEntry((ProgramPoint) node, exitEdge);
								}
							}

							resultingState.addCodeBlockToTrace((CodeBlock) e);

							RCFGNode targetNode = e.getTarget();
							if (targetNode != null)
							{
								if (putStateToNode(resultingState, targetNode, e))
								{
									ProgramPoint pp = (ProgramPoint) targetNode;
									if (mErrorLocs.contains(pp) && !mReachedErrorLocs.contains(pp))
									{
										mReachedErrorLocs.add(pp);
										reportErrorResult(pp, resultingState);
									}
									else
									{
										if (!mNodesToVisit.contains(targetNode))
										{
											mNodesToVisit.add(targetNode);
										}
									}
								}
							}
						}
					}
					else
					{
						hasUnprocessed = false;
					}

					// abort if asked to cancel
					mContinueProcessing = mVisitor.getContinueProcessing() && mServices.getProgressMonitorService().continueProcessing();

				} // hasUnprocessed

				// remove states if they aren't needed for possible widening
				// anymore
				if (node.getIncomingEdges().size() <= 1)
				{
					mStates.remove(node);
				}
				if (!mCallStatementsAtCalls.containsAll(mCallStatementsAtSummaries))
				{
					reportUnsupportedSyntaxResult(
							node,
							"Abstract interpretation plug-in can't verify programs which contain procedures without implementations.");
				}
				if (!mContinueProcessing)
				{
					break;
				}
			}
		}
	}

		
	
	/* -------------------------------- MISC -------------------------------- */
	/**
	 * Add a state change listener to be notified on state changes
	 * 
	 * @param listener
	 *            The listener to notify
	 * @return True if it has been added, false if not, i.e. if it was already
	 *         registered
	 */
	public boolean registerStateChangeListener(
			IAbstractStateChangeListener listener)
	{
		return mStateChangeListeners.add(listener);
	}

	/**
	 * Remove a state change listener
	 * 
	 * @param listener
	 *            The listener to remove
	 * @return True if it was in the list and has been removed, false if it
	 *         wasn't there to begin with
	 */
	public boolean removeStateChangeListener(
			IAbstractStateChangeListener listener)
	{
		return mStateChangeListeners.remove(listener);
	}

	/**
	 * Notifies all state change listeners of a state change
	 * 
	 * @param viaEdge
	 * @param oldStates
	 * @param newState
	 * @param mergedState
	 */
	private void notifyStateChangeListeners(
			RCFGEdge viaEdge,
			List<StackState> oldStates,
			StackState newState,
			StackState mergedState)
	{
		for (IAbstractStateChangeListener l : mStateChangeListeners)
		{
			List<StackState> statesCopy = new ArrayList<StackState>(oldStates.size());
			statesCopy.addAll(oldStates);
			l.onStateChange(viaEdge, statesCopy, newState, mergedState);
		}
	}

	/**
	 * Reports a possible error as the plugin's result
	 * 
	 * @param location
	 *            The error location
	 * @param state
	 *            The abstract state at the error location
	 */
	private UnprovableResult<RcfgElement, CodeBlock, Expression> reportErrorResult(
			ProgramPoint location, StackState state)
	{

		RcfgProgramExecution programExecution = new RcfgProgramExecution(
				state.getTrace(),
				new HashMap<Integer, ProgramState<Expression>>(), null);

		UnprovableResult<RcfgElement, CodeBlock, Expression> result = new UnprovableResult<RcfgElement, CodeBlock, Expression>(
				AIActivator.s_PLUGIN_NAME, location,
				mServices.getBacktranslationService(), programExecution);

		mServices.getResultService().reportResult(AIActivator.s_PLUGIN_ID,
				result);

		if (mPreferences.getStopAfterAnyError())
		{
			mContinueProcessing = false;
			mLogger.info(String
					.format("Abstract interpretation finished after reaching error location %s",
							location.getLocationName()));
		}
		else if (mPreferences.getStopAfterAllErrors())
		{
			if (mReachedErrorLocs.containsAll(mErrorLocs)) 
			{
				mContinueProcessing = false;
			}
			mLogger.info("Abstract interpretation finished after reaching all error locations");
		}
		return result;
	}

	private void reportUnsupportedSyntaxResult(IElement location, String message)
	{
		UnsupportedSyntaxResult<IElement> result = new UnsupportedSyntaxResult<IElement>(
				location, AIActivator.s_PLUGIN_NAME,
				mServices.getBacktranslationService(), message);

		mServices.getResultService().reportResult(AIActivator.s_PLUGIN_ID,
				result);

		mContinueProcessing = false;
	}

	/**
	 * Reports safety of the program as the plugin's result
	 */
	private void reportSafeResult()
	{
		mServices.getResultService().reportResult(
				AIActivator.s_PLUGIN_ID,
				new AllSpecificationsHoldResult(AIActivator.s_PLUGIN_NAME,
						"No error locations were reached."));
	}

	/* 
	 * Reports non-safety of the program as the plugin's result
	 */
	private void reportUnSafeResult(String message)
	{
		mServices.getResultService().reportResult(
				AIActivator.s_PLUGIN_ID,
				new GenericResult(AIActivator.s_PLUGIN_NAME, "assert violation", message, Severity.INFO));
	}
	/**
	 * Reports a timeout of the analysis
	 */
	private void reportTimeoutResult()
	{
		mServices.getResultService().reportResult(
				AIActivator.s_PLUGIN_ID,
				new TimeoutResult(AIActivator.s_PLUGIN_NAME,
						"Analysis aborted."));
	}

	
}
