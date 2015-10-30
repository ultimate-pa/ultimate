package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.io.File;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.*;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.preferences.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util.RCFGWalker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
import de.uni_freiburg.informatik.ultimate.result.*;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * @author Jan Hättig
 * 
 */
@SuppressWarnings("rawtypes")
public class AbstractInterpreter {
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
	private Map<ProgramPoint, Map<RCFGEdge, RCFGEdge>> mLoopEntryNodes;

	/**
	 * Lists of call statements to check if there is any node with a summary
	 * that has no corresponding regular call
	 */
	private List<CallStatement> mCallStatementsAtCalls = new LinkedList<CallStatement>();
	private List<CallStatement> mCallStatementsAtSummaries = new LinkedList<CallStatement>();

	private AIPreferences mPreferences;

	/**
	 * Visits the edges and statements to apply the actions on the states using
	 * the domain
	 */
	private AIVisitor mVisitor;
	private RCFGWalker mRCFGWalker;

	/**
	 * Execution will stop if there is a syntax error or after each edge the
	 * visitor can stop the execution
	 */
	private boolean mContinueProcessing;

	private int mNofMerging;
	private int mNofWidening;
	private int mNofRecMerging;
	private int mNofRecWidening;
	private int mNofSteps;
	private boolean mPostponeWidenedStates;

	/**
	 * Constructor
	 * 
	 * @param services
	 */
	public AbstractInterpreter(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(AIActivator.PLUGIN_ID);

		mPreferences = new AIPreferences();
		mPreferences.fetchPreferences();

		mNofMerging = 0;
		mNofWidening = 0;
		mNofRecMerging = 0;
		mNofRecWidening = 0;
		mNofSteps = 0;
		mPostponeWidenedStates = mPreferences.getPostponeWidening();
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
	private void annotateElement(IElement element, List<StackState> states) {
		if (!mPreferences.getGenerateStateAnnotations()) {
			return;
		}
		AbstractInterpretationAnnotations anno = new AbstractInterpretationAnnotations(states);
		anno.annotate(element);
	}

	/**
	 * Provide the RootNode from where to start and the RCFG will be processed.
	 * 
	 * @param root
	 *            The node to start from. RootAnnotations are required for loop
	 *            detection etc.
	 */
	@SuppressWarnings({ "unchecked" })
	public void processRcfg(RootNode root) {
		mErrorLocs.clear();
		mReachedErrorLocs.clear();
		mRecursionEntryNodes.clear();

		// state change logger
		if (mPreferences.getStateChangeLogConsole() || mPreferences.getStateChangeLogFile()) {
			String fileDir = "";
			String fileName = "";
			if (mPreferences.getStateChangeLogFile()) {
				File sourceFile = new File(root.getFilename());
				DateFormat dfm = new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss");
				fileName = sourceFile.getName() + "_AI_" + dfm.format(new Date()) + ".txt";

				// ---- DEFECT FILE STARTED HERE ----
				if (mPreferences.getStateChangeLogUseSourcePath()) {
					fileDir = sourceFile.getParent();
				} else {
					fileDir = null;
				}
				if (fileDir == null) {
					fileDir = new File(mPreferences.getStateChangeLogPath()).getAbsolutePath();
				}
			}
			StateChangeLogger scl = new StateChangeLogger(mLogger, mPreferences.getStateChangeLogConsole(),
					mPreferences.getStateChangeLogFile(), fileDir + File.separatorChar + fileName);
			this.registerStateChangeListener(scl);
		}

		// numbers for widening
		Set<String> numbersForWidening = new HashSet<String>();
		numbersForWidening.addAll(mPreferences.getNumbersForWidening());
		// collect literals if preferences say so
		if (mPreferences.getWideningAutoNumbers()) {
			LiteralCollector literalCollector = new LiteralCollector(root, mLogger);
			numbersForWidening.addAll(literalCollector.getResult());
		}

		// preprocessor annotation: get symbol table
		PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null) {
			mLogger.error("No symbol table found on given RootNode.");
			return;
		}
		mSymbolTable = pa.getSymbolTable();

		// create the domain
		AbstractDomainFactory domainFactory = new AbstractDomainFactory(mLogger);
		mDomain = domainFactory.createDomain(mPreferences, numbersForWidening);
		mDomain.initializeDomain();

		mLogger.info("Using Domain: " + mDomain.toString());

		// create the visitors
		mVisitor = new AIVisitor(mLogger, mServices, mSymbolTable, mDomain);
		mRCFGWalker = new RCFGWalker(mVisitor);

		// fetch loop nodes with their entry/exit edges
		final RCFGLoopDetector loopDetector = new RCFGLoopDetector(mServices);
		try {
			loopDetector.process(root);
		} catch (final Throwable ex) {
			mLogger.fatal("Loop detector failed: " + ex.getMessage());
			throw new RuntimeException(ex);
		}
		mLoopEntryNodes = loopDetector.getResult();

		mLogger.debug("Loop information:");
		for (ProgramPoint pp : mLoopEntryNodes.keySet()) {
			Map<RCFGEdge, RCFGEdge> loopsie = mLoopEntryNodes.get(pp);
			for (Entry<RCFGEdge, RCFGEdge> e : loopsie.entrySet()) {
				mLogger.debug(String.format("Loop: %s -> %s -> ... -> %s -> %s", pp,
						(ProgramPoint) e.getKey().getTarget(), (ProgramPoint) e.getValue().getSource(), pp));
			}
		}

		// root annotation: get location list, error locations
		RootAnnot ra = root.getRootAnnot();
		Map<String, ProgramPoint> entryNodes = ra.getEntryNodes();

		// find the main method entry
		String[] mainMethodNames = mPreferences.getMainMethodNames().split(",");
		ProgramPoint mainEntry = null;
		for (String s : mainMethodNames) {
			ProgramPoint p = entryNodes.get(s.trim());
			if (p != null) {
				mainEntry = p;
				break;
			}
		}
		// check for ULTIMATE.start and recursive methods
		for (String s : entryNodes.keySet()) {
			ProgramPoint entryNode = entryNodes.get(s);
			// check for ULTIMATE.start
			if (entryNode.getProcedure().startsWith(mPreferences.getUltimateStartProcName())) {
				mainEntry = entryNode;
			}

			// check for recursive methods
			Collection<ProgramPoint> methodNodes = ra.getProgramPoints().get(s).values();

			for (RCFGEdge e : entryNode.getIncomingEdges()) {
				if (methodNodes.contains(e.getSource())) {
					// entryNode belongs to recursive method
					mRecursionEntryNodes.add(entryNode);
				}
			}
		}

		Map<String, Collection<ProgramPoint>> errorLocMap = ra.getErrorNodes();
		for (String s : errorLocMap.keySet()) {
			mErrorLocs.addAll(errorLocMap.get(s));
		}

		// add entry node of Main procedure / any if no Main() exists
		for (RCFGEdge e : root.getOutgoingEdges()) {
			if (e instanceof RootEdge) {
				RCFGNode target = e.getTarget();
				if ((mainEntry == null) || (target == mainEntry)) {
					mLogger.warn("There was no entry node specified!");
					StackState state = new StackState(mDomain, mLogger);

					if (target instanceof ProgramPoint) {
						CallStatement mainProcMockStatement = new CallStatement(null, false, null,
								((ProgramPoint) target).getProcedure(), null);
						// layer for main method
						state.pushStackLayer(mainProcMockStatement, mDomain.createState());
					}
					putStateToNode(state, e, target);
					mNodesToVisit.add(target);
				}
			}
		}

		visitNodes();

		mLogger.info(String.format(
				"Executed operations: #Steps: %s,  #Merge: %s,  #Widening: %s,  #RecMerge: %s,  #RecWidening: %s",
				mNofSteps, mNofMerging, mNofWidening, mNofRecMerging, mNofRecWidening));
		/*
		 * report as safe if the analysis terminated after having explored the
		 * whole reachable state space without finding an error
		 */
		if (mReachedErrorLocs.isEmpty()) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throwTimeout();
			} else {
				reportSafeResult();
			}
		}

		final Map<RCFGNode, Term> predicates = getPredicates(root);
		if (mLogger.isDebugEnabled()) {
			printPredicatesDebug(predicates);
		}
		new AbstractInterpretationPredicates(predicates).annotate(root);
		mLogger.info("Annotated " + predicates.size() + " predicates");
		mDomain.finalizeDomain();
	}

	/**
	 * Visit edges as long as there are edges in m_edgesToVisit
	 */
	protected void visitNodes() {
		while (!mNodesToVisit.isEmpty()) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throwTimeout();
			}

			// mLogger.debug("Nodes to process:");
			// for (RCFGNode node : mNodesToVisit)
			// {
			// mLogger.debug(node.toString());
			// }
			RCFGNode node = (RCFGNode) mNodesToVisit.poll();
			if (node != null) {
				ProgramPoint pp = (ProgramPoint) node;

				mCallStatementsAtCalls.clear();
				mCallStatementsAtSummaries.clear();

				List<StackState> statesAtNode = mStates.get(node);
				// mLogger.debug(String.format("---- PROCESSING NODE %S ----",
				// pp));

				// process all unprocessed states at the node
				mContinueProcessing = true;
				while (mContinueProcessing) {
					// pick an unprocessed state
					StackState unprocessedState = null;
					for (StackState s : statesAtNode) {
						if (!s.isProcessed()) {
							unprocessedState = s;
							break;
						}
					}
					if (unprocessedState == null) {
						break;
					}

					// mLogger.debug("States at node:");
					// for (StackState s : statesAtNode)
					// {
					// mLogger.debug("\n" + (s.isProcessed() ? "(D)" : "(*)") +
					// s.toString());
					// }

					unprocessedState.setProcessed(true);
					mVisitor.setCurrentNode(node);

					RCFGEdge exclusiveEdge = unprocessedState.getExclusiveEdgeAt(pp);
					RCFGEdge ignoredEdge = unprocessedState.getIgnoreEdgeAt(pp);
					// process the state using each outgoing edge
					for (RCFGEdge edge : node.getOutgoingEdges()) {
						// mLogger.debug("Unprocessed state: \n" +
						// unprocessedState.toString());

						// do not take the outwards edge directly after widening

						if ((exclusiveEdge != null && exclusiveEdge != edge) || ignoredEdge == edge) {
							// mLogger.debug("postponed/ignored (" + edge +
							// ")");
							// mPostponeEdge.remove(unprocessedState);
							continue;
						}

						mNofSteps++;
						mVisitor.setCurrentState(unprocessedState);

						mRCFGWalker.visit(edge);

						// mLogger.debug("Resulting states: \n" +
						// StackState.toString(mVisitor.getResultingStates()));

						// check for errors
						if (!mVisitor.getError().isEmpty()) {
							reportUnsupportedSyntaxResult(edge, mVisitor.getError());
						}

						// check the resulting state
						List<StackState> resultingStates = mVisitor.getResultingStates();

						if (resultingStates.size() == 0) {
							// do not add the state if bottom
							// but report violated asserts
							if (mVisitor.violatedAssert()) {
								reportUnSafeResult(mVisitor.getResult());
							}
							continue;
						}

						// else if everything went fine, put node to state
						// handle each state
						for (StackState resultingState : resultingStates) {
							resultingState.addCodeBlockToTrace((CodeBlock) edge);

							// if this is a loop entry, add a loop stack entry
							increaseLoopCount(node, edge, resultingState);

							// put to node
							RCFGNode targetNode = edge.getTarget();
							if (targetNode != null) {
								if (putStateToNode(resultingState, edge, targetNode)) {
									ProgramPoint targetP = (ProgramPoint) targetNode;
									if (mErrorLocs.contains(targetP) && !mReachedErrorLocs.contains(targetP)) {
										mReachedErrorLocs.add(targetP);
										reportErrorResult(targetP, resultingState);
									} else if (!mNodesToVisit.contains(targetNode)) {
										mNodesToVisit.add(targetNode);
									}
								}
							}
						}
					}
					mContinueProcessing = mContinueProcessing && mVisitor.getContinueProcessing()
							&& mServices.getProgressMonitorService().continueProcessing();
				} // hasUnprocessed

				// remove states if they aren't needed for possible widening
				// anymore
				if (node.getIncomingEdges().size() <= 1) {
					mStates.remove(node);
				}
				if (!mCallStatementsAtCalls.containsAll(mCallStatementsAtSummaries)) {
					reportUnsupportedSyntaxResult(node,
							"Abstract interpretation plug-in can't verify programs which contain procedures without implementations.");
				}
				if (!mContinueProcessing) {
					break;
				}
			}
		}
	}

	private void throwTimeout() {
		throw new ToolchainCanceledException(getClass(), "Abstract interpretation timeout.");
	}

	private void increaseLoopCount(RCFGNode node, RCFGEdge edge, StackState resultingState) {
		Map<RCFGEdge, RCFGEdge> loopEdges = mLoopEntryNodes.get(node);
		ProgramPoint pp = (ProgramPoint) node;
		if (loopEdges != null) {
			RCFGEdge exitEdge = loopEdges.get(edge);
			if (exitEdge != null) {
				// check if the top element is already
				// of the same loop
				LoopStackElement top = resultingState.peekLoopEntry();
				if (!(top.getLoopNode() == pp && top.getExitEdge() == exitEdge)) {
					if (resultingState.containsLoopElement(pp, exitEdge)) {
						mLogger.warn("loop chaos");
						throw new RuntimeException();
					}
					// remember the node and the node where
					// the loop exits
					resultingState.pushLoopEntry(pp, exitEdge, edge);
				}
			}
		}
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
	@SuppressWarnings({ "unchecked" })
	private boolean putStateToNode(StackState state, RCFGEdge edge, RCFGNode targetNode) {
		mLogger.debug("Put state to node?");

		List<StackState> statesAtNode = mStates.get(targetNode);
		if (statesAtNode == null) {
			statesAtNode = new LinkedList<StackState>();
			mStates.put(targetNode, statesAtNode);
		}

		StackState newState = state;
		List<StackState> statesAtNodeBackup = new ArrayList<StackState>(statesAtNode);

		ProgramPoint pp = (ProgramPoint) targetNode;

		// ignored and exclusive edges shall only be ignored once
		newState.removeExclusiveEdgeAt(pp);
		newState.removeIgnoreEdgeAt(pp);

		// check for loop entry / widening
		RCFGEdge loopEntry = null;
		boolean applyLoopWidening = false;

		if (pp != null && mLoopEntryNodes.containsKey(pp) && newState.containsLoopElement(targetNode, edge)) {
			// find the correct loop entry
			LoopStackElement le = newState.peekLoopEntry();
			// if it was not the topmost one, remove all entries
			// until the correct one was found
			while (le.getLoopNode() != targetNode && le.getEntryEdge() != edge) {
				// remove it
				newState.popLoopEntry();
				// mLogger.debug("Dump lse: " + dump);
				// and get the next (outer one)
				le = newState.peekLoopEntry();
			}
			le.increaseIterationCount();
			// mLogger.debug("Found lse: " + le);

			if (le != null && le.getIterationCount() >= mPreferences.getIterationsUntilWidening()) {
				applyLoopWidening = true;
				loopEntry = le.getEntryEdge();
			}
		}

		// check for recursive method exit / widening
		boolean applyRecursionWidening = false;
		if (edge instanceof Call
				// mRecursionEntryNodes.contains(targetNode)
				&& newState.getRecursionCount() >= mPreferences.getIterationsUntilRecursiveWidening()) {
			// try to shrink the state (all sequences)
			applyRecursionWidening = true;
		}

		// check existing states: super/sub/widening/merging
		Set<StackState> unprocessedStates = new HashSet<StackState>();
		Set<StackState> statesToRemove = new HashSet<StackState>();
		StackState addState = null;
		for (StackState s : statesAtNode) {
			if (!(edge instanceof Return) && s.isSuperOrEqual(newState) && s.getExclusiveEdgeAt(pp) == null) {
				// mLogger.debug("NO!");
				return false; // abort if a super state exists
			}
		}

		for (StackState s : statesAtNode) {
			if (s.isProcessed()) {
				if (newState.isSuccessor(s)) {
					// widen after loop if possible
					if (applyLoopWidening) {
						if (s.getExclusiveEdgeAt(pp) != null) {
							// mLogger.debug("do not widen (posponed)");
						} else {
							// create a widened state, but add the old one as
							// well
							// mLogger.debug(String.format("Widening at " + pp +
							// "\n" + s + "\n---and---\n" + newState));
							StackState widenedState = s.widen(newState, false);
							mNofWidening++;
							// mLogger.debug("\n---result---\n" + widenedState);

							if (mPostponeWidenedStates) {
								widenedState.setExclusiveEdgeAt(pp, loopEntry);

								// since we prevent the execution out of the
								// loop for the
								// new state, we want to put at least the
								// un-widen-ed original state to the node too
								addState = newState;
								// this one may enter every other edge
								addState.setIgnoreEdgeAt(pp, loopEntry);

								// mLogger.debug("Pospone state: \n" +
								// widenedState.toString());
							}
							newState = widenedState;
						}
					}

					// widen at new recursive call if possible
					// only perform widening, if the stacks are the same
					if (applyRecursionWidening) {
						// try to match the sizes of the call stacks
						// shrink/merge the new state until they are equal in
						// size
						// mLogger.debug(String.format("Widening after recursion
						// at "
						// + pp + "\n" + s + "\n---and---\n" + newState));
						while (newState.getStackSize() > s.getStackSize() && newState.MergeStackLayers()) {
							mNofRecMerging++;
							// canBeMerged = true;
						}
						// mLogger.debug(String.format("\n---after stack
						// merging---\n"
						// + newState));

						// only try to widen if the merging lead to equal stack
						// sizes
						if (newState.getStackSize() == s.getStackSize()) {
							// TODO: check if the following merge operation can
							// be dropped
							// reason: the stacks are identical but
							// the last element is even a merge of the two last
							// iterations
							newState = s.merge(newState, true);
							// mLogger.debug("\n---merged stack---\n" +
							// newState);
							StackState widenedState = s.widen(newState, false);
							mNofRecWidening++;
							// mLogger.debug("\n---result---\n" + newState);

							newState = widenedState;
						} else {
							// mLogger.debug("cannot apply widening on different
							// size state stacks");
						}
					}

					// TODO: remove the following check, since it can never be
					// true
					// the state only grows after widening
					// check again if the (possibly widened state is not super
					// to the old)
					if ((applyRecursionWidening || applyLoopWidening) && s.getExclusiveEdgeAt(pp) == null
							&& s.isSuperOrEqual(newState)) {
						// mLogger.debug("new (widened) state is not super to
						// the old state -> NO");
						newState = null;
						break;
					}

					statesToRemove.add(s); // remove predecessor nodes
				}
			} else if (newState.isSuperOrEqual(s)) {
				// remove unprocessed sub states of the new state
				statesToRemove.add(s);
			} else {
				unprocessedStates.add(s); // collect unprocessed states
			}
		}
		if (addState != null) {
			addState.setProcessed(false);
			statesAtNode.add(addState);
			unprocessedStates.add(addState);
		}

		// remove states
		for (StackState s : statesToRemove) {
			// mLogger.debug("Remove state: " + s);
			statesAtNode.remove(s);
		}

		if (newState == null) {
			return false;
		}

		// merge unprocessed states (into the newState and remove them)
		if (unprocessedStates.size() + 1 > mPreferences.getParallelStatesUntilMerge()) {
			// merge states
			// mLogger.debug(String.format("Merging at %s",
			// targetNode.toString()));
			for (StackState s : unprocessedStates) {
				// mLogger.debug("\n---of---\n" + s + "\n---and---\n" + newState
				// + "\n---result---\n");
				StackState mergedState = s.merge(newState, false);
				mNofMerging++;
				// mLogger.debug(mergedState);
				if (mergedState != null) {
					statesAtNode.remove(s);
					newState = mergedState;
				}
			}
		}

		newState.setProcessed(false);
		statesAtNode.add(newState);

		notifyStateChangeListeners(edge, statesAtNodeBackup, state, newState);
		annotateElement(targetNode, statesAtNode);

		return true;
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
	public boolean registerStateChangeListener(IAbstractStateChangeListener listener) {
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
	public boolean removeStateChangeListener(IAbstractStateChangeListener listener) {
		return mStateChangeListeners.remove(listener);
	}

	private void printPredicatesDebug(Map<RCFGNode, Term> predicates) {
		if (predicates == null) {
			return;
		}

		for (final Entry<RCFGNode, Term> entry : predicates.entrySet()) {
			mLogger.debug(entry.getKey() + " has " + entry.getValue());
		}
	}

	private Map<RCFGNode, Term> getPredicates(RootNode root) {
		if (root == null) {
			mLogger.error("Cannot create predicates because root is null");
			return Collections.emptyMap();
		}

		final Map<RCFGNode, Term> rtr = new HashMap<>();
		final Script script = root.getRootAnnot().getScript();
		final Boogie2SMT bpl2smt = root.getRootAnnot().getBoogie2SMT();

		for (final Entry<RCFGNode, List<StackState>> entry : mStates.entrySet()) {
			final List<StackState> states = entry.getValue();
			if (states.size() != 1) {
				continue;
			}
			final StackState currentStackState = states.get(0);
			if (currentStackState.getStackSize() != 1) {
				continue;
			}
			IAbstractState currentState = currentStackState.getCurrentState();
			if (currentState == null) {
				continue;
			}
			rtr.put(entry.getKey(), currentState.getTerm(script, bpl2smt));
		}
		return rtr;
	}

	/**
	 * Notifies all state change listeners of a state change
	 * 
	 * @param viaEdge
	 * @param oldStates
	 * @param newState
	 * @param mergedState
	 */
	private void notifyStateChangeListeners(RCFGEdge viaEdge, List<StackState> oldStates, StackState newState,
			StackState mergedState) {
		for (IAbstractStateChangeListener l : mStateChangeListeners) {
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
	@SuppressWarnings("unchecked")
	private UnprovableResult<RcfgElement, CodeBlock, Expression> reportErrorResult(ProgramPoint location,
			StackState state) {

		RcfgProgramExecution programExecution = new RcfgProgramExecution(state.getTrace(),
				new HashMap<Integer, ProgramState<Expression>>());

		UnprovableResult<RcfgElement, CodeBlock, Expression> result = new UnprovableResult<RcfgElement, CodeBlock, Expression>(
				AIActivator.PLUGIN_NAME, location, mServices.getBacktranslationService(), programExecution,
				Collections.emptyList());

		mServices.getResultService().reportResult(AIActivator.PLUGIN_ID, result);

		if (mPreferences.getStopAfterAnyError()) {
			mContinueProcessing = false;
			mLogger.info(String.format("Abstract interpretation finished after reaching error location %s",
					location.getLocationName()));
		} else if (mPreferences.getStopAfterAllErrors()) {
			if (mReachedErrorLocs.containsAll(mErrorLocs)) {
				mContinueProcessing = false;
			}
			mLogger.info("Abstract interpretation finished after reaching all error locations");
		}
		return result;
	}

	private void reportUnsupportedSyntaxResult(IElement location, String message) {
		UnsupportedSyntaxResult<IElement> result = new UnsupportedSyntaxResult<IElement>(location,
				AIActivator.PLUGIN_NAME, mServices.getBacktranslationService(), message);

		mServices.getResultService().reportResult(AIActivator.PLUGIN_ID, result);

		mContinueProcessing = false;
	}

	/**
	 * Reports safety of the program as the plugin's result
	 */
	private void reportSafeResult() {
		mServices.getResultService().reportResult(AIActivator.PLUGIN_ID,
				new AllSpecificationsHoldResult(AIActivator.PLUGIN_NAME, "No error locations were reached."));
	}

	/*
	 * Reports non-safety of the program as the plugin's result
	 */
	private void reportUnSafeResult(String message) {
		mServices.getResultService().reportResult(AIActivator.PLUGIN_ID,
				new GenericResult(AIActivator.PLUGIN_NAME, "assert violation", message, Severity.INFO));
	}
}
