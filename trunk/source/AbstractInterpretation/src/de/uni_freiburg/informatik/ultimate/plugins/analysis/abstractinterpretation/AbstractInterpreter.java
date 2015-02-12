/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.io.File;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractInterpretationBoogieVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState.LoopStackElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.topbottomdomain.TopBottomDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.preferences.AbstractInterpretationPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

/**
 * @author Christopher Dillo
 * 
 */
public class AbstractInterpreter extends RCFGEdgeVisitor {

	private final IUltimateServiceProvider mServices;

	private final Logger mLogger;

	private IAbstractDomainFactory<?> mIntDomainFactory;
	private IAbstractDomainFactory<?> mRealDomainFactory;
	private IAbstractDomainFactory<?> mBoolDomainFactory;
	private IAbstractDomainFactory<?> mBitVectorDomainFactory;
	private IAbstractDomainFactory<?> mStringDomainFactory;

	private final LinkedList<RCFGNode> mNodesToVisit = new LinkedList<RCFGNode>();

	private final Map<RCFGNode, List<AbstractState>> mStates = new HashMap<RCFGNode, List<AbstractState>>();

	private AbstractState mCurrentState, mResultingState;

	private RCFGNode mCurrentNode;

	private AbstractInterpretationBoogieVisitor mBoogieVisitor;

	private final Set<IAbstractStateChangeListener> mStateChangeListeners = new HashSet<IAbstractStateChangeListener>();

	private final Set<ProgramPoint> mErrorLocs = new HashSet<ProgramPoint>();
	private final Set<ProgramPoint> mReachedErrorLocs = new HashSet<ProgramPoint>();

	private HashMap<ProgramPoint, HashMap<RCFGEdge, RCFGEdge>> mLoopEntryNodes;

	private final Set<ProgramPoint> mRecursionEntryNodes = new HashSet<ProgramPoint>();

	private Set<String> mFixedNumbersForWidening = new HashSet<String>();
	private Set<String> mNumbersForWidening = new HashSet<String>();

	private BoogieSymbolTable mSymbolTable;

	private boolean mContinueProcessing;

	// Lists of call statements to check if there is any node with a summary
	// that has no corresponding regular call
	private List<CallStatement> mCallStatementsAtCalls = new LinkedList<CallStatement>();
	private List<CallStatement> mCallStatementsAtSummaries = new LinkedList<CallStatement>();

	// for preferences
	private String mMainMethodName;
	private int mIterationsUntilWidening;
	private int mParallelStatesUntilMerge;
	private String mWideningFixedNumbers;
	private boolean mWideningAutoNumbers;

	private boolean mGenerateStateAnnotations;
	private boolean mStateChangeLogConsole;
	private boolean mStateChangeLogFile;
	private boolean mStateChangeLogUseSourcePath;
	private String mStateChangeLogPath;

	private boolean mStopAfterAnyError;
	private boolean mStopAfterAllErrors;

	private String mIntDomainID;
	private String mIntWideningOpName;
	private String mIntMergeOpName;

	private String mRealDomainID;
	private String mRealWideningOpName;
	private String mRealMergeOpName;

	private String mBoolDomainID;
	private String mBoolWideningOpName;
	private String mBoolMergeOpName;

	private String mBitVectorDomainID;
	private String mBitVectorWideningOpName;
	private String mBitVectorMergeOpName;

	private String mStringDomainID;
	private String mStringWideningOpName;
	private String mStringMergeOpName;

	// ULTIMATE.start
	private final String mUltimateStartProcName = "ULTIMATE.start";

	public AbstractInterpreter(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);

		fetchPreferences();

		if (!mWideningFixedNumbers.isEmpty()) {
			String[] nums = mWideningFixedNumbers.split(",");
			for (int i = 0; i < nums.length; i++)
				mFixedNumbersForWidening.add(nums[i].trim());
		}
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
	private void annotateElement(IElement element, List<AbstractState> states) {
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
	private boolean putStateToNode(AbstractState state, RCFGNode node, RCFGEdge fromEdge) {
		mLogger.debug("Put state to node?");
		List<AbstractState> statesAtNode = mStates.get(node);
		if (statesAtNode == null) {
			statesAtNode = new LinkedList<AbstractState>();
			mStates.put(node, statesAtNode);
		}

		AbstractState newState = state;
		List<AbstractState> statesAtNodeBackup = new ArrayList<AbstractState>(statesAtNode);

		// check for loop entry / widening
		boolean applyLoopWidening = false;
		ProgramPoint pp = (ProgramPoint) node;
		if ((pp != null) && mLoopEntryNodes.containsKey(pp)) {
			LoopStackElement le = newState.popLoopEntry();
			while ((le != null) && (le.getLoopNode() != null) && (le.getLoopNode() != node)
					&& (le.getExitEdge() == fromEdge))
				le = newState.popLoopEntry();
			if ((le != null) && (newState.peekLoopEntry().getIterationCount(pp) >= mIterationsUntilWidening))
				applyLoopWidening = true;
		}
		// check for recursive method exit / widening
		boolean applyRecursionWidening = false;
		if (mRecursionEntryNodes.contains(node))
			applyRecursionWidening = newState.getRecursionCount() >= mIterationsUntilWidening;

		// check existing states: super/sub/widening/merging
		Set<AbstractState> unprocessedStates = new HashSet<AbstractState>();
		Set<AbstractState> statesToRemove = new HashSet<AbstractState>();		for (AbstractState s : statesAtNode) {
			// TODO: FIX
			if (!(fromEdge instanceof Return) && s.isSuper(newState)) {
				mLogger.debug("NO!");
				return false; // abort if a superstate exists
			}
			if (s.isProcessed()) {
				if (newState.isSuccessor(s)) {
					// widen after loop if possible
					if (applyLoopWidening && (s.peekLoopEntry().getIterationCount(pp) > 0)) {
						newState = s.widen(newState);
						mLogger.debug(String.format("Widening at %s", pp));
					}
					// widen at new recursive call if possible
					if (applyRecursionWidening) {
						newState = s.widen(newState);
						mLogger.debug(String.format("Widening after recursion at %s", pp));
					}

					statesToRemove.add(s); // remove old obsolete nodes
				}
			} else if (newState.isSuper(s)) {
				// remove unprocessed substates of the new state
				statesToRemove.add(s);
			} else {
				unprocessedStates.add(s); // collect unprocessed states
			}
		}
		for (AbstractState s : statesToRemove)
			statesAtNode.remove(s);
		if (unprocessedStates.size() >= mParallelStatesUntilMerge) {
			// merge states
			mLogger.debug(String.format("Merging at %s", node.toString()));
			for (AbstractState s : unprocessedStates) {
				AbstractState mergedState = s.merge(newState);
				if (mergedState != null) {
					statesAtNode.remove(s);
					newState = mergedState;
				}
			}
		}
		statesAtNode.add(newState);
		mLogger.debug("Yes!!");
		notifyStateChangeListeners(fromEdge, statesAtNodeBackup, state, newState);

		if (mGenerateStateAnnotations)
			annotateElement(node, statesAtNode);
		return true;
	}

	/**
	 * Provide the RootNode from where to start and the RCFG will be processed.
	 * 
	 * @param root
	 *            The node to start from. RootAnnotations are required for loop
	 *            detection etc.
	 */
	public void processRcfg(RootNode root) {
		mErrorLocs.clear();
		mReachedErrorLocs.clear();
		mRecursionEntryNodes.clear();

		mContinueProcessing = true;

		// state change logger
		if (mStateChangeLogConsole || mStateChangeLogFile) {
			String fileDir = "";
			String fileName = "";
			if (mStateChangeLogFile) {
				File sourceFile = new File(root.getFilename());
				DateFormat dfm = new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss");
				fileName = sourceFile.getName() + "_AI_" + dfm.format(new Date()) + ".txt";
				if (mStateChangeLogUseSourcePath) {
					fileDir = sourceFile.getParent();
				} else {
					fileDir = null;
				}
				if (fileDir == null) {
					fileDir = new File(mStateChangeLogPath).getAbsolutePath();
				}
			}
			StateChangeLogger scl = new StateChangeLogger(mLogger, mStateChangeLogConsole, mStateChangeLogFile, fileDir
					+ File.separatorChar + fileName);
			this.registerStateChangeListener(scl);
		}

		// numbers for widening
		mNumbersForWidening.clear();
		mNumbersForWidening.addAll(mFixedNumbersForWidening);
		// collect literals if preferences say so
		if (mWideningAutoNumbers) {
			LiteralCollector literalCollector = new LiteralCollector(root, mLogger);
			mNumbersForWidening.addAll(literalCollector.getResult());
		}

		// domain factories chosen in preferences
		mIntDomainFactory = makeDomainFactory(mIntDomainID, mIntWideningOpName, mIntMergeOpName);
		mRealDomainFactory = makeDomainFactory(mRealDomainID, mRealWideningOpName, mRealMergeOpName);
		mBoolDomainFactory = makeDomainFactory(mBoolDomainID, mBoolWideningOpName, mBoolMergeOpName);
		mBitVectorDomainFactory = makeDomainFactory(mBitVectorDomainID, mBitVectorWideningOpName, mBitVectorMergeOpName);
		mStringDomainFactory = makeDomainFactory(mStringDomainID, mStringWideningOpName, mStringMergeOpName);

		// fetch loop nodes with their entry/exit edges
		RCFGLoopDetector loopDetector = new RCFGLoopDetector(mServices);
		try {
			loopDetector.process(root);
		} catch (Throwable e1) {
			e1.printStackTrace();
		}
		mLoopEntryNodes = loopDetector.getResult();

		mLogger.debug("Loop information:");
		for (ProgramPoint pp : mLoopEntryNodes.keySet()) {
			Map<RCFGEdge, RCFGEdge> loopsie = mLoopEntryNodes.get(pp);
			for (Entry<RCFGEdge, RCFGEdge> e : loopsie.entrySet()) {
				mLogger.debug(String.format("Loop: %s -> %s -> ... -> %s -> %s", pp, (ProgramPoint) e.getKey()
						.getTarget(), (ProgramPoint) e.getValue().getSource(), pp));
			}
		}

		// preprocessor annotation: get symboltable
		PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null) {
			mLogger.error("No symbol table found on given RootNode.");
			return;
		}
		mSymbolTable = pa.getSymbolTable();

		mBoogieVisitor = new AbstractInterpretationBoogieVisitor(mLogger, mSymbolTable, mIntDomainFactory,
				mRealDomainFactory, mBoolDomainFactory, mBitVectorDomainFactory, mStringDomainFactory);

		// root annotation: get location list, error locations
		RootAnnot ra = root.getRootAnnot();

		Map<String, ProgramPoint> entryNodes = ra.getEntryNodes();
		ProgramPoint mainEntry = entryNodes.get(mMainMethodName);

		// check for ULTIMATE.start and recursive methods
		for (String s : entryNodes.keySet()) {
			ProgramPoint entryNode = entryNodes.get(s);
			// check for ULTIMATE.start
			if (entryNode.getProcedure().startsWith(mUltimateStartProcName))
				mainEntry = entryNode;
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
		for (String s : errorLocMap.keySet())
			mErrorLocs.addAll(errorLocMap.get(s));

		// add entry node of Main procedure / any if no Main() exists
		for (RCFGEdge e : root.getOutgoingEdges()) {
			if (e instanceof RootEdge) {
				RCFGNode target = e.getTarget();
				if ((mainEntry == null) || (target == mainEntry)) {
					AbstractState state = new AbstractState(mLogger, mIntDomainFactory, mRealDomainFactory,
							mBoolDomainFactory, mBitVectorDomainFactory, mStringDomainFactory);
					if (target instanceof ProgramPoint) {
						CallStatement mainProcMockStatement = new CallStatement(null, false, null,
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
		if (mReachedErrorLocs.isEmpty()) {
			if (mContinueProcessing)
				reportSafeResult();
			else if (!mServices.getProgressMonitorService().continueProcessing())
				reportTimeoutResult();
		}
	}

	/**
	 * Visit edges as long as there are edges in m_edgesToVisit
	 */
	protected void visitNodes() {
		while (!mNodesToVisit.isEmpty()) {
			RCFGNode node = (RCFGNode) mNodesToVisit.poll();
			if (node != null) {
				mCallStatementsAtCalls.clear();
				mCallStatementsAtSummaries.clear();

				List<AbstractState> statesAtNode = mStates.get(node);
				mLogger.debug(String.format("---- PROCESSING NODE %S ----", (ProgramPoint) node));
				// process all unprocessed states at the node
				boolean hasUnprocessed = true;
				while (hasUnprocessed && mContinueProcessing) {
					AbstractState unprocessedState = null;
					for (AbstractState s : statesAtNode) {
						if (!s.isProcessed()) {
							unprocessedState = s;
							break;
						}
					}
					if (unprocessedState != null) {
						mCurrentState = unprocessedState;
						mCurrentState.setProcessed(true);

						mCurrentNode = node;

						for (RCFGEdge e : node.getOutgoingEdges()) {
							mResultingState = null;
							visit(e);
						}
					} else {
						hasUnprocessed = false;
					}
					// abort if asked to cancel
					mContinueProcessing = mContinueProcessing
							&& mServices.getProgressMonitorService().continueProcessing();
				} // hasUnprocessed

				// remove states if they aren't needed for possible widening
				// anymore
				if (node.getIncomingEdges().size() <= 1)
					mStates.remove(node);

				if (!mCallStatementsAtCalls.containsAll(mCallStatementsAtSummaries))
					reportUnsupportedSyntaxResult(node, "Abstract interpretation plug-in can't verify "
							+ "programs which contain procedures without implementations.");

				if (!mContinueProcessing)
					break;
			}
		}
	}

	/*protected List<UnprovableResult<RcfgElement, CodeBlock, Expression>> visitNodes(boolean runsOnNWA) {
		List<UnprovableResult<RcfgElement, CodeBlock, Expression>> result = new ArrayList<UnprovableResult<RcfgElement, CodeBlock, Expression>>();
		RCFGNode node = (RCFGNode) mNodesToVisit.poll();

		if (node != null) {
			mCallStatementsAtCalls.clear();
			mCallStatementsAtSummaries.clear();

			List<AbstractState> statesAtNode = mStates.get(node);
			mLogger.debug(String.format("---- PROCESSING NODE %S ----", (ProgramPoint) node));
			// process all unprocessed states at the node
			boolean hasUnprocessed = true;
			while (hasUnprocessed && mContinueProcessing) {
				AbstractState unprocessedState = null;
				for (AbstractState s : statesAtNode) {
					if (!s.isProcessed()) {
						unprocessedState = s;
						break;
					}
				}
				if (unprocessedState != null) {
					mCurrentState = unprocessedState;
					mCurrentState.setProcessed(true);

					mCurrentNode = node;

					for (RCFGEdge e : node.getOutgoingEdges()) {
						mResultingState = null;
						result.add(visit(e, runsOnNWA));
					}
				} else {
					hasUnprocessed = false;
				}
				// abort if asked to cancel
				mContinueProcessing = mContinueProcessing && mServices.getProgressMonitorService().continueProcessing();
			} // hasUnprocessed

			// remove states if they aren't needed for possible widening anymore
			if (node.getIncomingEdges().size() <= 1)
				mStates.remove(node);

			if (!mCallStatementsAtCalls.containsAll(mCallStatementsAtSummaries))
				reportUnsupportedSyntaxResult(node, "Abstract interpretation plug-in can't verify "
						+ "programs which contain procedures without implementations.");

			if (mContinueProcessing)
				result.addAll(visitNodes(runsOnNWA)); // repeat until
														// m_nodesToVisit is
														// empty
		}
		return result;
	}*/

	@Override
	protected void visit(RCFGEdge e) {
		mLogger.debug("Visiting: " + e.getSource() + " -> " + e.getTarget());

		super.visit(e);

		String evaluationError = mBoogieVisitor.getErrorMessage();
		if (!evaluationError.isEmpty()) {
			reportUnsupportedSyntaxResult(e, evaluationError);

			mResultingState = null; // return, abort, stop.
		}

		if (mResultingState == null)
			return; // do not process target node!

		Map<RCFGEdge, RCFGEdge> loopEdges = mLoopEntryNodes.get(mCurrentNode);
		if (loopEdges != null) {
			RCFGEdge exitEdge = loopEdges.get(e);
			if (exitEdge != null)
				mResultingState.pushLoopEntry((ProgramPoint) mCurrentNode, exitEdge);
		}

		mResultingState.addCodeBlockToTrace((CodeBlock) e);

		RCFGNode targetNode = e.getTarget();
		if (targetNode != null) {
			if (putStateToNode(mResultingState, targetNode, e)) {
				ProgramPoint pp = (ProgramPoint) targetNode;
				if (mErrorLocs.contains(pp) && !mReachedErrorLocs.contains(pp)) {
					mReachedErrorLocs.add(pp);
					reportErrorResult(pp, mResultingState, false);
				} else {
					if (!mNodesToVisit.contains(targetNode)) {
						mNodesToVisit.add(targetNode);
					}
				}
			}
		}
	}

	/*protected UnprovableResult<RcfgElement, CodeBlock, Expression> visit(RCFGEdge e, boolean runsOnNWA) {
		UnprovableResult<RcfgElement, CodeBlock, Expression> result = null;
		mLogger.debug("Visiting: " + e.getSource() + " -> " + e.getTarget());

		super.visit(e);

		String evaluationError = mBoogieVisitor.getErrorMessage();
		if (!evaluationError.isEmpty()) {
			reportUnsupportedSyntaxResult(e, evaluationError);

			mResultingState = null; // return, abort, stop.
		}

		if (mResultingState == null)
			return result; // do not process target node!

		Map<RCFGEdge, RCFGEdge> loopEdges = mLoopEntryNodes.get(mCurrentNode);
		if (loopEdges != null) {
			RCFGEdge exitEdge = loopEdges.get(e);
			if (exitEdge != null)
				mResultingState.pushLoopEntry((ProgramPoint) mCurrentNode, exitEdge);
		}

		mResultingState.addCodeBlockToTrace((CodeBlock) e);

		RCFGNode targetNode = e.getTarget();
		if (targetNode != null) {
			if (putStateToNode(mResultingState, targetNode, e)) {
				ProgramPoint pp = (ProgramPoint) targetNode;
				if (mErrorLocs.contains(pp) && !mReachedErrorLocs.contains(pp)) {
					mReachedErrorLocs.add(pp);

					result = reportErrorResult(pp, mResultingState, runsOnNWA);
				} else {
					if (!mNodesToVisit.contains(targetNode)) {
						mNodesToVisit.add(targetNode);
					}
				}
			}
		}
		return result;
	}*/

	@Override
	protected void visit(RootEdge e) {
		mLogger.debug("> RootEdge");

		super.visit(e);

		mResultingState = mCurrentState.copy();
	}

	@Override
	protected void visit(CodeBlock c) {
		mLogger.debug("> CodeBlock START");

		super.visit(c);

		mLogger.debug("< CodeBlock END");
	}

	@Override
	protected void visit(Call c) {
		mLogger.debug("> Call");

		CallStatement cs = c.getCallStatement();
		mCallStatementsAtCalls.add(cs);
		mResultingState = mBoogieVisitor.evaluateStatement(cs, mCurrentState);
	}

	@Override
	protected void visit(GotoEdge c) {
		mLogger.debug("> GotoEdge");

		mResultingState = mCurrentState.copy();
	}

	@Override
	protected void visit(ParallelComposition c) {
		mLogger.debug("> ParallelComposition START");

		Collection<CodeBlock> blocks = c.getBranchIndicator2CodeBlock().values();

		// process all blocks wrt. the current state and merge all resulting
		// states
		AbstractState mergedState = null;
		for (CodeBlock block : blocks) {
			mLogger.debug(String.format("Parallel: %s", block.getPrettyPrintedStatements()));
			visit(block);
			if (mResultingState != null) {
				if (mergedState == null) {
					mergedState = mResultingState;
				} else {
					mergedState = mergedState.merge(mResultingState);
				}
			}
		}
		mResultingState = mergedState;

		mLogger.debug("< ParallelComposition END");
	}

	@Override
	protected void visit(Return c) {
		mLogger.debug("> Return");

		mResultingState = mBoogieVisitor.evaluateReturnStatement(c.getCallStatement(), mCurrentState);
	}

	@Override
	protected void visit(SequentialComposition c) {
		mLogger.debug("> SequentialComposition START");

		AbstractState currentState = mCurrentState;
		// backup, as the member variable is manipulated during iterating the
		// CodeBlocks

		CodeBlock[] blocks = c.getCodeBlocks();

		for (int i = 0; i < blocks.length; i++) {
			visit(blocks[i]);
			mCurrentState = mResultingState;
			// so the next CodeBlocks current state is this states' result state

			if (mResultingState == null)
				break;
		}

		mCurrentState = currentState;

		mLogger.debug("< SequentialComposition END");
	}

	@Override
	protected void visit(Summary c) {
		mLogger.debug("> Summary");

		mCallStatementsAtSummaries.add(c.getCallStatement());
		mResultingState = null; // do not process target node (ignore summary
								// edges)
	}

	@Override
	protected void visit(StatementSequence c) {
		mLogger.debug("> StatementSequence");

		List<Statement> statements = c.getStatements();

		if (statements.size() > 0) {
			mResultingState = mCurrentState;
			for (int i = 0; i < statements.size(); i++) {
				Statement s = statements.get(i);
				if (s != null) {
					mResultingState = mBoogieVisitor.evaluateStatement(s, mResultingState);
					if (mResultingState == null)
						break;
				}
			}
		}
	}

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

	/**
	 * Notifies all state change listeners of a state change
	 * 
	 * @param viaEdge
	 * @param oldStates
	 * @param newState
	 * @param mergedState
	 */
	private void notifyStateChangeListeners(RCFGEdge viaEdge, List<AbstractState> oldStates, AbstractState newState,
			AbstractState mergedState) {
		for (IAbstractStateChangeListener l : mStateChangeListeners) {
			List<AbstractState> statesCopy = new ArrayList<AbstractState>(oldStates.size());
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
	private UnprovableResult<RcfgElement, CodeBlock, Expression> reportErrorResult(ProgramPoint location,
			AbstractState state, boolean runsOnNWA) {
		
		//PrintWriter writer;
		//try {
		//	writer = new PrintWriter(new FileOutputStream(new File("E:\\AbstractInterpretation.txt"), true));
		RcfgProgramExecution programExecution = new RcfgProgramExecution(state.getTrace(),
				new HashMap<Integer, ProgramState<Expression>>(), null);

		UnprovableResult<RcfgElement, CodeBlock, Expression> result = new UnprovableResult<RcfgElement, CodeBlock, Expression>(
				Activator.s_PLUGIN_NAME, location, mServices.getBacktranslationService(), programExecution);

		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, result);
		

		if (mStopAfterAnyError) {
			mContinueProcessing = false;
			mLogger.info(String.format("Abstract interpretation finished after reaching error location %s",
					location.getLocationName()));
		} else if (mStopAfterAllErrors) {
			if (mReachedErrorLocs.containsAll(mErrorLocs))
				mContinueProcessing = false;
			mLogger.info("Abstract interpretation finished after reaching all error locations");
		}
		//TODO Fabian
		/*String wr = location.getProcedure();
		wr = wr + " "+state.toString() + " "+result.getFailurePath().toString() + " " + result.toString();
		writer.append(wr);
		writer.append("\n*************\n");
		writer.close();
		return result;
		} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				return null;
		}*/
		return result;
	}

	private void reportUnsupportedSyntaxResult(IElement location, String message) {
		UnsupportedSyntaxResult<IElement> result = new UnsupportedSyntaxResult<IElement>(location,
				Activator.s_PLUGIN_NAME, mServices.getBacktranslationService(), message);

		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, result);

		mContinueProcessing = false;
	}

	/**
	 * Reports safety of the program as the plugin's result
	 */
	private void reportSafeResult() {
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID,
				new AllSpecificationsHoldResult(Activator.s_PLUGIN_NAME, "No error locations were reached."));
	}

	/**
	 * Reports a timeout of the analysis
	 */
	private void reportTimeoutResult() {
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID,
				new TimeoutResult(Activator.s_PLUGIN_NAME, "Analysis aborted."));
	}

	/**
	 * Get preferences from the preference store
	 */
	private void fetchPreferences() {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);

		mMainMethodName = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_MAIN_METHOD_NAME);

		mIterationsUntilWidening = prefs
				.getInt(AbstractInterpretationPreferenceInitializer.LABEL_ITERATIONS_UNTIL_WIDENING);
		mParallelStatesUntilMerge = prefs.getInt(AbstractInterpretationPreferenceInitializer.LABEL_STATES_UNTIL_MERGE);

		mWideningFixedNumbers = prefs
				.getString(AbstractInterpretationPreferenceInitializer.LABEL_WIDENING_FIXEDNUMBERS);
		mWideningAutoNumbers = prefs.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_WIDENING_AUTONUMBERS);

		mGenerateStateAnnotations = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_STATE_ANNOTATIONS);
		mStateChangeLogConsole = prefs.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_LOGSTATES_CONSOLE);
		mStateChangeLogFile = prefs.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_LOGSTATES_FILE);
		mStateChangeLogUseSourcePath = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_LOGSTATES_USESOURCEPATH);
		mStateChangeLogPath = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_LOGSTATES_PATH);

		String stopAfter = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_STOPAFTER);
		mStopAfterAnyError = (stopAfter.equals(AbstractInterpretationPreferenceInitializer.OPTION_STOPAFTER_ANYERROR));
		mStopAfterAllErrors = (stopAfter.equals(AbstractInterpretationPreferenceInitializer.OPTION_STOPAFTER_ALLERRORS));

		mIntDomainID = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_INTDOMAIN);
		mIntWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP, mIntDomainID));
		mIntMergeOpName = prefs.getString(String.format(AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mIntDomainID));

		mRealDomainID = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_REALDOMAIN);
		mRealWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP, mRealDomainID));
		mRealMergeOpName = prefs.getString(String.format(AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mRealDomainID));

		mBoolDomainID = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_BOOLDOMAIN);
		mBoolWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP, mBoolDomainID));
		mBoolMergeOpName = prefs.getString(String.format(AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mBoolDomainID));

		mBitVectorDomainID = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_BITVECTORDOMAIN);
		mBitVectorWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP, mBitVectorDomainID));
		mBitVectorMergeOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP, mBitVectorDomainID));

		mStringDomainID = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_STRINGDOMAIN);
		mStringWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP, mStringDomainID));
		mStringMergeOpName = prefs.getString(String.format(AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				mStringDomainID));
	}

	/**
	 * @param domainID
	 * @param wideningOpName
	 * @param mergeOpName
	 * @return An abstract domain factory for the abstract domain system given
	 *         by its ID
	 */
	private IAbstractDomainFactory<?> makeDomainFactory(String domainID, String wideningOpName, String mergeOpName) {
		if (domainID.equals(TopBottomDomainFactory.getDomainID()))
			return new TopBottomDomainFactory(mLogger);

		if (domainID.equals(BoolDomainFactory.getDomainID()))
			return new BoolDomainFactory(mLogger);

		if (domainID.equals(SignDomainFactory.getDomainID()))
			return new SignDomainFactory(mLogger, wideningOpName, mergeOpName);

		if (domainID.equals(IntervalDomainFactory.getDomainID()))
			return new IntervalDomainFactory(mLogger, new HashSet<String>(mNumbersForWidening), wideningOpName,
					mergeOpName);

		// default ADS: TOPBOTTOM
		mLogger.warn(String.format("Unknown abstract domain system \"%s\" chosen, using \"%s\" instead", domainID,
				TopBottomDomainFactory.getDomainID()));
		return new TopBottomDomainFactory(mLogger);
	}
}
