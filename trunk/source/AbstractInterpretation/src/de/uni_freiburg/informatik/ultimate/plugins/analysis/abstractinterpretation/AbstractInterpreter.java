/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractDomainRegistry;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractInterpretationBoogieVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.preferences.AbstractInterpretationPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpreter extends RCFGEdgeVisitor {

	private final static Logger s_logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private static IAbstractDomainFactory s_domainFactory;

	private static BoolDomainFactory s_boolDomainFactory;
	
	private final LinkedList<RCFGNode> m_nodesToVisit = new LinkedList<RCFGNode>();
	
	private final Map<RCFGNode, List<AbstractState>> m_states = new HashMap<RCFGNode, List<AbstractState>>();
	
	private AbstractState m_currentState, m_resultingState;
	
	private final AbstractInterpretationBoogieVisitor m_boogieVisitor = new AbstractInterpretationBoogieVisitor();
	
	private final Set<IAbstractStateChangeListener> m_stateChangeListeners = new HashSet<IAbstractStateChangeListener>();
	
	private final Set<RCFGNode> m_reachedErrorLocs = new HashSet<RCFGNode>();
	
	private final Set<ProgramPoint> m_loopEntryNodes = new HashSet<ProgramPoint>();
	
	// for preferences
	private static int s_iterationsUntilWidening;
	private static int s_parallelStatesUntilMerge;
	private static boolean s_StateAnnotations;
	private static String s_numberDomainID;
	private static String s_numberWideningOpName;
	private static String s_numberMergeOpName;
	
	public AbstractInterpreter() {
		fetchPreferences();
		
		// number domain factory chosen in preferences
		try {
			s_domainFactory = AbstractDomainRegistry.getDomainFactory(s_numberDomainID).newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			e.printStackTrace();
		}
		
		// factories which are present independent from preferences
		s_boolDomainFactory = new BoolDomainFactory();
	}
	
	/**
	 * @return The logger for the AbstractInterpretation plugin
	 */
	public static Logger getLogger() {
		return s_logger;
	}

	/**
	 * @return The domain factory which is to be used to generate objects specific to the chosen abstract domain for numbers
	 */
	public static IAbstractDomainFactory getNumberDomainFactory() {
		return s_domainFactory;
	}

	/**
	 * @return The domain factory which is to be used to generate objects for the boolean abstract domain
	 * which is used side-by-side with the domain chosen for numbers.
	 */
	public static BoolDomainFactory getBoolDomainFactory() {
		return s_boolDomainFactory;
	}

	/**
	 * Adds an AbstractInterpretationAnnotation with states at the given location IElement
	 * @param element The location of the given states
	 * @param states The states at the given location
	 */
	private void annotateElement(IElement element, List<AbstractState> states) {
		AbstractInterpretationAnnotations anno = new AbstractInterpretationAnnotations(states);
		anno.annotate(element);
	}
	
	/**
	 * Adds a program state to a node's list of states
	 * @param node The node that state belongs to
	 * @param state The program state to put on the node 
	 * @return True if the state was added, false if not (when a superstate is at the node)
	 */
	private boolean putStateToNode(AbstractState state, RCFGNode node) {
		List<AbstractState> statesAtNode = m_states.get(node);
		if (statesAtNode != null) {
			AbstractState newState = state;
			List<AbstractState> statesAtNodeBackup = new ArrayList<AbstractState>(statesAtNode);
			
			// check for loop entry / widening
			ProgramPoint pp = (ProgramPoint) node;
			if ((pp != null) && m_loopEntryNodes.contains(pp)) {
				newState.addLoopEntryNode(node);
				int visits = newState.getLoopEntryVisitCount(node);
				
				if (visits > getIterationsUntilWidening()) {
					// fetch old state, apply widening, discard old state
					AbstractState oldState = null;
					for (AbstractState s : statesAtNode) {
						if (s.isProcessed() && (s.getLoopEntryVisitCount(node) > 0)) {
							oldState = s;
							break;
						}
					}
					if (oldState != null) {
						newState = newState.widen(oldState);
						statesAtNode.remove(oldState);
					}
				}
			}
			
			Set<AbstractState> unprocessedStates = new HashSet<AbstractState>();
			for (AbstractState s : statesAtNode) {
				if (s.isSuper(newState)) return false; // abort if a superstate exists
				if (!s.isProcessed()) {
					if (newState.isSuper(s))
						statesAtNode.remove(s); // remove unprocessed substates of the new state
					else
						unprocessedStates.add(s); // collect unprocessed states
				}
			}
			if (unprocessedStates.size() >= getParallelStatesUntilMerge()) {
				// merge states
				for (AbstractState s : unprocessedStates) {
					statesAtNode.remove(s);
					newState = newState.merge(s);
				}
			}
			statesAtNode.add(newState);
			notifyStateChangeListeners(node, statesAtNodeBackup, state, newState);
		} else {
			// new state list with the given state
			statesAtNode = new LinkedList<AbstractState>();
			statesAtNode.add(state);
			m_states.put(node, statesAtNode);
			notifyStateChangeListeners(node, null, state, state);
		}

		if (getGenerateStateAnnotations())
			annotateElement(node, statesAtNode);
		return true;
	}
	
	/**
	 * Provide the RootNode from where to start and the RCFG will be processed.
	 * @param root The node to start from. RootAnnotations are required for loop detection etc.
	 */
	public void processRcfg(RootNode root) {
		m_reachedErrorLocs.clear();
		
		// add outgoing nodes
		for (RCFGEdge e : root.getOutgoingEdges()) {
			// TODO: get the one root edge to the main function
			if (e instanceof RootEdge) {
				RCFGNode target = e.getTarget();
				putStateToNode(new AbstractState(), target);
				m_nodesToVisit.add(target);
			}
		}
		
		m_loopEntryNodes.addAll(root.getRootAnnot().getLoopLocations().keySet());

		visitNodes();
		
		if (m_reachedErrorLocs.isEmpty()) {
			// report as safe
			reportSafeResult();
		}
	}
	
	/**
	 * Visit edges as long as there are edges in m_edgesToVisit
	 */
	protected void visitNodes() {
		RCFGNode node = m_nodesToVisit.poll();
		if (node != null) {
			List<AbstractState> statesAtNode = m_states.get(node);
			// process all unprocessed states at the node
			boolean hasUnprocessed = true;
			while (hasUnprocessed) {
				AbstractState unprocessedState = null;
				for (AbstractState s : statesAtNode) {
					if (!s.isProcessed()) {
						unprocessedState = s;
						break;
					}
				}
				if (unprocessedState != null) {
					m_currentState = unprocessedState;
					m_currentState.setProcessed(true);
					
					if (m_currentState == null) {
						s_logger.warn("No state found at node " + node.toString());
					} else {
						for (RCFGEdge e : node.getOutgoingEdges()) {
							m_resultingState = null;
							visit(e);
							if (m_resultingState != null)
								m_resultingState.addPassedNode(node);
						}
					}
				} else {
					hasUnprocessed = false;
				}
			} // loop
			
			visitNodes(); // repeat until m_nodesToVisit is empty
		}
	}

	@Override
	protected void visit(RCFGEdge e) {
		s_logger.debug("Visiting: " + e.getSource() + " -> " + e.getTarget());
		
		super.visit(e);
		
		// TODO: Actual proper state processing
		
		if (m_resultingState == null) return; // do not process target node!
		
		RCFGNode targetNode = e.getTarget();
		if (targetNode != null) {
			if (putStateToNode(m_resultingState, targetNode)) {
				ProgramPoint pp = (ProgramPoint) targetNode;
				if ((pp != null) && pp.isErrorLocation() && !m_reachedErrorLocs.contains(targetNode)) {
					m_reachedErrorLocs.add(targetNode);
					reportErrorResult(targetNode, m_resultingState);
					// TODO: Abort or proceed?
				} else {
					if (!m_nodesToVisit.contains(targetNode))
						m_nodesToVisit.add(targetNode);
				}
			}
		}
	}

	@Override
	protected void visit(RootEdge e) {
		s_logger.debug("> RootEdge");
		
		super.visit(e);

		m_resultingState = m_currentState.copy();
	}
	
	@Override
	protected void visit(CodeBlock c) {
		s_logger.debug("> CodeBlock begin");
			
		super.visit(c);

		s_logger.debug("> CodeBlock end");
	}

	@Override
	protected void visit(Call c) {
		s_logger.debug("> Call");
		
		super.visit(c);

		m_resultingState = m_currentState.copy();
		m_resultingState.pushStackLayer();
	}

	@Override
	protected void visit(GotoEdge c) {
		s_logger.debug("> GotoEdge");
		
		super.visit(c);

		m_resultingState = m_currentState.copy();
	}

	@Override
	protected void visit(ParallelComposition c) {
		s_logger.debug("> ParallelComposition");
		
		super.visit(c);

		Collection<CodeBlock> blocks = c.getBranchIndicator2CodeBlock().values();
		
		// process all blocks wrt. the current state and merge all resulting states
		AbstractState mergedState = null;
		for (CodeBlock block : blocks) {
			visit(block);
			if (m_resultingState != null) {
				if (mergedState == null) {
					mergedState = m_resultingState;
				} else {
					mergedState.merge(m_resultingState);
				}
			}
		}
		m_resultingState = mergedState;
	}

	@Override
	protected void visit(Return c) {
		s_logger.debug("> Return");
		
		super.visit(c);

		m_resultingState = m_currentState.copy();
		m_resultingState.popStackLayer();
	}

	@Override
	protected void visit(SequentialComposition c) {
		s_logger.debug("> SequentialComposition");
		
		super.visit(c);
		
		AbstractState currentState = m_currentState; // backup, as the member variable is manipulated during iterating the CodeBlocks
		
		CodeBlock[] blocks = c.getCodeBlocks();
		
		for (int i = 0; i < blocks.length; i++) {
			visit(blocks[i]);
			m_currentState = m_resultingState; // so the next CodeBlocks current state is this states' result state
			if (m_resultingState == null) break;
		}
		
		m_currentState = currentState;
	}

	@Override
	protected void visit(Summary c) {
		s_logger.debug("> Summary");
		
		super.visit(c);

		m_resultingState = null; // do not process target node (ignore summary edges)
	}

	@Override
	protected void visit(StatementSequence c) {
		s_logger.debug("> StatementSequence");
		
		super.visit(c);
		
		List<Statement> statements = c.getStatements();
		
		if (statements.size() > 0) {
			m_resultingState = m_currentState;
			for (int i = 0; i < statements.size(); i++) {
				Statement s = statements.get(i);
				if (s != null) {
					m_resultingState = m_boogieVisitor.evaluateStatement(s, m_resultingState);
					if (m_resultingState == null) break;
				}
			}
		}
	}
	
	/**
	 * Add a state change listener to be notified on state changes
	 * @param listener The listener to notify
	 * @return True if it has been added, false if not, i.e. if it was already registered
	 */
	public boolean registerStateChangeListener(IAbstractStateChangeListener listener) {
		return m_stateChangeListeners.add(listener);
	}
	
	/**
	 * Remove a state change listener
	 * @param listener The listener to remove
	 * @return True if it was in the list and has been removed, false if it wasn't there to begin with
	 */
	public boolean removeStateChangeListener(IAbstractStateChangeListener listener) {
		return m_stateChangeListeners.remove(listener);
	}
	
	/**
	 * Notifies all state change listeners of a state change
	 * @param location
	 * @param oldStates
	 * @param newState
	 * @param mergedState
	 */
	private void notifyStateChangeListeners(IElement location, List<AbstractState> oldStates, AbstractState newState, AbstractState mergedState) {
		for (IAbstractStateChangeListener l : m_stateChangeListeners) {
			List<AbstractState> statesCopy = new ArrayList<AbstractState>(oldStates.size());
			statesCopy.addAll(oldStates);
			l.onStateChange(location, statesCopy, newState, mergedState);
		}
	}
	
	/**
	 * Reports a possible error as the plugin's result
	 * @param location The error location
	 * @param state The abstract state at the error location
	 */
	private void reportErrorResult(IElement location, AbstractState state) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID,
				new GenericResult(Activator.s_PLUGIN_ID, "Possible error",
						"Some program specifications may be violated", Severity.ERROR));
	}
	
	/**
	 * Reports safety of the program as the plugin's result
	 */
	private void reportSafeResult() {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID,
				new AllSpecificationsHoldResult(Activator.s_PLUGIN_ID, ""));
	}
	
	/**
	 * Get preferences from the preference store
	 */
	private void fetchPreferences() {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);

		s_iterationsUntilWidening = prefs.getInt(AbstractInterpretationPreferenceInitializer.LABEL_ITERATIONS_UNTIL_WIDENING);
		s_parallelStatesUntilMerge = prefs.getInt(AbstractInterpretationPreferenceInitializer.LABEL_STATES_UNTIL_MERGE);
		s_StateAnnotations = prefs.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_STATE_ANNOTATIONS);
		s_numberDomainID = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_ABSTRACTDOMAIN);
		s_numberWideningOpName = prefs.getString(String.format(AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP, s_numberDomainID));
		s_numberMergeOpName = prefs.getString(String.format(AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP, s_numberDomainID));
	}

	/**
	 * @return The minimum number of iterations to perform before applying widening
	 */
	public static int getIterationsUntilWidening() {
		return s_iterationsUntilWidening;
	}
	
	/**
	 * @return The maximum number of states at a node which may be processed without merging 
	 */
	public static int getParallelStatesUntilMerge() {
		return s_parallelStatesUntilMerge;
	}
	
	/**
	 * @return Whether to generate node annotations with the present abstract states
	 */
	public static boolean getGenerateStateAnnotations() {
		return s_StateAnnotations;
	}
	
	/**
	 * @return The ID of the domain chosen for numbers
	 */
	public static String getNumberDomainID() {
		return s_numberDomainID;
	}
	
	/**
	 * @return The name of the chosen widening operator
	 */
	public static String getNumberWideningOperatorName() {
		return s_numberWideningOpName;
	}
	
	/**
	 * @return The name of the chosen merge operator
	 */
	public static String getNumberMergeOperatorName() {
		return s_numberMergeOpName;
	}
}
