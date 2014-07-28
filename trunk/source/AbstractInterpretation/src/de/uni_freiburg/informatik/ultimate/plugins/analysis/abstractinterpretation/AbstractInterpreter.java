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

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractDomainRegistry;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractInterpretationBoogieVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignDomainFactory;
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

	private Logger m_logger;

	private IAbstractDomainFactory<?> m_numberDomainFactory;

	private BoolDomainFactory m_boolDomainFactory;

	private final LinkedList<RCFGNode> m_nodesToVisit = new LinkedList<RCFGNode>();

	private final Map<RCFGNode, List<AbstractState>> m_states = new HashMap<RCFGNode, List<AbstractState>>();

	private AbstractState m_currentState, m_resultingState;

	private RCFGNode m_currentNode;

	private AbstractInterpretationBoogieVisitor m_boogieVisitor;

	private final Set<IAbstractStateChangeListener> m_stateChangeListeners = new HashSet<IAbstractStateChangeListener>();

	private final Set<RCFGNode> m_reachedErrorLocs = new HashSet<RCFGNode>();

	private final Set<ProgramPoint> m_loopEntryNodes = new HashSet<ProgramPoint>();

	private AbstractDomainRegistry m_domainRegistry;

	// for preferences
	private int m_iterationsUntilWidening;
	private int m_parallelStatesUntilMerge;
	private boolean m_generateStateAnnotations;
	private String m_numberDomainID;
	private String m_numberWideningOpName;
	private String m_numberMergeOpName;

	private final IUltimateServiceProvider mServices;

	public AbstractInterpreter(IUltimateServiceProvider services, AbstractDomainRegistry domainRegistry) {
		mServices = services;
		m_logger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);

		m_domainRegistry = domainRegistry;

		fetchPreferences();

		// number domain factory chosen in preferences
		try {
			m_numberDomainFactory = m_domainRegistry.getDomainFactory(m_numberDomainID)
					.getConstructor(Logger.class, AbstractDomainRegistry.class, String.class, String.class)
					.newInstance(m_logger, m_domainRegistry, m_numberWideningOpName, m_numberMergeOpName);
		} catch (Exception e) {
			m_logger.warn(String.format("Invalid domain factory %s chosen, using default domain %s", m_numberDomainID,
					SignDomainFactory.getDomainID()));
			m_numberDomainFactory = new SignDomainFactory(m_logger, m_domainRegistry, m_numberWideningOpName,
					m_numberMergeOpName); // fallback
		}

		// factories which are present independent from preferences
		m_boolDomainFactory = new BoolDomainFactory(m_logger);

		m_boogieVisitor = new AbstractInterpretationBoogieVisitor(m_logger, m_numberDomainFactory, m_boolDomainFactory);
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
	private boolean putStateToNode(AbstractState state, RCFGNode node) {
		List<AbstractState> statesAtNode = m_states.get(node);
		if (statesAtNode != null) {
			AbstractState newState = state;
			List<AbstractState> statesAtNodeBackup = new ArrayList<AbstractState>(statesAtNode);

			// check for loop entry / widening
			boolean applyWidening = false;
			ProgramPoint pp = (ProgramPoint) node;
			if ((pp != null) && m_loopEntryNodes.contains(pp)) {
				newState.addLoopEntryNode(node);

				if (newState.getLoopEntryVisitCount(node) >= m_iterationsUntilWidening)
					applyWidening = true;
			}

			Set<AbstractState> unprocessedStates = new HashSet<AbstractState>();
			Set<AbstractState> statesToRemove = new HashSet<AbstractState>();
			for (AbstractState s : statesAtNode) {
				if (s.isSuper(newState))
					return false; // abort if a superstate exists
				if (s.isProcessed()) {
					if (newState.isSuccessor(s)) {
						// widen if possible
						if (applyWidening && (s.getLoopEntryVisitCount(node) > 0)) {
							newState = newState.widen(s);
							m_logger.debug(String.format("Widening at %s", node.toString()));
						} else {
							m_logger.debug(String.format("Not widening at %s: %s with count %d", node.toString(),
									applyWidening ? "Apply widening" : "Don't apply widening",
									s.getLoopEntryVisitCount(node)));
						}

						statesToRemove.add(s); // remove old obsolete nodes
					}
				} else {
					if (newState.isSuper(s))
						statesToRemove.add(s); // remove unprocessed substates
												// of the new state
					else
						unprocessedStates.add(s); // collect unprocessed states
				}
			}
			for (AbstractState s : statesToRemove)
				statesAtNode.remove(s);
			if (unprocessedStates.size() >= m_parallelStatesUntilMerge) {
				// merge states
				m_logger.debug(String.format("Merging at %s", node.toString()));
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

		if (m_generateStateAnnotations)
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
		m_reachedErrorLocs.clear();

		// add outgoing nodes
		for (RCFGEdge e : root.getOutgoingEdges()) {
			// TODO: get the one root edge to the main function
			if (e instanceof RootEdge) {
				RCFGNode target = e.getTarget();
				putStateToNode(new AbstractState(m_logger, m_numberDomainFactory, m_boolDomainFactory), target);
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

					m_currentNode = node;

					for (RCFGEdge e : node.getOutgoingEdges()) {
						m_resultingState = null;
						visit(e);
					}
				} else {
					hasUnprocessed = false;
				}
			} // hasUnprocessed

			visitNodes(); // repeat until m_nodesToVisit is empty
		}
	}

	@Override
	protected void visit(RCFGEdge e) {
		m_logger.debug("Visiting: " + e.getSource() + " -> " + e.getTarget());

		super.visit(e);

		if (m_resultingState == null)
			return; // do not process target node!

		m_resultingState.addPassedNode(m_currentNode);

		RCFGNode targetNode = e.getTarget();
		if (targetNode != null) {
			if (putStateToNode(m_resultingState, targetNode)) {
				ProgramPoint pp = (ProgramPoint) targetNode;
				if ((pp != null) && pp.isErrorLocation() && !m_reachedErrorLocs.contains(targetNode)) {
					m_reachedErrorLocs.add(targetNode);
					reportErrorResult(targetNode, m_resultingState);
				} else {
					if (!m_nodesToVisit.contains(targetNode))
						m_nodesToVisit.add(targetNode);
				}
			}
		}
	}

	@Override
	protected void visit(RootEdge e) {
		m_logger.debug("> RootEdge");

		super.visit(e);

		m_resultingState = m_currentState.copy();
	}

	@Override
	protected void visit(CodeBlock c) {
		m_logger.debug("> CodeBlock begin");

		super.visit(c);

		m_logger.debug("> CodeBlock end");
	}

	@Override
	protected void visit(Call c) {
		m_logger.debug("> Call");

		super.visit(c);

		m_resultingState = m_currentState.copy();
		m_resultingState.pushStackLayer();
	}

	@Override
	protected void visit(GotoEdge c) {
		m_logger.debug("> GotoEdge");

		super.visit(c);

		m_resultingState = m_currentState.copy();
	}

	@Override
	protected void visit(ParallelComposition c) {
		m_logger.debug("> ParallelComposition");

		super.visit(c);

		Collection<CodeBlock> blocks = c.getBranchIndicator2CodeBlock().values();

		// process all blocks wrt. the current state and merge all resulting
		// states
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
		m_logger.debug("> Return");

		super.visit(c);

		m_resultingState = m_currentState.copy();
		m_resultingState.popStackLayer();
	}

	@Override
	protected void visit(SequentialComposition c) {
		m_logger.debug("> SequentialComposition");

		super.visit(c);

		AbstractState currentState = m_currentState; // backup, as the member
														// variable is
														// manipulated during
														// iterating the
														// CodeBlocks

		CodeBlock[] blocks = c.getCodeBlocks();

		for (int i = 0; i < blocks.length; i++) {
			visit(blocks[i]);
			m_currentState = m_resultingState; // so the next CodeBlocks current
												// state is this states' result
												// state
			if (m_resultingState == null)
				break;
		}

		m_currentState = currentState;
	}

	@Override
	protected void visit(Summary c) {
		m_logger.debug("> Summary");

		super.visit(c);

		m_resultingState = null; // do not process target node (ignore summary
									// edges)
	}

	@Override
	protected void visit(StatementSequence c) {
		m_logger.debug("> StatementSequence");

		super.visit(c);

		List<Statement> statements = c.getStatements();

		if (statements.size() > 0) {
			m_resultingState = m_currentState;
			for (int i = 0; i < statements.size(); i++) {
				Statement s = statements.get(i);
				if (s != null) {
					m_resultingState = m_boogieVisitor.evaluateStatement(s, m_resultingState);
					if (m_resultingState == null)
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
		return m_stateChangeListeners.add(listener);
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
		return m_stateChangeListeners.remove(listener);
	}

	/**
	 * Notifies all state change listeners of a state change
	 * 
	 * @param location
	 * @param oldStates
	 * @param newState
	 * @param mergedState
	 */
	private void notifyStateChangeListeners(IElement location, List<AbstractState> oldStates, AbstractState newState,
			AbstractState mergedState) {
		for (IAbstractStateChangeListener l : m_stateChangeListeners) {
			List<AbstractState> statesCopy = new ArrayList<AbstractState>(oldStates.size());
			statesCopy.addAll(oldStates);
			l.onStateChange(location, statesCopy, newState, mergedState);
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
	private void reportErrorResult(IElement location, AbstractState state) {
		mServices.getResultService().reportResult(
				Activator.s_PLUGIN_ID,
				new GenericResult(Activator.s_PLUGIN_ID, "Possible error",
						"Some program specifications may be violated", Severity.ERROR));
	}

	/**
	 * Reports safety of the program as the plugin's result
	 */
	private void reportSafeResult() {
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID,
				new AllSpecificationsHoldResult(Activator.s_PLUGIN_ID, ""));
	}

	/**
	 * Get preferences from the preference store
	 */
	private void fetchPreferences() {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);

		m_iterationsUntilWidening = prefs
				.getInt(AbstractInterpretationPreferenceInitializer.LABEL_ITERATIONS_UNTIL_WIDENING);
		m_parallelStatesUntilMerge = prefs.getInt(AbstractInterpretationPreferenceInitializer.LABEL_STATES_UNTIL_MERGE);
		m_generateStateAnnotations = prefs
				.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_STATE_ANNOTATIONS);
		m_numberDomainID = prefs.getString(AbstractInterpretationPreferenceInitializer.LABEL_ABSTRACTDOMAIN);
		m_numberWideningOpName = prefs.getString(String.format(
				AbstractInterpretationPreferenceInitializer.LABEL_WIDENINGOP, m_numberDomainID));
		m_numberMergeOpName = prefs.getString(String.format(AbstractInterpretationPreferenceInitializer.LABEL_MERGEOP,
				m_numberDomainID));
	}
}
