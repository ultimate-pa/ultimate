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
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractInterpretationBoogieVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
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

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpreter extends RCFGEdgeVisitor {

	public final static Logger s_logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	public static IAbstractDomainFactory s_domainFactory;
	
	private final LinkedList<RCFGNode> m_nodesToVisit = new LinkedList<RCFGNode>();
	
	private final Map<RCFGNode, List<AbstractState>> m_states = new HashMap<RCFGNode, List<AbstractState>>();
	
	private AbstractState m_currentState, m_resultingState;
	
	private final AbstractInterpretationBoogieVisitor m_boogieVisitor = new AbstractInterpretationBoogieVisitor();
	
	private final Set<IAbstractStateChangeListener> m_stateChangeListeners = new HashSet<IAbstractStateChangeListener>();
	
	public AbstractInterpreter() {
		// TODO: domain factory from preferences!
		s_domainFactory = new SignDomainFactory();
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
		// TODO: Merge / widen...
		List<AbstractState> statesAtNode = m_states.get(node);
		if (statesAtNode != null) {
			// append state if no superstate exists
			for (AbstractState s : statesAtNode)
				if (s.isSuper(state)) return false;
			statesAtNode.add(state);
			notifyStateChangeListeners(node, statesAtNode, state, null); // TODO: merged state...
			annotateElement(node, statesAtNode); // TODO: preference...
			return true;
		} else {
			// new state list with the given state
			statesAtNode = new LinkedList<AbstractState>();
			statesAtNode.add(state);
			m_states.put(node, statesAtNode);
			notifyStateChangeListeners(node, statesAtNode, state, null); // TODO: merged state...
			annotateElement(node, statesAtNode); // TODO: preference...
			return true;
		}
	}
	
	/**
	 * Throw in the rootnode from where to start and the RCFG will be processed.
	 * @param root The node to start from. Should be the main method root thing.
	 */
	public void processRcfg(RCFGNode root) {
		if (root instanceof RootNode) {
			// add outgoing nodes
			for (RCFGEdge e : root.getOutgoingEdges()) {
				// TODO: get the one root edge to the main function
				if (e instanceof RootEdge) {
					RCFGNode target = e.getTarget();
					putStateToNode(new AbstractState(), target);
					m_nodesToVisit.add(target);
				}
			}
		} else {
			putStateToNode(new AbstractState(), root);
			m_nodesToVisit.add(root);
		}
		visitNodes();
	}
	
	/**
	 * Visit edges as long as there are edges in m_edgesToVisit
	 */
	protected void visitNodes() {
		RCFGNode node = m_nodesToVisit.poll();
		if (node != null){
			List<AbstractState> statesAtNode = m_states.get(node);
			m_currentState = statesAtNode.get(statesAtNode.size() - 1); // TODO: Merge / widen...
			m_resultingState = null;
			
			if (m_currentState == null) {
				s_logger.warn("No state found at node " + node.toString());
			} else {
				for (RCFGEdge e : node.getOutgoingEdges())
					visit(e);
			}
			
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
			if (!m_nodesToVisit.contains(targetNode)) {
				if (putStateToNode(m_resultingState, targetNode))
					m_nodesToVisit.add(targetNode);
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
			if (mergedState == null) {
				mergedState = m_resultingState;
			} else {
				mergedState.merge(m_resultingState);
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
				if (s != null)
					m_resultingState = m_boogieVisitor.evaluateStatement(s, m_resultingState);
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
}
