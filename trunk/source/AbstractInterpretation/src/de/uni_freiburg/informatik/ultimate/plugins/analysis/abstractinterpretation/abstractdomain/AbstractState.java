/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * An AbstractState represents an abstract program state, mapping variable
 * identifiers to abstract values. As variables can have different types,
 * for instance int or bool, different abstract domains may be used.
 * 
 * @author Christopher Dillo
 */
public class AbstractState {

	/**
	 * Set of nodes which are loop entries and thus apply for widening with a visit-counter for each node
	 */
	private final Map<RCFGNode, Integer> m_loopEntryNodes = new HashMap<RCFGNode, Integer>();
	
	/**
	 * Sequence of nodes passed leading to this state -> "execution trace" 
	 */
	private final List<RCFGNode> m_passedNodes = new LinkedList<RCFGNode>();
	
	/**
	 * True if the state at a node has been processed already (prevent processing the same state twice)
	 */
	private boolean m_isProcessed = false;
	
	private Logger m_logger;
	
	private IAbstractDomainFactory<?> m_numberFactory;
	private IAbstractDomainFactory<BoolValue.Bool> m_boolFactory;
	
	/**
	 * Stack of maps from variable identifiers to values. Stack levels represent scope levels,
	 * index 0 is the global scope.
	 */
	private final List<Map<String, IAbstractValue<?>>> m_values = new ArrayList<Map<String, IAbstractValue<?>>>();
	
	public AbstractState(Logger logger, IAbstractDomainFactory<?> numberFactory, IAbstractDomainFactory<BoolValue.Bool> boolFactory) {
		m_logger = logger;
		m_numberFactory = numberFactory;
		m_boolFactory = boolFactory;
		
		pushStackLayer(); // global scope
	}
	
	/**
	 * @return True iff this state contains all variables of the given state
	 * and all variable values are greater or equal to their corresponding values
	 */
	public boolean isSuper(AbstractState state) {
		// referring to this state as "greater"
		
		if (state == null)
			return false;
		
		List<Map<String, IAbstractValue<?>>> otherValues = state.getValues();
		
		// must have at least as many stack layers (scopes)
		if (m_values.size() < otherValues.size())
			return false;
		
		// for each stack layer (scope level) of the others (which may be less!)
		for (int i = 0; i < otherValues.size(); i++) {
			Map<String, IAbstractValue<?>> greaterLayer = m_values.get(i);
			Map<String, IAbstractValue<?>> smallerLayer = otherValues.get(i);
			
			// must have at least as many variables
			if (greaterLayer.size() < smallerLayer.size())
				return false;

			// check if any variable in the other state occurs and is greater in this state
			Set<String> smallerKeys = smallerLayer.keySet();
			for (String key : smallerKeys) {
				IAbstractValue<?> smallerValue = smallerLayer.get(key);
				IAbstractValue<?> greaterValue = greaterLayer.get(key); 
				
				// identifier must exist and thus have a value
				if (greaterValue == null)
					return false;
				
				// value of this state must be greater than the value of the other state
				if (!greaterValue.isSuper(smallerValue))
					return false;
			}
		}
		
		// all checks passed, this state is greater or equal to the argument state
		return true;
	}
	
	/**
	 * @return A copy of this abstract program state that is independent of this object.
	 */
	public AbstractState copy() {
		AbstractState result = new AbstractState(m_logger, m_numberFactory, m_boolFactory);
		
		for (int i = 0; i < m_values.size(); i++) {
			if (i > 0) result.pushStackLayer();
			
			Map<String, ? extends IAbstractValue<?>> layer = m_values.get(i);
			
			for (String identifier : layer.keySet())
				result.declareIdentifier(identifier, layer.get(identifier).copy());
		}
		
		for (RCFGNode node : m_loopEntryNodes.keySet())
			result.addLoopEntryNode(node, m_loopEntryNodes.get(node));
		
		for (RCFGNode node : m_passedNodes)
			result.addPassedNode(node);
		
		return result;
	}
	
	/**
	 * Merge this state with the given state using the merge operator set in the preferences
	 * @param state The state to merge with
	 * @return A new merged state
	 */
	public AbstractState merge(AbstractState state) {		
		if (state == null)
			return null;
		
		IMergeOperator<?> mergeOp = m_numberFactory.getMergeOperator();
		IWideningOperator<BoolValue.Bool> boolMergeOp = m_boolFactory.getWideningOperator();
		
		List<Map<String, IAbstractValue<?>>> otherValues = state.getValues();

		AbstractState resultingState = new AbstractState(m_logger, m_numberFactory, m_boolFactory);
		List<Map<String, IAbstractValue<?>>> resultingValues = resultingState.getValues();
		
		int maxLayerCount = Math.max(m_values.size(), otherValues.size());
		
		// for each stack layer (scope level) 
		for (int i = 0; i < maxLayerCount; i++) {
			Map<String, IAbstractValue<?>> thisLayer = (i < m_values.size()) ? m_values.get(i) : null;
			Map<String, IAbstractValue<?>> otherLayer = (i < otherValues.size()) ? otherValues.get(i) : null;
			
			if (i > 0) resultingState.pushStackLayer();
			Map<String, IAbstractValue<?>> resultingLayer = resultingValues.get(i);

			Set<String> identifiers = new HashSet<String>();
			if (thisLayer != null)
				identifiers.addAll(thisLayer.keySet());
			if (otherLayer != null)
				identifiers.addAll(otherLayer.keySet());

			// merge values (or take the single value if only one is present)
			for (String identifier : identifiers) {
				IAbstractValue<?> thisValue = (thisLayer == null) ? null : thisLayer.get(identifier);
				IAbstractValue<?> otherValue = (otherLayer == null) ? null : otherLayer.get(identifier); 

				IAbstractValue<?> resultingValue;
				if (thisValue == null) {
					resultingValue = otherValue.copy();
				} else if (otherValue == null) {
					resultingValue = thisValue.copy();
				} else {
					if (thisValue instanceof BoolValue)
						resultingValue = boolMergeOp.apply(thisValue, otherValue);
					else
						resultingValue = mergeOp.apply(thisValue, otherValue);
				}
				if (resultingValue != null)
					resultingLayer.put(identifier, resultingValue);
			}
		}
		
		// add passed loop entry nodes with count
		for (RCFGNode node : m_loopEntryNodes.keySet())
			resultingState.addLoopEntryNode(node, m_loopEntryNodes.get(node));
		for (RCFGNode node : state.m_loopEntryNodes.keySet())
			resultingState.addLoopEntryNode(node, state.m_loopEntryNodes.get(node));

		// add passed nodes of resultingState : take longer trace
		List<RCFGNode> passedNodes = (m_passedNodes.size() >= state.m_passedNodes.size()) ? m_passedNodes : state.m_passedNodes;
		for (RCFGNode node : passedNodes)
			resultingState.addPassedNode(node);
		
		return resultingState;
	}
	
	/**
	 * Widen this state with the given state using the given widening operator set in the preferences
	 * @param state The state to merge with
	 * @return A new widened state: (the given state) wideningOp (this state)
	 */
	public AbstractState widen(AbstractState state) {
		
		if (state == null)
			return null;
		
		IWideningOperator<?> wideningOp = m_numberFactory.getWideningOperator();
		IWideningOperator<BoolValue.Bool> boolWideningOp = m_boolFactory.getWideningOperator();
		
		List<Map<String, IAbstractValue<?>>> otherValues = state.getValues();

		AbstractState resultingState = new AbstractState(m_logger, m_numberFactory, m_boolFactory);
		List<Map<String, IAbstractValue<?>>> resultingValues = resultingState.getValues();
		
		int maxLayerCount = Math.max(m_values.size(), otherValues.size());
		
		// for each stack layer (scope level) 
		for (int i = 0; i < maxLayerCount; i++) {
			Map<String, IAbstractValue<?>> thisLayer = (i < m_values.size()) ? m_values.get(i) : null;
			Map<String, IAbstractValue<?>> otherLayer = (i < otherValues.size()) ? otherValues.get(i) : null;
			
			if (i > 0) resultingState.pushStackLayer();
			Map<String, IAbstractValue<?>> resultingLayer = resultingValues.get(i);

			Set<String> identifiers = new HashSet<String>();
			if (thisLayer != null)
				identifiers.addAll(thisLayer.keySet());
			if (otherLayer != null)
				identifiers.addAll(otherLayer.keySet());

			// widen values: thisValue wideningOp otherValue
			for (String identifier : identifiers) {
				IAbstractValue<?> thisValue = (thisLayer == null) ? null : thisLayer.get(identifier);
				IAbstractValue<?> otherValue = (otherLayer == null) ? null : otherLayer.get(identifier); 

				IAbstractValue<?> resultingValue = null;
				if (thisValue == null) {
					resultingValue = otherValue.copy();
					m_logger.warn(String.format("Widening encountered a missing value for %s in the old state.", identifier));
				} else if (otherValue == null) {
					m_logger.error(String.format("Widening failed with a missing value for %s in the new state.", identifier));
				} else {
					if (thisValue instanceof BoolValue)
						resultingValue = boolWideningOp.apply(thisValue, otherValue);
					else
						resultingValue = wideningOp.apply(thisValue, otherValue);
				}
				if (resultingValue != null)
					resultingLayer.put(identifier, resultingValue);
			}
		}
		
		// add passed loop entry nodes with count
		Map<RCFGNode, Integer> loopEntryNodes = (m_loopEntryNodes.size() >= state.m_loopEntryNodes.size()) ? m_loopEntryNodes : state.m_loopEntryNodes;
		for (RCFGNode node : loopEntryNodes.keySet()) 
			resultingState.addLoopEntryNode(node, loopEntryNodes.get(node));

		// add passed nodes of resultingState
		List<RCFGNode> passedNodes = (m_passedNodes.size() >= state.m_passedNodes.size()) ? m_passedNodes : state.m_passedNodes;
		for (RCFGNode node : passedNodes)
			resultingState.addPassedNode(node);
		
		return resultingState;
	}
	
	/**
	 * @param identifier
	 * @return The uppermost layer of the stack which contains a key for the given identifier
	 */
	private Map<String, IAbstractValue<?>> getTopmostLayerWithIdentifier(String identifier) {
		int layerNumber = m_values.size() - 1;
		Map<String, IAbstractValue<?>> layerMap = null;
		
		boolean found = false;
		
		while (!found && (layerNumber >= 0)) {
			layerMap = m_values.get(layerNumber);
			found = layerMap.containsKey(identifier);
			layerNumber--;
		}
		
		return found ? layerMap : null;
	}

	/**
	 * @return The number of stack levels
	 */
	public int getStackSize() {
		return m_values.size();
	}
	
	/**
	 * Creates a new empty symbol table and puts it on the top of the stack
	 */
	public void pushStackLayer() {
		m_values.add(new HashMap<String, IAbstractValue<?>>());
	}
	
	/**
	 * Removes the topmost symbol table from the stack unless it is the only layer
	 * @return True if there was a table to pop, false if the stack only has a single layer
	 */
	public boolean popStackLayer() {
		int size = m_values.size();
		
		if (size <= 1)
			return false;
		
		m_values.remove(size - 1);
		return true;
	}
	
	/**
	 * Assigns the given value to the topmost occurance of the identifier in the stack.
	 * @param identifier An existing identifier
	 * @param value The new value
	 * @return True iff a layer with the given identifier exists so the value could be written
	 */
	public boolean writeValue(String identifier, IAbstractValue<?> value) {
		Map<String, IAbstractValue<?>> layer = getTopmostLayerWithIdentifier(identifier);
		
		if (layer == null) {
			// TODO: only do this if it actually is a new declaration on a new scope level, not an undeclared variable?
			m_logger.debug(String.format("New variable %s at scope level %d", identifier, getStackSize()));
			return declareIdentifier(identifier, value);
		}
		
		layer.put(identifier, value);
		
		return true;
	}
	
	/**
	 * @param identifier The identifier whose value is to be retrieved
	 * @return The value associated with the identifier on the topmost layer it occurs, or null if it is not found
	 */
	public IAbstractValue<?> readValue(String identifier) {
		Map<String, IAbstractValue<?>> layer = getTopmostLayerWithIdentifier(identifier);
		
		if (layer == null)
			return null;
		
		return layer.get(identifier);
	}
	
	/**
	 * Generates a new mapping for the given identifier on the topmost stack level if it does not exist there already.
	 * @param identifier The new identifier to declare
	 * @param initialValue Its initial value
	 * @return True if it could be declared, false if such an identifier already exists on the top layer or the stack is empty
	 */
	public boolean declareIdentifier(String identifier, IAbstractValue<?> initialValue) {
		int size = m_values.size();
		
		if (size <= 0)
			return false;
		
		Map<String, IAbstractValue<?>> topLayer = m_values.get(size - 1);
		
		if (topLayer.containsKey(identifier))
			return false;
		
		topLayer.put(identifier, initialValue);
		
		return true;
	}
	
	/**
	 * @param node A loop entry node to note for detecting applicability of widening
	 */
	public void addLoopEntryNode(RCFGNode node) {
		if (m_loopEntryNodes.containsKey(node)) {
			// visited before -> increase counter
			addLoopEntryNode(node, m_loopEntryNodes.get(node) + 1);
		} else {
			// add with count of 1 for the first visit
			addLoopEntryNode(node, 1);
		}
	}
	
	/**
	 * @param node A loop entry node to note for detecting applicability of widening
	 * @param visitCount The number of times this node was visited during creating this state
	 */
	public void addLoopEntryNode(RCFGNode node, Integer visitCount) {
		if (!m_loopEntryNodes.containsKey(node) || (m_loopEntryNodes.get(node) < visitCount)) {
			m_loopEntryNodes.put(node, visitCount);
		}
	}

	/**
	 * @param node A loop entry node to note ignore for detecting applicability of widening
	 */
	public void removeLoopEntryNode(RCFGNode node) {
		m_loopEntryNodes.remove(node);
	}
	
	/**
	 * @param node A loop entry node to check
	 * @return The number of times the given node was passed during calculating this state
	 */
	public int getLoopEntryVisitCount(RCFGNode node) {
		Integer count = m_loopEntryNodes.get(node);
		return count == null ? 0 : count.intValue();
	}
	
	/**
	 * @return The set of loop entry nodes with visit counts
	 */
	public Map<RCFGNode, Integer> getLoopEntryNodes() {
		return m_loopEntryNodes;
	}
	
	/**
	 * Add a node to the list of passed nodes for trace reconstruction
	 * @param node A node to add
	 * @return True if the node was successfully added
	 */
	public boolean addPassedNode(RCFGNode node) {
		return m_passedNodes.add(node);
	}
	
	/**
	 * @return A list of nodes passed during creating this state
	 */
	public List<RCFGNode> getPassedNodes() {
		return m_passedNodes;
	}
	
	/**
	 * @param predecessor
	 * @return True iff this state's passed node list contains and begins with all passed nodes of the
	 * given state in the same order, plus at least one more node
	 */
	public boolean isSuccessor(AbstractState predecessor) {
		if (m_passedNodes.size() <= predecessor.m_passedNodes.size())
			return false;
		
		for (int i = 0; i < predecessor.m_passedNodes.size(); i++) {
			if (!m_passedNodes.get(i).equals(predecessor.m_passedNodes.get(i)))
				return false;
		}
		
		return true;
	}
	
	/**
	 * @return The stack as a list, bottom layer at index 0.
	 */
	public List<Map<String, IAbstractValue<?>>> getValues() {
		return m_values;
	}
	
	/**
	 * @return True if the state is set as having been processed already
	 */
	public boolean isProcessed() {
		return m_isProcessed;
	}
	
	/**
	 * @param processed Set that the state has been processed already
	 */
	public void setProcessed(boolean processed) {
		m_isProcessed = processed;
	}
}
