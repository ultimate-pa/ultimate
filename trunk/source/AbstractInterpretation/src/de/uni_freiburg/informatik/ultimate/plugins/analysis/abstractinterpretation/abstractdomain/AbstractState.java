/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

/**
 * An AbstractState represents an abstract program state, mapping variable
 * identifiers to abstract values. As variables can have different types,
 * for instance int or bool, different abstract domains may be used.
 * 
 * @author Christopher Dillo
 */
public class AbstractState {
	
	/**
	 * Stores information on a loop stack level, that is:
	 * - The loop entry node of the current loop,
	 * - The exit edge over which the loop will be left
	 * - Iteration counts for loops nested within the current loop
	 */
	public class LoopStackElement {
		private final Object m_loopNode;
		private final RCFGEdge m_exitEdge;
		private final Map<Object, Integer> m_iterationCounts = new HashMap<Object, Integer>();
		public LoopStackElement(Object loopNode, RCFGEdge exitEdge) {
			m_loopNode = loopNode;
			m_exitEdge = exitEdge;
		}
		public Object getLoopNode() { return m_loopNode; }
		public RCFGEdge getExitEdge() { return m_exitEdge; }
		public int getIterationCount(Object loopNode) { 
			Integer count = m_iterationCounts.get(loopNode);
			if (count == null) return 0;
			return count.intValue();
		}
		public void increaseIterationCount(Object loopNode) {
			m_iterationCounts.put(loopNode, Integer.valueOf(getIterationCount(loopNode) + 1));
		}
		public LoopStackElement copy() {
			LoopStackElement result = new LoopStackElement(m_loopNode, m_exitEdge);
			for (Object p : m_iterationCounts.keySet())
				result.m_iterationCounts.put(p, m_iterationCounts.get(p));
			return result;
		}
	}
	
	public class ArrayData {
		private final String m_identifier;
		private IAbstractValue<?> m_value;
		private boolean m_unclearIndices;
		public ArrayData(String identifier) {
			m_identifier = identifier;
			m_value = null;
			m_unclearIndices = false;
		}
		public String getIdentifier() { return m_identifier; }
		public IAbstractValue<?> getValue() { return m_value; }
		public void setValue(IAbstractValue<?> value) { m_value = value; }
		public boolean getIndicesUnclear() { return m_unclearIndices; }
		public void setIndicesUnclear() { m_unclearIndices = true; }
	}
	
	public class ScopedAbstractState {
		private final CallStatement m_callStatement;
		private final Map<String, IAbstractValue<?>> m_values, m_oldValues;
		private final LinkedList<LoopStackElement> m_loopStack = new LinkedList<LoopStackElement>();
		private final Map<String, ArrayData> m_arrays;
		private boolean m_isGlobalScope = false;
		public ScopedAbstractState(CallStatement callStatement, Map<String, IAbstractValue<?>> oldValues) {
			m_callStatement = callStatement;
			m_values = new HashMap<String, IAbstractValue<?>>();
			m_oldValues = oldValues == null ? new HashMap<String, IAbstractValue<?>>() : new HashMap<String, IAbstractValue<?>>(oldValues);
			m_loopStack.add(new LoopStackElement(null, null)); // global stack element
			m_arrays = new HashMap<String, ArrayData>();
		}
		public CallStatement getCallStatement() { return m_callStatement; }
		public Map<String, IAbstractValue<?>> getValues() { return m_values; }
		public Map<String, IAbstractValue<?>> getOldValues() { return m_oldValues; }
		public LinkedList<LoopStackElement> getLoopStack() { return m_loopStack; }
		public Map<String, ArrayData> getArrays() { return m_arrays; }
		public boolean isGlobalScope() { return m_isGlobalScope; }
		public void SetIsGlobalScope(boolean isGlobalScope) { m_isGlobalScope = isGlobalScope; }
		public String toString() { return m_values.toString(); }
	}
	
	/**
	 * Sequence of nodes passed leading to this state -> "execution trace" 
	 */
	private final List<CodeBlock> m_trace = new LinkedList<CodeBlock>();
	
	/**
	 * True if the state at a node has been processed already (prevent processing the same state twice)
	 */
	private boolean m_isProcessed = false;
	
	private Logger m_logger;
	
	private IAbstractDomainFactory<?> m_intFactory;
	private IAbstractDomainFactory<?> m_realFactory;
	private IAbstractDomainFactory<?> m_boolFactory;
	private IAbstractDomainFactory<?> m_bitVectorFactory;
	private IAbstractDomainFactory<?> m_stringFactory;
	
	/**
	 * Stack of maps from variable identifiers to values. Stack levels represent scope levels,
	 * index 0 is the global scope.
	 */
	private final LinkedList<ScopedAbstractState> m_callStack = new LinkedList<ScopedAbstractState>();
	
	public AbstractState(Logger logger, IAbstractDomainFactory<?> intFactory, IAbstractDomainFactory<?> realFactory,
			IAbstractDomainFactory<?> boolFactory, IAbstractDomainFactory<?> bitVectorFactory,
			IAbstractDomainFactory<?> stringFactory) {
		m_logger = logger;
		m_intFactory = intFactory;
		m_realFactory = realFactory;
		m_boolFactory = boolFactory;
		m_bitVectorFactory = bitVectorFactory;
		m_stringFactory = stringFactory;
		
		pushStackLayer(null); // global scope
		getGlobalScope().SetIsGlobalScope(true);
		
		pushLoopEntry(null, null); // global iteration count
	}
	
	/**
	 * @return True iff this state contains all variables of the given state on all scopes
	 * and all variable values are greater or equal to their corresponding values
	 */
	public boolean isSuper(AbstractState state) {
		// referring to this state as "greater"
		
		if (state == null)
			return false;


		List<ScopedAbstractState> thisCallStack = getCallStack();
		List<ScopedAbstractState> otherCallStack = state.getCallStack();
		
		int thisCallStackSize = thisCallStack.size();
		int otherCallStackSize = otherCallStack.size();
		if (thisCallStackSize < otherCallStackSize)
			return false;
		for (int i = 1; i <= thisCallStackSize; i++) {
			ScopedAbstractState thisCSE =  i >= thisCallStackSize
					? thisCallStack.get(0)
					: thisCallStack.get(thisCallStackSize - i);
			ScopedAbstractState otherCSE =  i >= otherCallStackSize
					? otherCallStack.get(0)
					: otherCallStack.get(otherCallStackSize - i);
			
			if (!isSuper(thisCSE, otherCSE))
				return false;
		}
		
		m_logger.debug(String.format("is super? %s ~ %s", thisCallStack, otherCallStack));
		
		// all checks passed, this state is greater or equal to the argument state
		return true;
	}
	
	/**
	 * Checks if the left CSE contains all variables of the right CSE
	 * and all variable values are greater or equal to their corresponding values
	 * @param left
	 * @param right
	 * @return True iff left isSuper right
	 */
	private boolean isSuper(ScopedAbstractState left, ScopedAbstractState right) {
		// must be of the same method call and have at least as many variables
		if ((left.getCallStatement() != right.getCallStatement())
				|| (left.getValues().size() < right.getValues().size()))
			return false;

		// check if any variable in the right CSE occurs and is greater in the left CSE
		Set<String> rightKeys = right.getValues().keySet();
		for (String key : rightKeys) {
			IAbstractValue<?> rightValue = right.getValues().get(key);
			IAbstractValue<?> leftValue = left.getValues().get(key);
			
			m_logger.debug(String.format("is super? %s ~ %s", leftValue, rightValue));
			
			// identifier must exist and thus have a value
			if (leftValue == null)
				return false;
			
			// value of left CSE must be greater than the value of the right CSE
			if (!leftValue.isSuper(rightValue))
				return false;

			m_logger.debug(String.format("Is super! %s ~ %s (-:", leftValue, rightValue));
		}

		// check if any array value in the right CSE occurs and is greater in the left CSE
		rightKeys = right.getArrays().keySet();
		for (String key : rightKeys) {
			ArrayData rightData = right.getArrays().get(key);
			ArrayData leftData = left.getArrays().get(key); 
			
			// identifier must exist and thus have a value
			if (leftData == null)
				return false;
			
			// value of left CSE must be greater than the value of the right CSE
			if (!leftData.getValue().isSuper(rightData.getValue()))
				return false;
		}
		
		return true;
	}
	
	/**
	 * @return A copy of this abstract program state that is independent of this object.
	 */
	public AbstractState copy() {
		AbstractState result = new AbstractState(m_logger, m_intFactory, m_realFactory, m_boolFactory,
				m_bitVectorFactory, m_stringFactory);
		
		result.m_callStack.clear();
		for (int i = 0; i < m_callStack.size(); i++) {
			ScopedAbstractState cse = m_callStack.get(i);
			
			Map<String, IAbstractValue<?>> thisLayer = cse.getValues();
			ScopedAbstractState resultCSE = new ScopedAbstractState(cse.getCallStatement(), cse.getOldValues());
			resultCSE.SetIsGlobalScope(cse.isGlobalScope());
			result.m_callStack.add(resultCSE);
			Map<String, IAbstractValue<?>> copyLayer = result.m_callStack.get(i).getValues();
			for (String identifier : thisLayer.keySet()) {
				IAbstractValue<?> originalValue = thisLayer.get(identifier);
				if (originalValue == null) {
					m_logger.error(String.format("Invalid null value for identifier \"%s\" found.", identifier));
				} else {
					copyLayer.put(identifier, originalValue.copy());
				}
			}

			Map<String, ArrayData> thisArray = cse.getArrays();
			Map<String, ArrayData> copyArray = result.m_callStack.get(i).getArrays();
			for (String identifier : thisArray.keySet()) {
				ArrayData originalArrayData = thisArray.get(identifier);
				ArrayData resultArrayData = new ArrayData(identifier);
				resultArrayData.setValue(originalArrayData.getValue());
				if (originalArrayData.getIndicesUnclear())
					resultArrayData.setIndicesUnclear();
				copyArray.put(identifier, resultArrayData);
			}
			
			resultCSE.getLoopStack().clear();
			resultCSE.getLoopStack().addAll(cse.getLoopStack());
		}
		
		
		result.m_trace.addAll(m_trace);
		
		return result;
	}
	
	/**
	 * Merge this state with the given state using the merge operator set in the preferences.
	 * Merges the global and current (matching) scope only, all other scope layers are copied
	 * from the state with a longer trace
	 * @param state The state to merge with
	 * @return A new state with merged global and current layer:
	 * (this state's global layer) mergeOp (the given state's global layer)
	 * (this state's current layer) mergeOp (the given state's current layer)
	 * <br> All other layers remain as found in the state with longer trace
	 * <br> Returns null if the states can't be merged, i.e. belong to different calls
	 */
	public AbstractState merge(AbstractState state) {
		if (state == null)
			return copy();

		List<ScopedAbstractState> thisCallStack = getCallStack();
		List<ScopedAbstractState> otherCallStack = state.getCallStack();
		int thisCallStackSize = thisCallStack.size();
		int otherCallStackSize = otherCallStack.size();
		if (thisCallStackSize < otherCallStackSize)
			return null;
		for (int i = 1; i < thisCallStackSize; i++) {
			ScopedAbstractState thisCSE =  i >= thisCallStackSize
					? thisCallStack.get(0)
					: thisCallStack.get(thisCallStackSize - i);
			ScopedAbstractState otherCSE =  i >= otherCallStackSize
					? otherCallStack.get(0)
					: otherCallStack.get(otherCallStackSize - i);
			if (thisCSE.getCallStatement() != otherCSE.getCallStatement())
				return null;
		}
		
		boolean thisIsLonger = getTrace().size() > state.getTrace().size();

		AbstractState shorter = thisIsLonger ? state : this;
		AbstractState longer = thisIsLonger ? this : state;
		AbstractState result = longer.copy();
		
		mergeLayers(shorter.getGlobalScope(), longer.getGlobalScope(), result.getGlobalScope());
		
		if (longer.getStackSize() > 1) {
			// if data for a non-global scope exists
			mergeLayers(shorter.getCurrentScope(), longer.getCurrentScope(), result.getCurrentScope());
		}
		
		return result;
	}
	
	/**
	 * Merges values from left and right, storing the resulting values in result:
	 * result-value = left-value merge right-value
	 * left and right need to belong to the same method call (or be both global)
	 * @param left
	 * @param right
	 * @param result Existing data (values, arrays, loop stack) will be cleared & replaced
	 */
	private void mergeLayers(ScopedAbstractState left, ScopedAbstractState right, ScopedAbstractState result) {
		if ((left == null) || (right == null) || (result == null))
			return;
		
		// clear possibly existing data
		result.getArrays().clear();
		result.getValues().clear();
		
		Map<String, IAbstractValue<?>> leftValues = left.getValues();
		Map<String, IAbstractValue<?>> rightValues = right.getValues();
		Map<String, IAbstractValue<?>> resultValues = result.getValues();

		Set<String> identifiers = new HashSet<String>();
		identifiers.addAll(leftValues.keySet());
		identifiers.addAll(rightValues.keySet());

		// widen values: thisValue wideningOp otherValue
		for (String identifier : identifiers) {
			IAbstractValue<?> leftValue = leftValues.get(identifier);
			IAbstractValue<?> rightValue = rightValues.get(identifier); 

			IAbstractValue<?> resultValue = null;
			if (leftValue == null) {
				resultValue = rightValue.copy();
			} else if (rightValue == null) {
				resultValue = leftValue.copy();
			} else {
				resultValue = mergeValues(leftValue, rightValue);
				m_logger.debug(String.format("%s: %s merge %s => %s", identifier, leftValue, rightValue, resultValue));
			}
			if (resultValue != null)
				resultValues.put(identifier, resultValue);
		}

		// merge array data
		Map<String, ArrayData> leftArrays = left.getArrays();
		Map<String, ArrayData> rightArrays = right.getArrays();
		Map<String, ArrayData> resultArrays = result.getArrays();

		identifiers.clear();
		identifiers.addAll(leftArrays.keySet());
		identifiers.addAll(rightArrays.keySet());

		for (String identifier : identifiers) {
			ArrayData leftData = leftArrays.get(identifier);
			ArrayData rightData = rightArrays.get(identifier);
			
			boolean indicesUnclear;
			IAbstractValue<?> mergedValue;
			
			if (leftData == null) {
				indicesUnclear = rightData.getIndicesUnclear();
				mergedValue = rightData.getValue();
			} else if (rightData == null) {
				indicesUnclear = leftData.getIndicesUnclear();
				mergedValue = leftData.getValue();
			} else {
				indicesUnclear = leftData.getIndicesUnclear() || rightData.getIndicesUnclear();
				IAbstractValue<?> thisValue = leftData.getValue();
				IAbstractValue<?> otherValue = rightData.getValue();
				mergedValue = mergeValues(thisValue, otherValue);
			}
			
			ArrayData resultData = new ArrayData(identifier);
			resultData.setValue(mergedValue);
			if (indicesUnclear)
				resultData.setIndicesUnclear();
			resultArrays.put(identifier, resultData);
		}
	}
	
	private IAbstractValue<?> mergeValues(IAbstractValue<?> A, IAbstractValue<?> B) {
		IMergeOperator<?> mergeOp = null;
		
		if (m_boolFactory.valueBelongsToDomainSystem(A)) {
			mergeOp = m_boolFactory.getMergeOperator();
		} else if (m_bitVectorFactory.valueBelongsToDomainSystem(A)) {
			mergeOp = m_bitVectorFactory.getMergeOperator();
		} else if (m_stringFactory.valueBelongsToDomainSystem(A)) {
			mergeOp = m_stringFactory.getMergeOperator();
		} else if (m_intFactory.valueBelongsToDomainSystem(A)) {
			mergeOp = m_intFactory.getMergeOperator();
		} else if (m_realFactory.valueBelongsToDomainSystem(A)) {
			mergeOp = m_realFactory.getMergeOperator();
		}
		if (mergeOp != null)
			return mergeOp.apply(A, B);

		m_logger.warn(String.format("Can't create merge operator for value %s", A));
		return null;
	}
	
	/**
	 * Widen this state with the given state using the widening operator set in the preferences.
	 * Widens the global and current (matching) scope only, all other scope layers are copied
	 * from the given state
	 * @param state The state to widen with
	 * @return A new state with widened global and current layer:
	 * (this state's global layer) wideningOp (the given state's global layer)
	 * (this state's current layer) wideningOp (the given state's current layer)
	 * <br> All other layers remain as found in the given state
	 */
	public AbstractState widen(AbstractState state) {
		if (state == null)
			return copy();

		AbstractState result = state.copy();
		
		widenLayers(getGlobalScope(), state.getGlobalScope(), result.getGlobalScope());
		
		if (state.getStackSize() > 1) {
			// if data for a non-global scope exists
			widenLayers(getCurrentScope(), state.getCurrentScope(), result.getCurrentScope());
		}
		
		return result;
	}
	
	/**
	 * Widens values from left and right, storing the resulting values in result:
	 * result-value = left-value widen right-value
	 * left and right need to belong to the same method call (or be both global)
	 * @param left
	 * @param right
	 * @param result Existing data (values, arrays, loop stack) will be cleared & replaced
	 */
	private void widenLayers(ScopedAbstractState left, ScopedAbstractState right, ScopedAbstractState result) {
		if ((left == null) || (right == null) || (result == null))
			return;
		
		// clear possibly existing data
		result.getArrays().clear();
		result.getValues().clear();
		
		Map<String, IAbstractValue<?>> leftValues = left.getValues();
		Map<String, IAbstractValue<?>> rightValues = right.getValues();
		Map<String, IAbstractValue<?>> resultValues = result.getValues();

		Set<String> identifiers = new HashSet<String>();
		identifiers.addAll(leftValues.keySet());
		identifiers.addAll(rightValues.keySet());

		// widen values: thisValue wideningOp otherValue
		for (String identifier : identifiers) {
			IAbstractValue<?> leftValue = leftValues.get(identifier);
			IAbstractValue<?> rightValue = rightValues.get(identifier); 

			IAbstractValue<?> resultValue = null;
			if (leftValue == null) {
				resultValue = rightValue.copy();
				m_logger.warn(String.format("Widening encountered a missing value for %s in the old state.", identifier));
			} else if (rightValue == null) {
				m_logger.error(String.format("Widening failed with a missing value for %s in the new state.", identifier));
			} else {
				resultValue = widenValues(leftValue, rightValue);
			}
			if (resultValue != null)
				resultValues.put(identifier, resultValue);
		}

		// merge array data
		Map<String, ArrayData> leftArrays = left.getArrays();
		Map<String, ArrayData> rightArrays = right.getArrays();
		Map<String, ArrayData> resultArrays = result.getArrays();

		identifiers.clear();
		identifiers.addAll(leftArrays.keySet());
		identifiers.addAll(rightArrays.keySet());

		for (String identifier : identifiers) {
			ArrayData leftData = leftArrays.get(identifier);
			ArrayData rightData = rightArrays.get(identifier);
			
			if (leftData == null) {
				ArrayData resultData = new ArrayData(identifier);
				resultData.setValue(rightData.getValue());
				if (rightData.getIndicesUnclear())
					resultData.setIndicesUnclear();
				resultArrays.put(identifier, resultData);
				m_logger.warn(String.format("Widening encountered a missing value for %s in the old state.", identifier));
			} else if (rightData == null) {
				m_logger.error(String.format("Widening failed with a missing value for array %s in the new state.", identifier));
			} else {
				boolean indicesUnclear = leftData.getIndicesUnclear() || rightData.getIndicesUnclear();
				IAbstractValue<?> widenedValue = widenValues(leftData.getValue(), rightData.getValue());
				ArrayData resultData = new ArrayData(identifier);
				resultData.setValue(widenedValue);
				if (indicesUnclear)
					resultData.setIndicesUnclear();
				resultArrays.put(identifier, resultData);
			}
		}
	}
	
	private IAbstractValue<?> widenValues(IAbstractValue<?> A, IAbstractValue<?> B) {
		IWideningOperator<?> wideningOp = null;
		
		if (m_boolFactory.valueBelongsToDomainSystem(A)) {
			wideningOp = m_boolFactory.getWideningOperator();
		} else if (m_bitVectorFactory.valueBelongsToDomainSystem(A)) {
			wideningOp = m_bitVectorFactory.getWideningOperator();
		} else if (m_stringFactory.valueBelongsToDomainSystem(A)) {
			wideningOp = m_stringFactory.getWideningOperator();
		} else if (m_intFactory.valueBelongsToDomainSystem(A)) {
			wideningOp = m_intFactory.getWideningOperator();
		} else if (m_realFactory.valueBelongsToDomainSystem(A)) {
			wideningOp = m_realFactory.getWideningOperator();
		}
		if (wideningOp != null)
			return wideningOp.apply(A, B);

		m_logger.warn(String.format("Can't create widening operator for value %s", A));
		return null;
	}
	
	/**
	 * @param identifier
	 * @return The current scope if it has the given identifier,
	 * 		else the global scope if that one does,
	 * 		else null if none of them has it. 
	 */
	private ScopedAbstractState getScopeOfIdentifier(String identifier) {
		ScopedAbstractState cse = getCurrentScope();
		if (cse.getValues().containsKey(identifier))
			return cse;
		
		if (!cse.isGlobalScope()) {
			cse = getGlobalScope();
			if (cse.getValues().containsKey(identifier))
				return cse;
		}
		
		return null;
	}

	/**
	 * @return The number of stack levels
	 */
	public int getStackSize() {
		return m_callStack.size();
	}
	
	/**
	 * @return The current scope level
	 */
	public ScopedAbstractState getCurrentScope() {
		return m_callStack.peek();
	}
	
	/**
	 * @return The name of the current scope's function
	 */
	public String getCurrentScopeName() {
		CallStatement cs = getCurrentScope().getCallStatement();
		return (cs == null) ? "GLOBAL" : cs.getMethodName();
	}
	
	/**
	 * @return The global scope level
	 */
	public ScopedAbstractState getGlobalScope() {
		return m_callStack.getLast();
	}
	
	/**
	 * Creates a new empty symbol table and puts it on the top of the stack
	 * @param CallStatement The call statement of the method call that creates this scope level
	 */
	public void pushStackLayer(CallStatement callStatement) {
		if (m_callStack.size() > 2) {
			/*
			 * For recursive calls: Determine a pair of matching call statements in the call
			 * stack, where one is the current top element and the other is the next element
			 * with the same call statement:
			 * global - ... - call A2 - ... - call A1
			 * 				(second)		(first)
			 * 
			 * If now for every element between first and second, the same sequence follows 
			 * under second, we merge all these:
			 * global - ... - call D2 - call C2 - call B2 - call A2 - call D1 - call C1 - call B1 - call A1
			 * 												(second)								(first)
			 * merged:
			 * global - ... - call D* - call C* - call B* - call A*
			 * where call X* = call X1 merge call X2
			 * 
			 * the new scope is added on top of this shortened scope.
			 */
			
			LinkedList<ScopedAbstractState> headSequence = new LinkedList<ScopedAbstractState>();
			int max = m_callStack.size();
			ScopedAbstractState first = m_callStack.get(0);
			ScopedAbstractState second = null;
			for (int i = 1; i < max; i++) {
				ScopedAbstractState current = m_callStack.get(i);
				if (current.getCallStatement() == first.getCallStatement()) {
					second = current;
					break;
				} else {
					headSequence.add(current);
				}
			}
			// if a matching recursive call exists, check if its predecessors match the headSequence
			if (second != null) {
				int headSize = headSequence.size();
				LinkedList<ScopedAbstractState> tailSequence = new LinkedList<ScopedAbstractState>();
				boolean isMatch = true;
				for (int i = 0; i < headSize; i++) {
					int tailId = headSize + i + 2;
					if (tailId >= max) {
						isMatch = false;
						break;
					}
					ScopedAbstractState head = headSequence.get(i);
					ScopedAbstractState tail = m_callStack.get(tailId);
					if (head.getCallStatement() != tail.getCallStatement()) {
						isMatch = false;
						break;
					}
					tailSequence.add(tail);
				}
				if (isMatch) {
					//merge all corresponding states, cutting off the head
					for (int i = 0; i <= headSize; i++) {
						m_callStack.pop(); m_callStack.pop();
					}
					headSequence.push(first);
					tailSequence.push(second);
					for (int i = headSize; i >= 0; i--) {
						ScopedAbstractState head = headSequence.get(i);
						ScopedAbstractState tail = tailSequence.get(i);
						ScopedAbstractState merged = new ScopedAbstractState(head.getCallStatement(), head.getOldValues());
						mergeLayers(head, tail, merged);
						m_callStack.push(merged);
					}
				}
			}
		}
		
		Map<String, IAbstractValue<?>> oldValues = m_callStack.isEmpty() ? null : getGlobalScope().getValues();
		m_callStack.push(new ScopedAbstractState(callStatement, oldValues));
	}
	
	/**
	 * Removes the topmost symbol table from the stack unless it is the only layer
	 * @return True if there was a table to pop, false if the stack only has a single layer
	 */
	public boolean popStackLayer() {
		int size = m_callStack.size();
		
		if (size <= 1)
			return false;
		
		m_callStack.pop();
		return true;
	}
	
	/**
	 * @return Number of occurrences of the current method with the same call statement in the call stack
	 */
	public int getRecursionCount() {
		int result = 0;
		
		CallStatement currentCall = getCurrentScope().getCallStatement();
		
		for (ScopedAbstractState cse : m_callStack) {
			if (cse.getCallStatement() == currentCall)
				result++;
		}
		
		return result;
	}
	
	/**
	 * Assigns the given value to the topmost occurrence of the identifier in the stack.
	 * @param identifier An existing identifier
	 * @param value The new value
	 * @return True iff a layer with the given identifier exists so the value could be written
	 */
	public boolean writeValue(String identifier, IAbstractValue<?> value) {
		ScopedAbstractState layer = getScopeOfIdentifier(identifier);
		
		if (layer == null)
			return false;
		
		layer.getValues().put(identifier, value);
		
		value.setIdentifier(identifier, layer.isGlobalScope());
		
		return true;
	}
	
	/**
	 * @param identifier The identifier whose value is to be retrieved
	 * @param old Set to true if instead of "x" you want "old(x)" - for global variables only, else you just get "x"
	 * @return The value associated with the identifier on its scope level, or null if it is not found
	 */
	public IAbstractValue<?> readValue(String identifier, boolean old) {
		ScopedAbstractState scope = old ? getCurrentScope() : getScopeOfIdentifier(identifier);
		
		if (scope == null)
			return null;
		
		if (old) {
			IAbstractValue<?> result = scope.getOldValues().get(identifier);
			if (result != null)
				return result;
		}
		
		return scope.getValues().get(identifier);
	}
	
	/**
	 * Generates a new mapping for the given identifier on the topmost stack level if it does not exist there already.
	 * @param identifier The new identifier to declare
	 * @param initialValue Its initial value
	 * @param asGlobal Set to true if the variable is a global variable
	 * @return True if it could be declared, false if such an identifier already exists on the top layer or the stack is empty
	 */
	public boolean declareIdentifier(String identifier, IAbstractValue<?> initialValue, boolean asGlobal) {
		if (initialValue == null)
			return false;
		
		ScopedAbstractState layer = asGlobal ? getGlobalScope() : getCurrentScope();

		m_logger.debug(String.format("New variable %s at scope level %d %s", identifier, getStackSize()-1,
				getCurrentScopeName()));
		
		if ((layer == null) || (layer.getValues().containsKey(identifier))) {
			m_logger.error("Cannot declare identifier!");
			return false;
		}
		
		layer.getValues().put(identifier, initialValue);
		
		initialValue.setIdentifier(identifier, asGlobal);
		
		return true;
	}
	
	/**
	 * Add a loop entry to the loop entry stack
	 * (Stack of loop entry nodes along with the edge taken to enter the loop; used to make sure
	 *  widening is applied properly in nested loops)
	 * @param loopNode Loop entry node
	 * @param entryEdge The edge over which the loop will be left
	 */
	public void pushLoopEntry(Object loopNode, RCFGEdge exitEdge) {
		getCurrentScope().getLoopStack().push(new LoopStackElement(loopNode, exitEdge));
	}

	/**
	 * Remove the top element of the loop entry stack
	 * @return The removed old top element of the loop entry stack
	 */
	public LoopStackElement popLoopEntry() {
		LinkedList<LoopStackElement> loopStack = getCurrentScope().getLoopStack();
		if (loopStack.size() <= 1) {
			m_logger.warn("Tried to pop the last, global loop stack level.");
			return null;
		} else {
			LoopStackElement lastLoop = loopStack.pop();
			if (lastLoop != null) {
				LoopStackElement currentLoop = loopStack.peek();
				currentLoop.increaseIterationCount(lastLoop.getLoopNode());
			}
			return lastLoop;
		}
	}
	
	/**
	 * @return The top element of the loop entry stack
	 */
	public LoopStackElement peekLoopEntry() {
		return getCurrentScope().getLoopStack().peek();
	}
	
	/**
	 * @return The stack of loop entry nodes along with the edges over which the loop has been entered
	 */
	public LinkedList<LoopStackElement> getLoopEntryNodes() {
		return getCurrentScope().getLoopStack();
	}
	
	/**
	 * Add a block to the list of passed CodeBlocks for trace reconstruction
	 * @param CodeBlock A block to add
	 * @return True if the block was successfully added
	 */
	public boolean addCodeBlockToTrace(CodeBlock block) {
		if (block == null)
			return false;
		return m_trace.add(block);
	}
	
	/**
	 * @return A list of codeblocks passed during creating this state
	 */
	public List<CodeBlock> getTrace() {
		return m_trace;
	}
	
	/**
	 * @param predecessor
	 * @return True iff this state's passed node list contains and begins with all passed nodes of the
	 * given state in the same order, plus at least one more node
	 */
	public boolean isSuccessor(AbstractState predecessor) {
		if (m_trace.size() <= predecessor.m_trace.size())
			return false;
		
		for (int i = 0; i < predecessor.m_trace.size(); i++) {
			if (!m_trace.get(i).equals(predecessor.m_trace.get(i)))
				return false;
		}
		
		return true;
	}
	
	/**
	 * @return The stack as a list, bottom layer at index 0.
	 */
	public List<ScopedAbstractState> getCallStack() {
		return m_callStack;
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
