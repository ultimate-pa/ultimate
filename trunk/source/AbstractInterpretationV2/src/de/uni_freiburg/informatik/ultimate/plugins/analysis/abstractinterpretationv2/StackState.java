package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2;

import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.ScopedAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

/**
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 *            concrete type of abstract states
 */
public class StackState<T>
{
	private final IAbstractDomain<T> mDomain;

	private final Logger mLogger;

	/**
	 * Stack of maps from variable identifiers to values. Stack levels represent
	 * scope levels, index 0 is the global scope.
	 */
	private final LinkedList<ScopedAbstractState<T>> mCallStack;

	/**
	 * Sequence of nodes passed leading to this state -> "execution trace"
	 */
	private final List<CodeBlock> mTrace = new LinkedList<CodeBlock>();

	/**
	 * If true, the state has been set to be processed.
	 */
	private boolean mIsProcessed;

	
	
	/**
	 * Constructor.
	 * 
	 * @param domain
	 * @param logger
	 */
	public StackState(IAbstractDomain<T> domain, Logger logger)
	{
		mDomain = domain;
		mLogger = logger;
		mCallStack = new LinkedList<ScopedAbstractState<T>>();
	}

	
	
	/**
	 * @return True if the state is set as having been processed already
	 */
	public boolean isProcessed() 
	{
		return mIsProcessed;
	}
	
	/**
	 * @param processed Set that the state has been processed already
	 */
	public void setProcessed(boolean processed) 
	{
		mIsProcessed = processed;
	}

	/**
	 * @return The stack as a list, bottom layer at index 0.
	 */
	public List<ScopedAbstractState<T>> getCallStack()
	{
		return mCallStack;
	}

	/**
	 * @return The number of stack levels
	 */
	public int getStackSize()
	{
		return mCallStack.size();
	}
	
	/**
	 * @return The current scope level
	 */
	public ScopedAbstractState<T> getCurrentScope()
	{
		return mCallStack.peek();
	}

	/**
	 * @return The current scope level
	 */
	public ScopedAbstractState<T> getScope(int i)
	{
		return mCallStack.get(i);
	}
		
	/**
	 * 
	 * @param state
	 */
	public void setCurrentScope(ScopedAbstractState<T> state)
	{
		mCallStack.pop();
		mCallStack.push(state);
	}


	/**
	 * @return The current scope level
	 */
	public void getScope(int i, ScopedAbstractState<T> state)
	{
		mCallStack.set(i, state);
	}

	public IAbstractState<T> getCurrentState()
	{
		return getCurrentScope().getState();
	}
	
	/**
	 * @return Number of occurrences of the current method with the same call statement in the call stack
	 */
	public int getRecursionCount() 
	{
		int result = 0;
		
		CallStatement currentCall = getCurrentScope().getCallStatement();
		
		for (ScopedAbstractState<T> cse : mCallStack) 
		{
			if (cse.getCallStatement() == currentCall)
			{
				result++;
			}
		}
		
		return result;
	}
	
	/**
	 * Add a loop entry to the loop entry stack
	 * (Stack of loop entry nodes along with the edge taken to enter the loop; used to make sure
	 *  widening is applied properly in nested loops)
	 * @param loopNode Loop entry node
	 * @param entryEdge The edge over which the loop will be left
	 */
	public void pushLoopEntry(ProgramPoint loopNode, RCFGEdge exitEdge)
	{
		getCurrentScope().getLoopStack().push(new LoopStackElement(loopNode, exitEdge));		
	}
	
	/**
	 * Remove the top element of the loop entry stack
	 * 
	 * @return The removed old top element of the loop entry stack
	 */
	public LoopStackElement popLoopEntry()
	{
		LinkedList<LoopStackElement> loopStack = getCurrentScope().getLoopStack();
		if (loopStack.size() <= 1)
		{
			mLogger.warn("Tried to pop the last, global loop stack level.");
			return null;
		}
		else
		{
			LoopStackElement lastLoop = loopStack.pop();
			if (lastLoop != null)
			{
				LoopStackElement currentLoop = loopStack.peek();
				currentLoop.increaseIterationCount(lastLoop.getLoopNode());
			}
			return lastLoop;
		}
	}

	/**
	 * @return The top element of the loop entry stack
	 */
	public LoopStackElement peekLoopEntry()
	{
		return (LoopStackElement) getCurrentScope().getLoopStack().peek();
	}
	
	public List<LoopStackElement> getLoopEntryNodes()
	{
		return getCurrentScope().getLoopStack();
	}
		
	
	
	/**
	 * Creates a new empty symbol table and puts it on the top of the stack
	 * 
	 * @param CallStatement
	 *            The call statement of the method call that creates this scope
	 *            level
	 */
	public void pushStackLayer(CallStatement callStatement)
	{
		if (mCallStack.size() > 1)
		{
			/*
			 * For recursive calls: Determine a pair of matching call statements
			 * in the call stack, where one is the current top element and the
			 * other is the next element with the same call statement: global -
			 * ... - call A2 - ... - call A1 (second) (first)
			 * 
			 * If now for every element between first and second, the same
			 * sequence follows under second, we merge all these: global - ... -
			 * call D2 - call C2 - call B2 - call A2 - call D1 - call C1 - call
			 * B1 - call A1 (second) (first) merged: global - ... - call D* -
			 * call C* - call B* - call A* where call X* = call X1 merge call X2
			 * 
			 * the new scope is added on top of this shortened scope.
			 */

			LinkedList<ScopedAbstractState<T>> headSequence = new LinkedList<ScopedAbstractState<T>>();
			int size = mCallStack.size();
			ScopedAbstractState<T> first = mCallStack.get(0);
			ScopedAbstractState<T> second = null;
			for (int i = 1; i < size; i++)
			{
				ScopedAbstractState<T> current = mCallStack.get(i);
				if (current.getCallStatement() == first.getCallStatement())
				{
					second = current;
					break;
				}
				else
				{
					headSequence.add(current);
				}
			}

			// if a matching recursive call exists, check if its predecessors
			// match the headSequence
			if (second != null)
			{
				int headSize = headSequence.size();
				LinkedList<ScopedAbstractState<T>> tailSequence = new LinkedList<ScopedAbstractState<T>>();
				boolean isMatch = true;
				for (int i = 0; i < headSize; i++)
				{
					int tailId = headSize + i + 2;
					if (tailId >= size)
					{
						isMatch = false;
						break;
					}
					ScopedAbstractState<T> head = headSequence.get(i);
					ScopedAbstractState<T> tail = mCallStack.get(tailId);
					if (head.getCallStatement() != tail.getCallStatement())
					{
						isMatch = false;
						break;
					}
					tailSequence.add(tail);
				}
				if (isMatch)
				{
					// merge all corresponding states, cutting off the head
					for (int i = 0; i <= headSize; i++)
					{
						mCallStack.pop();
						mCallStack.pop();
					}
					headSequence.push(first);
					tailSequence.push(second);
					for (int i = headSize; i >= 0; i--)
					{
						ScopedAbstractState<T> head = headSequence.get(i);
						ScopedAbstractState<T> tail = tailSequence.get(i);
						ScopedAbstractState<T> merged = applyOnScopedState(mDomain.getMergeOperator(), head, tail);						
						mCallStack.push(merged);
					}
				}
			}
		}

		// Map<Pair, IAbstractValue<?>> oldValues = m_callStack.isEmpty() ? null
		// : getGlobalScope().getValues();
		mCallStack.push(new ScopedAbstractState<T>(callStatement, mDomain.createState()));
	}
	
	/**
	 * Compares this stack state with another stack state.
	 * Compares all layers as much as the smaller state possesses.
	 * @param state
	 * @param allLayers
	 * @return
	 */
	public boolean isSuper(StackState<T> state)
	{
		if (state == null)
		{
			return false;
		}				

		List<ScopedAbstractState<T>> thisCallStack = getCallStack();
		List<ScopedAbstractState<T>> otherCallStack = state.getCallStack();
		
		int thisCallStackSize = thisCallStack.size();
		int otherCallStackSize = otherCallStack.size();
		
		
		if (thisCallStackSize < otherCallStackSize)
		{
			return false;
		}
		
		for (int i = 0; i < otherCallStackSize; i++) 
		{
			ScopedAbstractState<T> thisCSE =  thisCallStack.get(thisCallStackSize - i);
			ScopedAbstractState<T> otherCSE = otherCallStack.get(otherCallStackSize - i);
			
			if (!thisCSE.isSuper(otherCSE))
			{
				return false;
			}
		}
		
		mLogger.debug(String.format("is super? %s ~ %s", thisCallStack, otherCallStack));
		
		// all checks passed, this state is greater or equal to the argument state
		return true;
	}

	/**
	 * Check if the given state is the predecessor
	 * of this.
	 * @param s
	 * @return
	 */
	public boolean isSuccessor(StackState<T> s)
	{
		if (mTrace.size() <= s.mTrace.size())
		{
			return false;
		}
		
		for (int i = 0; i < s.mTrace.size(); i++)
		{
			if (!mTrace.get(i).equals(s.mTrace.get(i)))
			{
				return false;
			}
		}
		
		return true;
	}	
	

	/**
	 * 
	 * @return
	 */
	public List<CodeBlock> getTrace()
	{
		return mTrace;
	}	

	/**
	 * Returns a copy of this with the top most state replaced
	 * with the given state.
	 * 
	 * @param newTopState
	 * @return
	 */
	public StackState<T> increment(IAbstractState<T> newTopState)
	{
		StackState<T> result = copy();
		
		// create a copy of the scopeedState 
		ScopedAbstractState<T> topState = getCurrentScope().copy();	
		topState.setState(newTopState);
		result.setCurrentScope(topState);
		
		return result;
	}
	
	/**
	 * Applies the given operator on the given abstract states.
	 * 
	 * @param op
	 * @param a
	 * @param b
	 * @return
	 */
	private ScopedAbstractState<T> applyOnScopedState(IAbstractOperator<T> op, ScopedAbstractState<T> a, ScopedAbstractState<T> b)
	{
		assert(a.getCallStatement() == b.getCallStatement());
		
		ScopedAbstractState<T> merged = new ScopedAbstractState<T>(
				a.getCallStatement(), 
				op.apply(a.getState(), b.getState()));
		
		return merged;				
	}
	
	/**
	 * Merge this state with the given state using the merge operator set in the
	 * preferences. Merges the current (matching) scope only, all
	 * other scope layers are copied from the state with the longer trace
	 * 
	 * @param state
	 *            The state to merge with
	 * @return A new state with merged global and current layer: (this state's
	 *         global layer) mergeOp (the given state's global layer) (this
	 *         state's current layer) mergeOp (the given state's current layer) <br>
	 *         All other layers remain as found in the state with longer trace <br>
	 *         Returns null if the states can't be merged, i.e. belong to
	 *         different calls
	 */
	public StackState<T> merge(StackState<T> s, boolean allLayers)
	{
		// get the widening operator
		IAbstractMergeOperator<T> op = mDomain.getMergeOperator();
		
		return applyOnLayers(op, s, allLayers);				
	}
	
	/**
	 * Widen this state with the given state using the widening operator set in
	 * the preferences. Widens the current (matching) scope only, all other
	 * scope layers are copied from the given state, if allLayers is set to
	 * false.
	 * 
	 * @param state
	 *            The state to widen with
	 * @return A new state with widened global and current layer: (this state's
	 *         global layer) wideningOp (the given state's global layer) (this
	 *         state's current layer) wideningOp (the given state's current
	 *         layer) <br>
	 *         All other layers remain as found in the given state
	 */
	public StackState<T> widen(StackState<T> s, boolean allLayers)
	{
		// get the widening operator
		IAbstractWideningOperator<T> op = mDomain.getWideningOperator();
		
		return applyOnLayers(op, s, allLayers);		
	}
	
	/**
	 * Applies the given operator on this state and the stack state
	 * on the topmost or on all layers
	 * @param op
	 * @param s
	 * @param allLayers
	 * @return
	 */
	private StackState<T> applyOnLayers(IAbstractOperator<T> op, StackState<T> s, boolean allLayers)
	{
		if(s == null)
		{
			return copy();
		}
		StackState<T> result = s.copy();
			
		
		if (allLayers)
		{
			for (int i = 0; i < getStackSize() && i < s.getStackSize(); i++)
			{
				result.getScope(i).setState(
						op.apply(
							getScope(i).getState(),
							s.getScope(i).getState()));

			}
		}
		else
		{
			result.getCurrentScope().setState(
					op.apply(
						getCurrentScope().getState(),
						s.getCurrentScope().getState()));

		}

		return result;
	}

	/**
	 * Copies this instance.
	 * Does not copy the domain logger or any state in the
	 * call stack.
	 * @return
	 */
	public StackState<T> copy()
	{
		StackState<T> clone = new StackState<T>(mDomain, mLogger);
		for(ScopedAbstractState<T> state : mCallStack)
		{
			clone.mCallStack.add(state);
		}
		for(CodeBlock block : mTrace)
		{
			clone.mTrace.add(block);
		}
		return clone;
	}
	
	/**
	 * Add a block to the list of passed CodeBlocks for trace reconstruction
	 * @param CodeBlock A block to add
	 * @return True if the block was successfully added
	 */
	public boolean addCodeBlockToTrace(CodeBlock block)
	{		
		if (block == null)
		{
			return false;
		}
		return mTrace.add(block);
	}

}
