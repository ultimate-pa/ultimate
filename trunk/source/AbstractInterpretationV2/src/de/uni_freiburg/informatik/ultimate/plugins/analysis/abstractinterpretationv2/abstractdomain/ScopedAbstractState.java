package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain;

import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.LoopStackElement;

/**
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 */
public class ScopedAbstractState<T>
{
	private final CallStatement m_callStatement;

	private IAbstractState<T> m_state;

	private final LinkedList<LoopStackElement> m_loopStack;

	public ScopedAbstractState(CallStatement callStatement, IAbstractState<T> state) 
	{
		m_callStatement = callStatement;
		m_state = state;

		m_loopStack = new LinkedList<LoopStackElement>();
		// m_loopStack.add(new LoopStackElement(null, null)); // global stack
		// element

		// m_arrays = new HashMap<Pair, ArrayData>();
	}

	public IAbstractState<T> getState()
	{
		return m_state;
	}
	
	public void setState(IAbstractState<T> s)
	{
		m_state = s;
	}

	public CallStatement getCallStatement()
	{
		return m_callStatement;
	}

	public LinkedList<LoopStackElement> getLoopStack()
	{
		return m_loopStack;
	}
	
	public String toString()
	{
		return m_state.toString();
	}
	
	
	/**
	 * Checks if the left CSE contains all variables of the right CSE
	 * and all variable values are greater or equal to their corresponding values
	 * @param left
	 * @param right
	 * @return True iff left isSuper right
	 */
	public boolean isSuper(ScopedAbstractState<T> right) 
	{
		// must be of the same method call and have at least as many variables
		if (getCallStatement() != right.getCallStatement())				
		{
			return false;
		}
		
		// must be super
		return m_state.isSuper(right.getState());   

		/*
		 * _TODO_
		 * 
		// check if any variable in the right CSE occurs and is greater in the left CSE
		Set<AbstractState.Pair> rightKeys = right.getValues().keySet();
		for (Pair key : rightKeys) {
			//IAbstractValue<?> rightValue = right.getValues().get(key);
			//IAbstractValue<?> leftValue = left.getValues().get(key);
			IAbstractValue<?> rightValue = (IAbstractValue<?>) right.getValues().get(key);
			IAbstractValue<?> leftValue = (IAbstractValue<?>) left.getValues().get(key);
			
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
		for (Pair key : rightKeys) {
			ArrayData rightData = (ArrayData) right.getArrays().get(key);
			ArrayData leftData = (ArrayData) left.getArrays().get(key); 
			
			// identifier must exist and thus have a value
			if (leftData == null)
				return false;
			
			// value of left CSE must be greater than the value of the right CSE
			if (!leftData.getValue().isSuper(rightData.getValue()))
				return false;
		}
		
		return true;
		*/
	}

	/**
	 * Gets a copy of this ans its state
	 */
	public ScopedAbstractState<T> copy()
	{
		ScopedAbstractState<T> clone = new ScopedAbstractState<T>(m_callStatement, m_state.copy());
		
		for(LoopStackElement lse : m_loopStack)
		{
			clone.m_loopStack.add(lse);
		}
		
		return clone;
	}
}