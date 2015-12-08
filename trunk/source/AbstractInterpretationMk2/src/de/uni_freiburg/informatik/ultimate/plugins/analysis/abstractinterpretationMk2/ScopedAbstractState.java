package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;

/**
 * Contains an abstract state and adds scoping information as well as loop
 * information
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 */
public class ScopedAbstractState<T> {
	private final CallStatement m_callStatement;

	private IAbstractState<T> m_state;

	private final LinkedList<LoopStackElement> m_loopStack;

	/**
	 * Copy constructor
	 */
	public ScopedAbstractState(ScopedAbstractState<T> original,
			IAbstractState<T> state) {
		m_callStatement = original.m_callStatement;
		m_state = state;
		m_loopStack = new LinkedList<LoopStackElement>();

		for (LoopStackElement lse : original.m_loopStack) {
			m_loopStack.add(lse.copy());
		}
	}

	/**
	 * Copy constructor
	 */
	public ScopedAbstractState(ScopedAbstractState<T> original) {
		m_callStatement = original.m_callStatement;
		m_state = original.m_state.copy();
		m_loopStack = new LinkedList<LoopStackElement>();

		for (LoopStackElement lse : original.m_loopStack) {
			m_loopStack.add(lse.copy());
		}
	}

	public ScopedAbstractState(CallStatement callStatement,
			IAbstractState<T> state) {
		m_callStatement = callStatement;
		m_state = state;

		m_loopStack = new LinkedList<LoopStackElement>();
		m_loopStack.add(new LoopStackElement(null, null, null)); // base stack
																	// element

		// m_arrays = new HashMap<Pair, ArrayData>();
	}

	public IAbstractState<T> getState() {
		return m_state;
	}

	public void setState(IAbstractState<T> s) {
		m_state = s;
	}

	public CallStatement getCallStatement() {
		return m_callStatement;
	}

	public String getCallMethodName() {
		return m_callStatement.getMethodName();
	}

	public LinkedList<LoopStackElement> getLoopStack() {
		return m_loopStack;
	}

	public String toString() {
		String ls = "";

		// for(LoopStackElement lse : m_loopStack)
		// {
		// ls += "~" + lse.toString();
		// }
		ILocation loc = getCallStatement().getPayload().getLocation();

		String cs = getCallMethodName()
				+ (loc == null ? "" : ":L" + loc.getStartLine());
		return "[" + cs + "]" + (m_state == null ? "null" : m_state.toString())
				+ ls;
	}

	/**
	 * Checks if the left CSE contains all variables of the right CSE and all
	 * variable values are greater or equal to their corresponding values
	 * 
	 * @param left
	 * @param right
	 * @return True iff left isSuper right
	 */
	public boolean isSuperOrEqual(ScopedAbstractState<T> right) {
		// must be of the same method call and have at least as many variables
		// if (getCallStatement() != right.getCallStatement())
		if (!getCallStatement().getMethodName().equals(
				right.getCallStatement().getMethodName())) {
			return false;
		}

		// must be super
		return m_state.isSuperOrEqual(right.getState());
	}

	// /**
	// * Gets a copy of this and its state
	// */
	// public ScopedAbstractState<T> copy()
	// {
	// ScopedAbstractState<T> clone = new
	// ScopedAbstractState<T>(m_callStatement, m_state.copy());
	//
	// for(LoopStackElement lse : m_loopStack)
	// {
	// clone.m_loopStack.add(lse.copy());
	// }
	//
	// return clone;
	// }
	//
	// /**
	// * Gets a copy of this and but inserts a new state
	// */
	// public ScopedAbstractState<T> copy(IAbstractState<T> state)
	// {
	// ScopedAbstractState<T> clone = new
	// ScopedAbstractState<T>(m_callStatement, state);
	//
	// for(LoopStackElement lse : m_loopStack)
	// {
	// clone.m_loopStack.add(lse.copy());
	// }
	//
	// return clone;
	// }
}