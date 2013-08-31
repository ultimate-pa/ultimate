package de.uni_freiburg.informatik.ultimate.result;

import java.util.Collection;
import java.util.Map;

/**
 * Program Execution defined by a trace and (partial) program states at each
 * position of this trace.
 * 
 * @author Matthias Heizmann
 *
 * @param <TE> Type of the elements whose sequence are the trace.
 * @param <E> Type of the expressions that are used to denote program variables
 * and their values.
 */
public interface IProgramExecution<TE, E> {

	/**
	 * Returns the length of this program execution. The Length of a program
	 * execution is the length of the sequence of trace elements.
	 */
	public int getLength();
	
	
	/**
	 * Returns the trace element at position i of this program execution.
	 */
	public TE getTraceElement(int i);
	
	
	/**
	 * Returns the partial program state at position i of this program 
	 * execution.
	 * The partial program state at position i is the partial state of the
	 * program directly <b>after</b> executing the trace element at position i.
	 * Returns null if this object does not have any information about the
	 * program state at position i.
	 */
	public PartialProgramState<E> getPartialProgramState(int i);
	
	
	/**
	 * Returns the partial program state at the beginning of this program
	 * execution.
	 * This is the partial program state before the first trace element was
	 * executed.
	 */
	public PartialProgramState<E> getInitialPartialProgramState();
	
	
	
	/**
	 * Program state that is defined only partially. This class defines for
	 * some variables of the program a Collection of possible values.
	 * Variables and values are expressions of type E. 
	 * We use a map to assign to each variable a set of possible values.
	 * 
	 * @author Matthias Heizmann
	 *
	 */
	public class PartialProgramState<E> {
		private final Map<E, Collection<E>> m_Variable2Values;

		public PartialProgramState(Map<E, Collection<E>> variable2Values) {
			super();
			m_Variable2Values = variable2Values;
		}

		public Map<E, Collection<E>> getVariable2Values() {
			return m_Variable2Values;
		} 
	}
}
