package de.uni_freiburg.informatik.ultimate.result;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

/**
 * Program Execution defined by a finite trace and (partial) program states at 
 * each position of this trace. This interface is used to transport traces from
 * an analyzer tool through the toolchain back to the user.
 * 
 * TODO: how should an interface for infinite traces look?
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
	public ProgramState<E> getProgramState(int i);
	
	
	/**
	 * Returns the partial program state at the beginning of this program
	 * execution.
	 * This is the partial program state before the first trace element was
	 * executed.
	 */
	public ProgramState<E> getInitialProgramState();
	
	
	public Class<E> getExpressionClass();
	
	public Class<TE> getTraceElementClass();
	
	
	/**
	 * Program state that is can be defined only partially. This class defines 
	 * for some variables of the program a Collection of possible values.
	 * Variables and values are expressions of type E. 
	 * We use a map to assign to each variable a set of possible values.
	 * 
	 * @author Matthias Heizmann
	 */
	public class ProgramState<E> {
		private final Map<E, Collection<E>> m_Variable2Values;

		public ProgramState(Map<E, Collection<E>> variable2Values) {
			super();
			m_Variable2Values = variable2Values;
		}

		public Set<E> getVariables() {
			return m_Variable2Values.keySet();
		}
		
		public Collection<E> getValues(E variable) {
			return m_Variable2Values.get(variable);
		}

		@Override
		public String toString() {
			return m_Variable2Values.toString();
		}
	}
}
