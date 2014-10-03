package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 * Program Execution defined by a finite trace and (partial) program states at
 * each position of this trace. This interface is used to transport traces from
 * an analyzer tool through the toolchain back to the user.
 * 
 * TODO: how should an interface for infinite traces look?
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 * 
 * @param <TE>
 *            Type of the elements whose sequence are the trace.
 * @param <E>
 *            Type of the expressions that are used to denote program variables
 *            and their values.
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
	public AtomicTraceElement<TE> getTraceElement(int i);

	/**
	 * Returns the partial program state at position i of this program
	 * execution. The partial program state at position i is the partial state
	 * of the program directly <b>after</b> executing the trace element at
	 * position i. Returns null if this object does not have any information
	 * about the program state at position i.
	 */
	public ProgramState<E> getProgramState(int i);

	/**
	 * Returns the partial program state at the beginning of this program
	 * execution. This is the partial program state before the first trace
	 * element was executed.
	 */
	public ProgramState<E> getInitialProgramState();

	public Class<E> getExpressionClass();

	public Class<TE> getTraceElementClass();

	/**
	 * Program state that is can be defined only partially. This class defines
	 * for some variables of the program a Collection of possible values.
	 * Variables and values are expressions of type E. We use a map to assign to
	 * each variable a set of possible values.
	 * 
	 * @author heizmann@informatik.uni-freiburg.de
	 * @author dietsch@informatik.uni-freiburg.de
	 */
	public class ProgramState<E> {
		private final Map<E, Collection<E>> mVariable2Values;

		public ProgramState(Map<E, Collection<E>> variable2Values) {
			super();
			mVariable2Values = variable2Values;
		}

		public Set<E> getVariables() {
			return mVariable2Values.keySet();
		}

		public Collection<E> getValues(E variable) {
			return mVariable2Values.get(variable);
		}

		@Override
		public String toString() {
			ArrayList<Entry<E, Collection<E>>> toSort = new ArrayList<>(
					mVariable2Values.entrySet());
			Collections.sort(toSort, new Comparator<Entry<E, Collection<E>>>() {
				@Override
				public int compare(Entry<E, Collection<E>> arg0,
						Entry<E, Collection<E>> arg1) {
					return arg0.getKey().toString()
							.compareToIgnoreCase(arg1.getKey().toString());
				}
			});
			return toSort.toString();
		}
	}

	/**
	 * An atomic trace element in the sense of a debugger trace of a program. It
	 * consists of an {@link AtomicTraceElement#getTraceElement() trace element}
	 * , which is probably a statement of some program, and the currently
	 * evaluated {@link AtomicTraceElement#getStep() part of this statement}.
	 * 
	 * This class is used to display an error trace for the user.
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 * 
	 * @param <TE>
	 *            The type of the trace element and the step.
	 */
	public class AtomicTraceElement<TE> {
		private final TE mElement;
		private final TE mStep;
		private final StepInfo mStepInfo;

		/**
		 * Creates an instance where the trace element is evaluated atomically
		 * (i.e. {@link #getTraceElement()} == {@link #getStep()}).
		 */
		public AtomicTraceElement(TE element) {
			this(element, element, StepInfo.NONE);
		}

		/**
		 * Creates an instance where the trace element is not necessarily
		 * evaluated atomically (i.e. {@link #getTraceElement()} !=
		 * {@link #getStep()} is allowed)
		 * 
		 * @param element
		 * @param step
		 * @param info
		 *            provides additional information about the step, e.g. if
		 *            its a condition that evaluated to true or false, if it is
		 *            a call or a return, etc.
		 */
		public AtomicTraceElement(TE element, TE step, StepInfo info) {
			mElement = element;
			mStep = step;
			mStepInfo = info;
		}

		/**
		 * @return The statement which is currently executed. Is never null.
		 */
		public TE getTraceElement() {
			return mElement;
		}

		/**
		 * @return An expression or statement which is evaluated atomically as
		 *         part of the evaluation of {@link #getTraceElement()} or a
		 *         statement that is equal to {@link #getTraceElement()} when
		 *         {@link #getTraceElement()} itself is evaluated atomically.
		 * 
		 *         This is always a reference to some subtree of
		 *         {@link #getTraceElement()}.
		 */
		public TE getStep() {
			return mStep;
		}

		public StepInfo getStepInfo() {
			return mStepInfo;
		}

		/**
		 * StepInfo provides additional information for
		 * {@link AtomicTraceElement#getStep()}.
		 * 
		 * This may be replaced by an actual object later, but for now it should
		 * be sufficient.
		 * 
		 * @author dietsch@informatik.uni-freiburg.de
		 * 
		 */
		public enum StepInfo {
			NONE, CONDITION_EVAL_TRUE, CONDITION_EVAL_FALSE, CALL, RETURN,
		}
		
		@Override
		public String toString() {
			return getTraceElement().toString();
		}

	}
}
