/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.states;

import de.uni_muenster.cs.sev.lethal.languages.RegularTreeLanguage;


/**
 * Simple state implementation used for the internal representation of
 * {@link RegularTreeLanguage}<br>
 * A state has a number which identifies it. This leads to a behaviour
 * which is similar to NamedState<Integer>, but for efficiency reasons
 * the name is stored as integer.
 */
public class NumberedState implements State {

	/**
	 * Number identifying this state.
	 */
	private final int index;


	/**
	 * Constructs a new state identified by the given number.
	 * @param index number to identify the new state
	 */
	public NumberedState(final int index) {
		this.index = index;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return String.valueOf(index);
	}


	/**
	 * Returns the index of this NumberedState, i.e. the identifying number.
	 * @return the number this NumberedState is identified with
	 */
	public int getIndex() {
		return index;
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return index;
	}


	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		NumberedState other = (NumberedState) obj;
		if (this.index != other.index)
			return false;
		return true;
	}
}
