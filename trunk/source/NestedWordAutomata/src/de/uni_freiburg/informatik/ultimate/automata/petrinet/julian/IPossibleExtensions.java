package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

public interface IPossibleExtensions<S, C> {
	/**
	 * remove and return the minimal element with respect to the specified Order.
	 * Throws an Exception if queue empty.
	 * @return
	 */
	Event<S, C> remove();
	
	/**
	 * Extend set of possible extensions by all possible extensions which are
	 * successors of e. 
	 */
	void update(Event<S, C> e);
	
	int size();
	boolean isEmpy();
}
