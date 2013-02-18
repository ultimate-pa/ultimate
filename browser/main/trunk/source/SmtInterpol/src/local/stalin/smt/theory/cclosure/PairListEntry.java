package local.stalin.smt.theory.cclosure;

import local.stalin.smt.dpll.SimpleListable;

/**
 * A light-weight double linked list for pairs.
 * @author hoenicke
 *
 */
public class PairListEntry<E,F> extends SimpleListable<PairListEntry<E,F>>{
	E                  first;
	F	               second;
	
	public PairListEntry(E first, F second) {
		this.first = first;
		this.second = second;
	}
	
	public E getFirst() {
		return first;
	}
	public F getSecond() {
		return second;
	}
}