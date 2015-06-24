package de.uni_freiburg.informatik.ultimate.util.relation;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <E1>
 *            Any type.
 * @param <E2>
 *            Any type.
 */
public class ModifiablePair<E1, E2> extends Pair<E1, E2> {

	public ModifiablePair(E1 first, E2 second) {
		super(first, second);
	}

	public E1 setFirst(E1 first) {
		final E1 tmp = mFirstElement;
		mFirstElement = first;
		return tmp;
	}

	public E2 setSecond(E2 second) {
		final E2 tmp = mSecondElement;
		mSecondElement = second;
		return tmp;
	}
}
