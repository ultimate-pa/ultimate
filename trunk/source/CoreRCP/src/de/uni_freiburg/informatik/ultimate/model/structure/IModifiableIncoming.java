package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.Collection;

/**
 * 
 * @author dietsch
 *
 * @param <T>
 */
public interface IModifiableIncoming<T> {
	// TODO Add comments (DD)
	boolean addIncoming(T incoming);

	// TODO Add comments (DD)
	// TODO Optional operation
	/***
	 * 
	 * @param index
	 * @param incoming
	 * @return
	 * @throws UnsupportedOperationException
	 *             if the <tt>addIncoming</tt> operation is not supported by
	 *             this implementation.
	 */
	boolean addIncoming(int index, T incoming);

	// TODO Add comments (DD)
	boolean addAllIncoming(Collection<? extends T> c);

	// TODO Add comments (DD)
	// TODO Optional operation
	boolean addAllIncoming(int index, Collection<? extends T> c);

	// TODO Add comments (DD)
	void clearIncoming();

	// TODO Add comments (DD)
	T removeIncoming(int index);

	// TODO Add comments (DD)
	boolean removeIncoming(Object o);

	// TODO Add comments (DD)
	boolean removeAllIncoming(Collection<?> c);
}
