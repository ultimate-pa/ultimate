package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.Collection;

//TODO Add comments (DD)
public interface IModifiableOutgoing<T> {
	// TODO Add comments (DD)
	boolean addOutgoing(T outgoing);

	// TODO Add comments (DD)
	// TODO Optional operation
	boolean addOutgoing(int index, T outgoing);
	
	// TODO Add comments (DD)
	boolean addAllOutgoing(Collection<? extends T> c);

	// TODO Add comments (DD)
	// TODO Optional operation
	boolean addAllOutgoing(int index, Collection<? extends T> c);

	// TODO Add comments (DD)
	void clearOutgoing();

	// TODO Add comments (DD)
	T removeOutgoing(int index);

	// TODO Add comments (DD)
	boolean removeOutgoing(Object o);

	// TODO Add comments (DD)
	boolean removeAllOutgoing(Collection<?> c);
}
