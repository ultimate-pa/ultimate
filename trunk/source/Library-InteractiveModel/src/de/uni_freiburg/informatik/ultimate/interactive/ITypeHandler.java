package de.uni_freiburg.informatik.ultimate.interactive;

public interface ITypeHandler<T> {
	void consume(T data);

	T supply();

	<D> T supply(D data);
}