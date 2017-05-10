package de.uni_freiburg.informatik.ultimate.interactive;

public interface ITypeHandler<T> {
	public void consume(T data);

	public T supply();

	public <D> T supply(D data);
}