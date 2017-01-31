package de.uni_freiburg.informatik.ultimate.servermodel;

public interface IRegisteredType<T> {
	public Class<T> getType();

	public T getDefaultInstance();

	public String registeredName();
}