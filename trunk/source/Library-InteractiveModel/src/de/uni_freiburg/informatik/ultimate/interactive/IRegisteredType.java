package de.uni_freiburg.informatik.ultimate.interactive;

public interface IRegisteredType<T> {
	Class<T> getType();

	T getDefaultInstance();

	String registeredName();
}