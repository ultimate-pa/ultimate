package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

/**
 * This Exception is thrown, when a Converter between two types is registered,
 * but the requested direction of conversion is not implemented.
 * 
 * @author Julian Jarecki
 *
 */
public class ConversionNotImplementedException extends ServerException {
	private static final long serialVersionUID = 6163598721264845950L;
	private Class<?> mTypeA;
	private Class<?> mTypeB;

	public ConversionNotImplementedException(Class<?> typeA, Class<?> typeB) {
		mTypeA = typeA;
		mTypeB = typeB;
	}

	public Class<?> getTypeA() {
		return mTypeA;
	}

	public Class<?> getTypeB() {
		return mTypeB;
	}
}
