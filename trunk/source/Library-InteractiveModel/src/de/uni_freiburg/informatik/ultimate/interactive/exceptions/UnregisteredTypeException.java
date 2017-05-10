package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

/**
 * This Exception is thrown, when The user is trying to send data of an
 * unregistered Type.
 * 
 * @author Julian Jarecki
 *
 */
public class UnregisteredTypeException extends ServerException {
	private static final long serialVersionUID = 4316008641785575704L;
	private final Class<?> mType;

	public UnregisteredTypeException(final Class<?> type) {
		super("Unregistered Type " + type);
		mType = type;
	}

	@SuppressWarnings("unchecked")
	public <E> Class<E> getType() {
		return (Class<E>) mType;
	}
}
