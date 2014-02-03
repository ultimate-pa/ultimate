package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * @author Markus Lindenmann, Matthias Heizmann
 * @since 26.04.2012
 */
public class IncorrectSyntaxException extends RuntimeException {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = -1309056833732436476L;
	
	private final ILocation m_Location;

	/**
	 * Constructs an IncorrectSyntaxException with the specified detail
	 * message. Parameters:
	 * 
	 * @param msg
	 *            the detail message
	 */
	public IncorrectSyntaxException(ILocation location, String msg) {
		super(msg);
		m_Location = location;
	}
	
	public ILocation getLocation() {
		return m_Location;
	}
}
