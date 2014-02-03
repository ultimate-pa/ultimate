package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * @author Markus Lindenmann, Matthias Heizmann
 * @since 26.04.2012
 */
public class UnsupportedSyntaxException extends RuntimeException {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = -868222134936145470L;
	private final ILocation m_Location;

	/**
	 * Constructs an UnsupportedSyntaxException with the specified detail
	 * message. Parameters:
	 * 
	 * @param msg
	 *            the detail message
	 */
	public UnsupportedSyntaxException(ILocation location, String msg) {
		super(msg);
		m_Location = location;
	}
	
	public ILocation getLocation() {
		return m_Location;
	}
}
