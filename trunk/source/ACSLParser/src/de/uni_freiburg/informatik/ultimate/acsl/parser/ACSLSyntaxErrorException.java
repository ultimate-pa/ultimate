/*
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ACSLParser plug-in.
 * 
 * The ULTIMATE ACSLParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ACSLParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ACSLParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ACSLParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ACSLParser plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.acsl.parser;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Exception class which is thrown by the ACSLParser.
 * 
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.04.2012
 */
public class ACSLSyntaxErrorException extends Exception {
	private static final long serialVersionUID = 1L;

	/**
	 * ACSLNode that locates the SyntaxError.
	 */
	private final ACSLNode mLocation;

	/**
	 * The message of this Exception (is displayed to the user).
	 */
	private final String mMessage;

	/**
	 * @param location
	 *            dummyLocation of the Syntax-Error.
	 * @param message
	 *            the message text of this exception.
	 */
	public ACSLSyntaxErrorException(final ACSLNode location, final String message) {
		mLocation = location;
		mMessage = message;
	}

	/**
	 * @return the location.
	 */
	public ACSLNode getLocation() {
		return mLocation;
	}

	/**
	 * @return given message text.
	 */
	public String getMessageText() {
		return mMessage;
	}
}
