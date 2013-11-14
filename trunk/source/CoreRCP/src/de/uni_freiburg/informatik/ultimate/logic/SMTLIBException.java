/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

/**
 * This is the exception thrown by the script interface when an error occurs.
 * This corresponds to the SMTLIB 2 result 
 * <pre>(error "msg")</pre>
 * For the result <code>unsupported</code>, the standard java exception 
 * UnsupportedOperationException is used.
 * 
 * This class extends RuntimeException since it should never be thrown if
 * the script interface is used correctly.  It therefore corresponds to 
 * other runtime exceptions like IllegalArgumentException. 
 * 
 * @author hoenicke
 */
@SuppressWarnings("serial")
public class SMTLIBException extends RuntimeException {
	public SMTLIBException(String message) {
		super(message);
	}

	public SMTLIBException(Throwable cause) {
		super(cause);
	}

	public SMTLIBException(String message, Throwable cause) {
		super(message, cause);
	}
}
