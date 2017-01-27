/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptInterpreter plug-in.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptInterpreter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptInterpreter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptInterpreter plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Exception that is thrown if the interpreter has found an error in the ats file. The short description may be null
 * which means that no short description is provided.
 * 
 * @author musab@informatik.uni-freiburg.de
 */
class InterpreterException extends Exception {
	private static final long serialVersionUID = -7514869048479460179L;
	private final ILocation mLocation;
	private final String mShortDescription;
	private final String mLongDescription;
	
	public InterpreterException(final ILocation location, final String longDescription) {
		super();
		mLocation = location;
		mLongDescription = longDescription;
		mShortDescription = null;
	}
	
	public InterpreterException(final ILocation location, final String longDescription,
			final String shortDescription) {
		super();
		mLocation = location;
		mLongDescription = longDescription;
		mShortDescription = shortDescription;
	}
	
	public InterpreterException(final ILocation location, final Throwable cause) {
		// pass throwable as cause to superclass
		super(cause);
		mLocation = location;
		mLongDescription = generateLongDescriptionFromThrowable(cause);
		mShortDescription = cause.getClass().getSimpleName();
	}
	
	private static String generateLongDescriptionFromThrowable(final Throwable throwable) {
		if (throwable.getMessage() == null) {
			return throwable.getClass().getSimpleName();
		}
		return throwable.getClass().getSimpleName() + ": " + throwable.getMessage();
	}
	
	public ILocation getLocation() {
		return mLocation;
	}
	
	public String getLongDescription() {
		return mLongDescription;
	}
	
	public String getShortDescription() {
		return mShortDescription;
	}
}
