/*
 * Copyright (C) 2009-2015 Björn Buchhold
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model.repository
 * File:	DuplicateKeyException.java created on Oct 29, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions;

/**
 * DuplicateKeyException
 *
 * @author Björn Buchhold
 *
 */
public class DuplicateKeyException extends DataAccessException {
	

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8860449896992867725L;
	
	/**
	 * @param msg
	 */
	public DuplicateKeyException(String msg) {
		super(msg);
	}
	
	/**
	 * @param msg
	 * @param cause
	 */
	public DuplicateKeyException(String msg, Throwable cause) {
		super(msg, cause);
	}

	
}
