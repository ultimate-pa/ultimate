/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jeremi Dzienian
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE Cookiefy plug-in.
 *
 * The ULTIMATE Cookiefy plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Cookiefy plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Cookiefy plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Cookiefy plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Cookiefy plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.HashMap;
import java.util.Map;

/**
 * Represents a map, where each procedure name is matched with an id and vice versa. It is used to represent a procedure
 * within a stack as an integer number.
 *
 * @author Jeremi
 * @author Vincent
 *
 */
public class IdentMap {
	private final Map<String, Integer> mIdentToID;
	private final Map<Integer, String> mIdToIdent;

	/**
	 * auto incrementing ID. use getNextID
	 */
	private int lastID = 0;

	private int getNextID() {
		return lastID++;
	}

	public IdentMap() {
		mIdentToID = new HashMap<>();
		mIdToIdent = new HashMap<>();
	}

	/**
	 * if the procedure identifier does not have an id then some is assigned. If not, then this does nothing.
	 * 
	 * @param procedureIdentifier
	 */
	public void put(final String procedureIdentifier) {
		if (!mIdentToID.containsKey(procedureIdentifier)) {
			final int id = getNextID();
			mIdToIdent.put(id, procedureIdentifier);
			mIdentToID.put(procedureIdentifier, id);
		}
	}

	/**
	 * returns the ID of the given procedure. If none was given yet, then some new is created!
	 * 
	 * @param procedureIdentifier
	 * @return
	 */
	public int getID(final String procedureIdentifier) {
		if (!mIdentToID.containsKey(procedureIdentifier)) {
			put(procedureIdentifier);
		}
		return mIdentToID.get(procedureIdentifier);
	}
}
