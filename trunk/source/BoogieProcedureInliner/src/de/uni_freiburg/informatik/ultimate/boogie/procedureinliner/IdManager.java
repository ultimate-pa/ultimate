/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Used to manage identifiers.
 * This stores already used identifiers and can make identifiers unique by adding pre- and post-fixes.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class IdManager {

	/** Delimiter between prefix and original identifier. */
	private static final String PREFIX_DELIM = "_";
	/** Delimiter between original identifier and post-fix. */
	private static final String POSTFIX_DELIM = "#";

	/** All registered ids (renamed to be unique). */
	private final Set<String> mIds = new HashSet<>();
	
	/**
	 * Adds an id to this manager. The id will be registered as it is.
	 * @param id An identifier.
	 * @return The same identifier.
	 * @throws IllegalStateException When adding the same id twice.
	 */
	public String addId(String id){
		if (!mIds.add(id)) {
			throw new IllegalStateException("Id was already registered: " + id);
		}
		return id;
	}
	/**
	 * Convenience method for {@link #makeAndAddUniqueId(String, String)} without prefix.
	 * This tries to preserve the original identifier.
	 */
	public String makeAndAddUniqueId(String id) {
		return makeAndAddUniqueId(null, id);
	}	
	
	/**
	 * Makes an id unique and adds it to this manager.
	 * @param prefix Prefix to be used (for instance, the id of the surrounding procedure).
	 *               The prefix is followed by a delimiter symbol. Use null for no prefix and prefix delimiter.
	 * @param id An identifier.
	 * @return The unique and registered version of the id.
	 */
	public String makeAndAddUniqueId(String prefix, String id) {
		String fixedPart = "";
		if (prefix != null) {
			fixedPart = prefix + PREFIX_DELIM;
		}
		fixedPart += id;
		int postFixNumber = 1;
		String uniqueId = fixedPart;
		while (mIds.contains(uniqueId)) {
			++postFixNumber;
			uniqueId = fixedPart + POSTFIX_DELIM + postFixNumber;
		}
		mIds.add(uniqueId);
		return uniqueId;
	}

	/**
	 * Returns a Read-only view of all stored identifiers. Changes on this IdManager affect the returned set too.
	 * @return Set of stored identifiers.
	 */
	public Set<String> getIds() {
		return Collections.unmodifiableSet(mIds);
	}
	
}
