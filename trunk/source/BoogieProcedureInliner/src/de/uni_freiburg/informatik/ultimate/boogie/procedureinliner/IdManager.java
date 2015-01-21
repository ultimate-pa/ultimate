package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;

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
	private Set<String> mIds = new HashSet<>();
	
	/**
	 * Adds an id to this manager. The id will be registered as it is.
	 * @param id An identifier.
	 * @throws IllegalStateException The id was already registered.
	 */
	public void addId(String id) throws IllegalStateException {
		if(!mIds.add(id)) {
			throw new IllegalStateException("Identifier was already registered: " + id);
		}
	}

	/**
	 * Makes an id unique and adds it to this manager.
	 * @param prefix Prefix to be used (for instance, the id of the surrounding procedure).
	 * @param id An identifier.
	 * @return The unique and registered version of the id.
	 */
	public String makeAndAddUniqueId(String prefix, String id) {
		final String fixedPart = prefix + PREFIX_DELIM + id;
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
