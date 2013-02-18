package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.HashMap;
import java.util.Map;

/**
 * Represents a map, where each procedure name is matched with an id and vice versa.
 * It is used to represent a procedure within a stack as an integer number.
 * 
 * @author Jeremi,Vincent
 *
 */
public class IdentMap {
	private Map<String, Integer> IdentToID;
	private Map<Integer, String> IDToIdent;

	/**
	 * auto incrementing ID. use getNextID
	 */
	private int lastID = 0;
	private int getNextID() {
		return lastID++;
	}
	
	public IdentMap() {
		IdentToID = new HashMap<String, Integer>();
		IDToIdent = new HashMap<Integer, String>();
	}
	
	/**
	 * if the procedure identifier does not have an id then some is assigned.
	 * If not, then this does nothing.
	 * @param procedureIdentifier
	 */
	public void put(String procedureIdentifier) {
		if (!IdentToID.containsKey(procedureIdentifier)) {
			int id = getNextID();
			IDToIdent.put(id, procedureIdentifier);
			IdentToID.put(procedureIdentifier, id);
		}
	}

	/**
	 * returns the ID of the given procedure. If none was given yet, then
	 * some new is created!
	 * @param procedureIdentifier
	 * @return
	 */
	public int getID(String procedureIdentifier) {
		if (!IdentToID.containsKey(procedureIdentifier)) {
			put(procedureIdentifier);
		}
		return IdentToID.get(procedureIdentifier);
	}
}
