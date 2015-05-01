package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

/**
 * Labels for nodes from the call graph.
 * <p>
 * Note, that call-foralls aren't treated other than normal calls.
 * This is not a real problem, but might be inefficient in some (constructed) cases.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum CallGraphNodeLabel {

	/**
	 * The procedure is an entry procedure of the program (for instance {@code main}, or {@code ULTIMATE.start}).
	 */
	ENTRY,
	
	/**
	 * The call graph contains a path from an entry or re-entry procedure to this procedure
	 * and only the last edge of that path isn't marked for inlining.
	 * <p>
	 * A procedure might be an entry procedure and re-entry procedure at the same time. In this case, ENTRY is used.
	 */
	RE_ENTRY,
	
	/**
	 * After inlining, the procedure will be dead code (unreachable from all entry procedures) and can be removed.
	 * <p>
	 * This is the case, if there is <b>no</b> path from an entry procedure to this procedure,
	 * ending with an edge, not marked for inlining.<br>
	 * In other words: The procedure is neither an entry nor an re-entry procedure.
	 */
	DEAD;
	
	public boolean isEntryOrReEntry() {
		return this == ENTRY || this == RE_ENTRY;
	}
	
	public boolean isDead() {
		return this == DEAD;
	}
}