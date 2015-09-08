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
