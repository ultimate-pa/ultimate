/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.boogie;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.joogie.boogie.statements.Statement;
import org.joogie.soot.GlobalsCache;

/**
 * this is only a stub an might be replaced by other boogie parser/cfg
 * implementations
 * 
 * @author schaef
 */
public class BasicBlock {

	private LocationTag locationTag = null;

	private String blockName;
	public HashSet<BasicBlock> Successors = new HashSet<BasicBlock>();
	public HashSet<BasicBlock> Predecessors = new HashSet<BasicBlock>();

	private LinkedList<Statement> Statements = new LinkedList<Statement>();

	public boolean IsLoopHead = false;

	public BasicBlock(String prefix, LocationTag tag) {
		this.locationTag = tag;
		blockName = prefix + "Block"
				+ GlobalsCache.v().getUniqueNumber().toString();
	}

	public BasicBlock(String prefix) {
		this(prefix, null);		
	}

	public BasicBlock(LocationTag tag) {
		this("", tag);		
	}
	
	public BasicBlock() {
		this("", null);
	}

	public void addStatement(Statement s) {
		this.addStatement(s, false);
	}

	public void addStatement(Statement s, boolean addToFront) {
		/*
		 * TODO in this procedure we have to collect all variables that are used
		 * and also, how often they are written. this is necessary for the
		 * improved SSA which is not yet implemented. Use:
		 * s.getModifiedVariables()
		 */
		if (addToFront) {
			this.Statements.addFirst(s);
		} else {
			this.Statements.addLast(s);
		}
	}

	public void connectToSuccessor(BasicBlock succ) {
		if (!this.Successors.contains(succ))
			this.Successors.add(succ);
		if (!succ.Predecessors.contains(this))
			succ.Predecessors.add(this);		
	}

	public void disconnectFromSuccessor(BasicBlock succ) {
		this.Successors.remove(succ);
		succ.Predecessors.remove(this);
	}

	public String getName() {
		return blockName;
	}

	public void setLocationTag(LocationTag lt) {
		locationTag = lt;
	}

	public LocationTag getLocationTag() {
		return locationTag;
	}

	// Note that the cloned block has a different name
	// Note that the edges are not cloned
	@Override
	public BasicBlock clone() {
		return this.clone(null);
	}

	public BasicBlock clone(String prefix) {
		BasicBlock clone;
		if (prefix != null)
			clone = new BasicBlock(prefix);
		else
			clone = new BasicBlock();
		clone.IsLoopHead = this.IsLoopHead;
		clone.setStatements(new LinkedList<Statement>());
		for (Statement s : this.getStatements()) {
			clone.addStatement(s.clone());
		}
		return clone;
	}

	/**
	 * @return A deep copy of the basic block, with linked successors that are
	 *         clones as well
	 */
	public BasicBlock deepClone() {
		return deepClone(null, new HashMap<BasicBlock, BasicBlock>());
	}

	/**
	 * @param prefix
	 *            A string to prefix all cloned blocks
	 * @return A deep copy of the basic block, with linked successors that are
	 *         clones as well
	 */
	public BasicBlock deepClone(String prefix) {
		return deepClone(prefix, new HashMap<BasicBlock, BasicBlock>());
	}

	/**
	 * Recursive deep clone. Makes sure the links remain consistent.
	 * 
	 * @param map
	 *            A map between old and new(cloned) blocks starting at the root.
	 * @return A deep copy of the basic block, the map of cloned blocks is
	 *         updated.
	 */
	public BasicBlock deepClone(String prefix, Map<BasicBlock, BasicBlock> map) {
		BasicBlock result = this.clone(prefix);
		map.put(this, result);
		for (BasicBlock b : this.Successors) {
			if (map.containsKey(b)) {
				result.connectToSuccessor(map.get(b));
			} else {
				BasicBlock succ = b.deepClone(prefix, map);
				result.connectToSuccessor(succ);
			}
		}
		return result;
	}

	@Override
	public String toString() {
		return this.getName();
	}

	public String toBoogie() {
		StringBuilder sb = new StringBuilder();
		if (locationTag != null) {
			sb.append(locationTag.toString());
		}
		sb.append(blockName + ":\n");
		for (Statement s : getStatements()) {
			sb.append(s.toBoogie() + ";\n");
		}
		if (Successors.size() > 0) {
			sb.append("\t goto ");
			boolean firstgoto = true;
			for (BasicBlock b : Successors) {
				if (firstgoto) {
					firstgoto = false;
				} else {
					sb.append(", ");
				}
				sb.append(b.getName());
			}
			sb.append(";\n");
		} else {
			sb.append("\t return;\n");
		}
		return sb.toString();
	}

	public LinkedList<Statement> getStatements() {
		return Statements;
	}

	public void setStatements(LinkedList<Statement> statements) {
		// TODO: flush all information about SSA (once this is implemented)
		this.Statements.clear();
		for (Statement s : statements) {
			this.addStatement(s);
		}
	}

	/**
	 * Retrieve a list of final blocks (without any successors) that are in the
	 * transitive closure of the successor relation
	 * 
	 * @return The list of final blocks
	 */
	public Set<BasicBlock> getFinalSuccessors() {
		Set<BasicBlock> visitedBlocks = new HashSet<BasicBlock>();
		return getFinalSuccessors(visitedBlocks);
	}

	private Set<BasicBlock> getFinalSuccessors(Set<BasicBlock> visitedBlocks) {
		Set<BasicBlock> result = new HashSet<BasicBlock>();
		if (this.Successors.isEmpty()) {
			result.add(this);
		} else {
			visitedBlocks.add(this);
			for (BasicBlock b : this.Successors)
				if (!visitedBlocks.contains(b))
					result.addAll(b.getFinalSuccessors(visitedBlocks));
		}
		return result;
	}

}
