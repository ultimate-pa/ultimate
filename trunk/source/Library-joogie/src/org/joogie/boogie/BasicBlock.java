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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.joogie.boogie.statements.Statement;

/**
 * this is only a stub an might be replaced by other boogie parser/cfg
 * implementations
 * 
 * @author schaef
 */
public class BasicBlock {

	private final String mBlockName;
	private final HashSet<BasicBlock> mSuccessors;
	private final HashSet<BasicBlock> mPredecessors;
	private final LinkedList<Statement> mStatements;

	private boolean mIsLoopHead;
	private LocationTag mLocationTag;

	public BasicBlock(String prefix, LocationTag tag, String uid) {
		this(prefix + "Block " + uid, tag);
	}

	public BasicBlock(String prefix, String uid) {
		this(prefix, null, uid);
	}

	public BasicBlock(LocationTag tag, String uid) {
		this("", tag, uid);
	}

//	public BasicBlock(String uid) {
//		this("", null, uid);
//	}

	private BasicBlock(String name, LocationTag tag) {
		mLocationTag = tag;
		mBlockName = name;
		mSuccessors = new HashSet<>();
		mPredecessors = new HashSet<>();
		mStatements = new LinkedList<>();
		mIsLoopHead = false;
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
			this.mStatements.addFirst(s);
		} else {
			this.mStatements.addLast(s);
		}
	}

	public void connectToSuccessor(BasicBlock succ) {
		if (!this.mSuccessors.contains(succ))
			this.mSuccessors.add(succ);
		if (!succ.mPredecessors.contains(this))
			succ.mPredecessors.add(this);
	}

	public void disconnectFromSuccessor(BasicBlock succ) {
		this.mSuccessors.remove(succ);
		succ.mPredecessors.remove(this);
	}

	public String getName() {
		return mBlockName;
	}

	public void setLocationTag(LocationTag lt) {
		mLocationTag = lt;
	}

	public LocationTag getLocationTag() {
		return mLocationTag;
	}

	// Note that the cloned block has a different name
	// Note that the edges are not cloned
	@Override
	public BasicBlock clone() {
		return this.clone(null);
	}

	public BasicBlock clone(String prefix) {
		BasicBlock clone = new BasicBlock(mBlockName, mLocationTag);
		clone.mIsLoopHead = this.mIsLoopHead;
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
		for (BasicBlock b : this.mSuccessors) {
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
		if (mLocationTag != null) {
			sb.append(mLocationTag.toString());
		}
		sb.append(mBlockName + ":\n");
		for (Statement s : getStatements()) {
			sb.append(s.toBoogie() + ";\n");
		}
		if (mSuccessors.size() > 0) {
			sb.append("\t goto ");
			boolean firstgoto = true;
			for (BasicBlock b : mSuccessors) {
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
		return mStatements;
	}

	public void setStatements(LinkedList<Statement> statements) {
		// TODO: flush all information about SSA (once this is implemented)
		this.mStatements.clear();
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
		// TODO: May lead to stackoverflows
		Set<BasicBlock> result = new HashSet<BasicBlock>();
		if (mSuccessors.isEmpty()) {
			result.add(this);
		} else {
			visitedBlocks.add(this);
			for (BasicBlock b : this.mSuccessors)
				if (!visitedBlocks.contains(b))
					result.addAll(b.getFinalSuccessors(visitedBlocks));
		}
		return result;
	}

	public Collection<BasicBlock> getSuccessors() {
		return mSuccessors;
	}

	public Collection<BasicBlock> getPredecessors() {
		return mPredecessors;
	}

}
