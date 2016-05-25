/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DebugGUI plug-in.
 * 
 * The ULTIMATE DebugGUI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DebugGUI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DebugGUI plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DebugGUI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE DebugGUI plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.gui.misc;

import java.util.ArrayList;
import java.util.List;

/**
 * @author dietsch
 *
 */
public class GroupEntry extends TreeViewEntry {

	private final List<TreeViewEntry> mEntries;

	public GroupEntry(String entryName, GroupEntry parent) {
		super(entryName, parent);
		mEntries = new ArrayList<TreeViewEntry>();
	}

	public Object[] getEntries() {
		return mEntries.toArray();
	}

	public boolean removeEntry(TreeViewEntry entry) {
		return mEntries.remove(entry);
	}

	public boolean addEntry(TreeViewEntry entry) {
		return mEntries.add(entry);
	}

	@Override
	public boolean isEmpty() {
		return mEntries.isEmpty();
	}

}
