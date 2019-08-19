/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class SCC implements Iterable<IcfgLocation> {
	private final HashSet<IcfgLocation> mVertices;

	public SCC() {
		mVertices = new HashSet<>();
	}

	public <T extends IcfgLocation> SCC(Collection<T> all) {
		mVertices = new HashSet<IcfgLocation>(all);

	}

	void add(IcfgLocation member) {
		mVertices.add(member);
	}

	@Override
	public Iterator<IcfgLocation> iterator() {
		return mVertices.iterator();
	}

	public boolean isSingleton() {
		return mVertices.size() == 1;
	}

	public boolean isSingletonOrEmpty() {
		return isSingleton() || isEmpty();
	}

	public boolean isEmpty() {
		return mVertices.isEmpty();
	}

	public boolean contains(IcfgLocation node) {
		return mVertices.contains(node);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("(");
		for (final IcfgLocation node : mVertices) {
			sb.append(node).append(" ");
		}
		if (!isEmpty()) {
			sb.deleteCharAt(sb.length() - 1);
		}
		sb.append(")");
		return sb.toString();
	}

}
