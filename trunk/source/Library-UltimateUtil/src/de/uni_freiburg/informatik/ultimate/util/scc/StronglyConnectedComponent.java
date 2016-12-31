/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.scc;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * StronglyConnectedComponent used in {@link SccComputation}.
 * 
 * @author Matthias Heizmann
 *
 * @param <NODE>
 */
public class StronglyConnectedComponent<NODE> {

	protected NODE mRootNode;
	protected final Set<NODE> mNodes = new HashSet<>();

	public int getNumberOfStates() {
		return mNodes.size();
	}

	public NODE getRootNode() {
		return mRootNode;
	}

	/**
	 * @return The {@link StateContainer}s of all states that are contained in this SCC.
	 */
	public Set<NODE> getNodes() {
		return Collections.unmodifiableSet(mNodes);
	}

	public void addNode(final NODE node) {
		if (mRootNode != null) {
			throw new UnsupportedOperationException("If root node is set SCC may not be modified");
		}
		final boolean notAlreadyContained = mNodes.add(node);
		assert notAlreadyContained : "nodes must not be added twice";
	}

	public void setRootNode(final NODE rootNode) {
		if (mRootNode != null) {
			throw new UnsupportedOperationException("If root node is set SCC may not be modified");
		}
		mRootNode = rootNode;
	}

	@Override
	public String toString() {
		return String.valueOf(mNodes);
	}

}
