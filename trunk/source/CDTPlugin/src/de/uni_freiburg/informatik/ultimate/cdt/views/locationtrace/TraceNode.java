/*
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.locationtrace;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * We need this class, because it is necessary that every Object in the
 * Location-Trace is unique.
 * 
 * @author Stefan Wissert
 * 
 */
public class TraceNode {
	
	private final ILocation location;
	
	private final int index;
	
	private final int originalIndex;
	
	private int iteration;
	
	/**
	 * Inits a trace node
	 * 
	 * @param loc Location
	 * @param index index in the internal list
	 * @param oIndex index in the original list
	 * @param iteration the count of iterations
	 */
	public TraceNode(ILocation loc, int index, int oIndex) {
		location = loc;
		this.index = index;
		originalIndex = oIndex;
	}

	/**
	 * @param iteration the iteration to set
	 */
	public void setIteration(int iteration) {
		this.iteration = iteration;
	}

	/**
	 * @return the originalIndex
	 */
	public int getOriginalIndex() {
		return originalIndex;
	}

	/**
	 * Getter for the location
	 * @return the location.
	 */
	public ILocation getLocation() {
		return location;
	}

	/**
	 * @return the number
	 */
	public int getIndex() {
		return index;
	}

	/**
	 * @return the iteration
	 */
	public int getIteration() {
		return iteration;
	}

}
