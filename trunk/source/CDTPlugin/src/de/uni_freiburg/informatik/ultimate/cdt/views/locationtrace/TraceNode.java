/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.locationtrace;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * We need this class, because it is necessary that every Object in the
 * Location-Trace is unique.
 * 
 * @author Stefan Wissert
 * 
 */
public class TraceNode {
	
	private ILocation location;
	
	private int index;
	
	private int originalIndex;
	
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
		this.location = loc;
		this.index = index;
		this.originalIndex = oIndex;
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
