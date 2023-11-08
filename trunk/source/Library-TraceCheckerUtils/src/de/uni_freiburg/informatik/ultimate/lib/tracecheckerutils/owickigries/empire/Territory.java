package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */

public final class Territory <PLACE, LETTER>{
	
	/**
	 * Set of regions in Territory.
	 */
	private final Set<Region> mTerritory;
	
	public Territory (Set<Region> regions) {
		mTerritory = regions;
	}
	
	/**
	 * @return Set of regions in Territory.
	 */
	public Set<Region> getRegions(){
		return mTerritory;
	}
	
	/**
	 * Adds the specified set of regions into the territory.	
	 * @param Set of regions
	 */
	public void addRegion(Set<Region> regions) {
		mTerritory.addAll(regions);
	}
	
	/**
	 * Adds the specified region of places into territory.
	 * @param region
	 */
	public void addRegion(Region region) {
		mTerritory.add(region);
	}
	
	
	//Corelation at level of places call
	
	

}
