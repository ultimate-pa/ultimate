package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;


public class Region<PLACE, LETTER> {

	/**
	 * The set of places in Region.
	 */
	
	private final Set<PLACE> mRegion;
	
	public Region(Set<PLACE> region) {
		mRegion = region;
	}
	
	/**
	 * @return set of all places in region.
	 */
	public Set<PLACE> getPlaces(){
		return mRegion;
	}
	
	/**
	 * * Adds the specified place in to the set of places in the region.
	 * @param place	 
	 */
	public void addPlace(PLACE place) {
		mRegion.add(place);
	}
	
	/**
	 * Add the specified set of places to the region.
	 * @param places
	 */
	public void addPlace(Set<PLACE> places) {
		mRegion.addAll(places);
	}
	
	/**
	 * Removes the specified place from the region.
	 * @param place
	 */
	public void removePlace(PLACE place) {
		if (mRegion.contains(place)){ 
			mRegion.remove(place);
		}
	}
	
	/**
	 * @param petriNet over which place corelation is checked.
	 * @return true if place is NOT corelated to all places in the region.
	 * TODO: place corelation!!!!
	 */
	public boolean checkCorelation(IPetriNet<LETTER, PLACE> petriNet) {
		return true;
	}
}
