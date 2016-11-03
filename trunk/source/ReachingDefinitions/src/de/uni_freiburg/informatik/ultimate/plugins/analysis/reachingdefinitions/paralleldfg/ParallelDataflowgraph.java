package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg;

import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

public class ParallelDataflowgraph<T> extends ModifiableLabeledEdgesMultigraph<ParallelDataflowgraph<T>, IProgramVar>{

	private Map< String, Set<BoogieIcfgLocation>> locations;
	private final T mNodeLabel;
	
	public ParallelDataflowgraph(T stmt, Map< String, Set<BoogieIcfgLocation>> locations) {
		mNodeLabel = stmt;
		setLocations(locations);
	}
	
	public Boolean compare(T label, Map< String, Set<BoogieIcfgLocation>> l){
		// for comparing two this data flow nodes with a not yet constructed node
		if (label == mNodeLabel && l.equals(locations)){
			return true;
		}
		return false;
	}
	
	public Boolean compare(ParallelDataflowgraph<T> node){
		// for comparing two data flow nodes
		if (node.getNodeLabel() == mNodeLabel && node.getLocations().equals(locations)){
			return true;
		}
		return false;
	}
	
	@Override
	public String toString(){
		String s = "Statement: ";
		if (mNodeLabel == null){
			s =  s+ "no statement"  + " Locations: ";
		}
		else {
			s = s+ mNodeLabel.toString() + " Locations: ";
		}
		for (final Entry<String, Set<BoogieIcfgLocation>> entry : locations.entrySet()){
			s += entry.getKey() + entry.getValue().toString();
		}
		return s;
	}
	
	public T getNodeLabel() {
		return mNodeLabel;
	}
	
	public Map< String, Set<BoogieIcfgLocation>> getLocations() {
		return locations;
	}
	
	public Set<BoogieIcfgLocation>  getLocations(String procedure){
		return locations.get(procedure);
	}

	private void setLocations(Map< String, Set<BoogieIcfgLocation>> locations) {
		this.locations = locations;
	}

}
