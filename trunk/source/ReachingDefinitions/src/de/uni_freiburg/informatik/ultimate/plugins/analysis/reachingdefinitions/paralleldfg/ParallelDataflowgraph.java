package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.DataflowDAG;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

public class ParallelDataflowgraph<T> extends ModifiableLabeledEdgesMultigraph<ParallelDataflowgraph<T>, IProgramVar>{

	private Map< String, Set<ProgramPoint>> locations;
	private final T mNodeLabel;
	
	public ParallelDataflowgraph(T stmt, Map< String, Set<ProgramPoint>> locations) {
		mNodeLabel = stmt;
		setLocations(locations);
	}
	
	public String toString(){
		String s = "Statement: " + mNodeLabel.toString() + " Locations: ";
		for (Entry<String, Set<ProgramPoint>> entry : locations.entrySet()){
			s += entry.getKey() + entry.getValue().toString();
		}
		return s;
	}
	
	public T getNodeLabel() {
		return mNodeLabel;
	}
	
	public Map< String, Set<ProgramPoint>> getLocations() {
		return locations;
	}
	
	public Set<ProgramPoint>  getLocations(String procedure){
		return locations.get(procedure);
	}

	private void setLocations(Map< String, Set<ProgramPoint>> locations) {
		this.locations = locations;
	}

}
