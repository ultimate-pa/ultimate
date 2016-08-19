package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.DataflowDAG;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

public class ParallelDataflowgraph<T> extends ModifiableLabeledEdgesMultigraph<ParallelDataflowgraph<T>, ScopedBoogieVar>{

	
	public ParallelDataflowgraph(T stmt, List<ProgramPoint> setOfLocations) {
		mNodeLabel = stmt;
		setLocations(new ArrayList<ProgramPoint>());
	}
	
	public T getNodeLabel() {
		return mNodeLabel;
	}
	
	public List<ProgramPoint> getLocations() {
		return locations;
	}

	private void setLocations(List<ProgramPoint> locations) {
		this.locations = locations;
	}

	private List<ProgramPoint> locations;
	private final T mNodeLabel;
	

}
