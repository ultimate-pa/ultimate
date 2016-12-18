package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg;

import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class ParallelDataflowgraph<T> extends ModifiableLabeledEdgesMultigraph<ParallelDataflowgraph<T>, IProgramVar> {

	private static final long serialVersionUID = 1L;
	private Map<String, Set<IcfgLocation>> mLocations;
	private final T mNodeLabel;

	public ParallelDataflowgraph(final T stmt, final Map<String, Set<IcfgLocation>> locations) {
		mNodeLabel = stmt;
		setLocations(locations);
	}

	public Boolean compare(final T label, final Map<String, Set<IcfgLocation>> l) {
		// for comparing two this data flow nodes with a not yet constructed node
		if (label == mNodeLabel && l.equals(mLocations)) {
			return true;
		}
		return false;
	}

	public Boolean compare(final ParallelDataflowgraph<T> node) {
		// for comparing two data flow nodes
		if (node.getNodeLabel() == mNodeLabel && node.getLocations().equals(mLocations)) {
			return true;
		}
		return false;
	}

	@Override
	public String toString() {
		String s = "Statement: ";
		if (mNodeLabel == null) {
			s = s + "no statement" + " Locations: ";
		} else {
			s = s + mNodeLabel.toString() + " Locations: ";
		}
		for (final Entry<String, Set<IcfgLocation>> entry : mLocations.entrySet()) {
			s += entry.getKey() + entry.getValue().toString();
		}
		return s;
	}

	public T getNodeLabel() {
		return mNodeLabel;
	}

	public Map<String, Set<IcfgLocation>> getLocations() {
		return mLocations;
	}

	public Set<IcfgLocation> getLocations(final String procedure) {
		return mLocations.get(procedure);
	}

	private void setLocations(final Map<String, Set<IcfgLocation>> locations) {
		mLocations = locations;
	}

}
