package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ICFGExecutionEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class InterpretedIcfg {
	private final HashMap<IcfgLocation, HashSet<ICFGExecutionEdge>> mOutEdges = new HashMap<>();
	private final HashMap<IcfgLocation, HashSet<ICFGExecutionEdge>> mInEdges = new HashMap<>();
	private final HashSet<Variable> mVariables = new HashSet<>();
	private final HashSet<IcfgLocation> mLocations = new HashSet<>();
	private final IIcfg<? extends IcfgLocation> mICFG;

	private final static HashSet<ICFGExecutionEdge> emptySet = new HashSet<>();

	public InterpretedIcfg(final IIcfg<? extends IcfgLocation> icfg) {
		mICFG = icfg;
	}

	public IIcfg<? extends IcfgLocation> getIcfg() {
		return mICFG;
	}

	public HashSet<ICFGExecutionEdge> getOutEdges(final IcfgLocation location) {
		return mOutEdges.getOrDefault(location, emptySet);
	}

	public void addEdge(final ICFGExecutionEdge edge) {
		// register new edge
		final HashSet<ICFGExecutionEdge> outEdgeSet = mOutEdges.getOrDefault(edge.mSource, new HashSet<>());
		outEdgeSet.add(edge);
		mOutEdges.put(edge.mSource, outEdgeSet);
		final HashSet<ICFGExecutionEdge> inEdgeSet = mInEdges.getOrDefault(edge.mTarget, new HashSet<>());
		inEdgeSet.add(edge);
		mInEdges.put(edge.mTarget, inEdgeSet);
		mVariables.addAll(edge.getVariables());
		mLocations.add(edge.mSource);
		mLocations.add(edge.mTarget);

		// add edges that originate at the new edges target location as its children
		edge.addChildren(mOutEdges.getOrDefault(edge.mTarget, new HashSet<>()));

		// add edge as child to all edges that terminate at the new edges source location
		final ArrayList<ICFGExecutionEdge> edgeList = new ArrayList<>();
		edgeList.add(edge);
		for (final ICFGExecutionEdge parentEdge : mInEdges.getOrDefault(edge.mSource, new HashSet<>())) {
			parentEdge.addChildren(edgeList);
		}
	}

	public HashSet<Variable> getVariables() {
		return mVariables;
	}

	public HashSet<IcfgLocation> getLocations() {
		return mLocations;
	}
}
