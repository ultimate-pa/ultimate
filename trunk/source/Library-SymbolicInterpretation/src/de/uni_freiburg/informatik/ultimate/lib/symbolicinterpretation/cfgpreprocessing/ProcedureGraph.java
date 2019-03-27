package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.GenericLabeledGraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class ProcedureGraph extends GenericLabeledGraph<IcfgLocation, IIcfgTransition<IcfgLocation>> {

	private final IcfgLocation mEntryNode;
	private final IcfgLocation mExitNode;
	private final Set<IcfgLocation> mErrorNodes;

	public ProcedureGraph(final IcfgLocation entryNode, final IcfgLocation returnNode,
			final Set<IcfgLocation> errorNodes) {
		mEntryNode = entryNode;
		mExitNode = returnNode;
		mErrorNodes = errorNodes;
		mNodes.add(mEntryNode);
		mNodes.add(mExitNode);
		mNodes.addAll(mErrorNodes);
	}
	
	public ProcedureGraph(final IIcfg<IcfgLocation> icfg, final String procedureName) {
		this(icfg.getProcedureEntryNodes().get(procedureName), icfg.getProcedureExitNodes().get(procedureName),
				icfg.getProcedureErrorNodes().getOrDefault(procedureName, Collections.emptySet()));
	}

	public IcfgLocation getEntryNode() {
		return mEntryNode;
	}

	public IcfgLocation getExitNode() {
		return mExitNode;
	}

	public Set<IcfgLocation> getErrorNodes() {
		return mErrorNodes;
	}
}
