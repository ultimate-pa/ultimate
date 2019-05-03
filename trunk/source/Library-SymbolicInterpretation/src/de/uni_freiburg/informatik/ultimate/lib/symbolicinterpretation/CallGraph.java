package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.Collection;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class CallGraph {

	/**
	 * Temporary mark for {@link #mSuccessorsOfInterest} used in {@link #mark(String, String)} to detect
	 * cycles/recursion.
	 * <p>
	 * Cycle detection works as in Djikstra's DFS-based topological sorting, see
	 * <a href="https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search">Wikipedia</a>.
	 * <p>
	 * This mark has to be different from the usual marks. Usual marks are procedure names.
	 * Procedure names cannot be empty.
	 */
	private static final String TMP_MARK_TO_DETECT_CYCLES = "";

	private IIcfg<IcfgLocation> mIcfg;
	private Collection<IcfgLocation> mLocationsOfInterest;
	private HashRelation<String, String> mPredecessors = new HashRelation<>();
	private HashRelation<String, String> mSuccessorsOfInterest = new HashRelation<>();

	public CallGraph(final IIcfg<IcfgLocation> icfg, final Collection<IcfgLocation> locationsOfInterest) {
		mIcfg = icfg;
		mLocationsOfInterest = locationsOfInterest;
		buildGraph();
		markGraph();
	}

	private void buildGraph() {
		new IcfgEdgeIterator(mIcfg).asStream()
				.filter(edge -> edge instanceof IIcfgCallTransition<?>)
				.forEach(this::addCall);
	}

	private void addCall(final IcfgEdge call) {
		mPredecessors.addPair(call.getSource().getProcedure(), call.getTarget().getProcedure());
	}

	private void markGraph() {
		mLocationsOfInterest.stream()
				.map(IcfgLocation::getProcedure)
				.forEach(loi -> mark(loi, TMP_MARK_TO_DETECT_CYCLES));
	}

	private void mark(final String currentProcedure, final String mark) {
		if (!mSuccessorsOfInterest.addPair(currentProcedure, TMP_MARK_TO_DETECT_CYCLES)) {
			throw new IllegalArgumentException("Recursive programs are not supported.");
		} else if (mSuccessorsOfInterest.addPair(currentProcedure, mark)) {
			// Was already marked accordingly, therefore predecessors have to be already marked too.
			return;
		}
		mPredecessors.getImage(currentProcedure).forEach(predecessor -> mark(predecessor, currentProcedure));
		mSuccessorsOfInterest.removePair(currentProcedure, TMP_MARK_TO_DETECT_CYCLES);
	}

	public Collection<String> initialProcedures() {
		return mIcfg.getInitialNodes().stream().map(IcfgLocation::getProcedure).collect(Collectors.toList());
	}

	public Collection<String> successorsOfInterest(final String procedure) {
		return mSuccessorsOfInterest.getImage(procedure);
	}
}
