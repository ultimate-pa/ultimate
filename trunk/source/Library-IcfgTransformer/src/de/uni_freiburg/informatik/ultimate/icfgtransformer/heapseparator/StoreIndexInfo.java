package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Represents an index that is used in a store term somewhere in the program.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StoreIndexInfo {
	private final EdgeInfo mEdgeInfo;
	private final Term mTerm;

	/**
	 * Each array write happens at a certain dimension of ore or more arrays.
	 *  (+ the same Term may be used to do more than one array write in an IcfgEdge)
	 *
	 * which array is written at which dimensions in the given edge with the given term
	 */
	private final HashRelation<IProgramVarOrConst, Integer> mArrayToAccessDimensions;

	private final Set<Integer> mAccessDimensions;

	/**
	 *
	 * @param edgeInfo
	 * @param term
	 */
	public StoreIndexInfo(final EdgeInfo edgeInfo, final Term term) {
		super();
		mEdgeInfo = edgeInfo;
		mTerm = term;
		mArrayToAccessDimensions = new HashRelation<>();// = computeArrayToAccessDimensions(edgeInfo, term);
		mAccessDimensions = new HashSet<>();
	}

//	private HashRelation<IProgramVarOrConst, Integer> computeArrayToAccessDimensions(final EdgeInfo edgeInfo, final Term term) {
//		final ApplicationTermFinder atf = new
//		for (SmtUtils.find)
//		// TODO Auto-generated method stub
//		return null;
//	}

	public void addArrayAccessDimension(final IProgramVarOrConst array, final Integer accessDimension) {
		mArrayToAccessDimensions.addPair(array, accessDimension);
		mAccessDimensions.add(accessDimension);
	}

	public EdgeInfo getEdgeInfo() {
		return mEdgeInfo;
	}

	public Term getIndexTerm() {
		return mTerm;
	}

	public Set<Integer> getAccessDimensions() {
		return Collections.unmodifiableSet(mAccessDimensions);
	}

	/**
	 *
	 * @return all the arrays that the stores with mTerm refer to in mEdgeInfo.
	 */
	public Set<IProgramVarOrConst> getArrays() {
		return mArrayToAccessDimensions.getDomain();
	}

	public HashRelation<IProgramVarOrConst, Integer> getArrayToAccessDimensions() {
		return mArrayToAccessDimensions;
	}

	@Override
	public String toString() {
		return "(Store at" + mEdgeInfo + " with " + mTerm + ")";
	}

}

/**
 * Wrapper for an IcfgEdge that carries information about the edge that we are interested in in the heap separator.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
class EdgeInfo {
	IcfgEdge mEdge;

	EdgeInfo(final IcfgEdge edge) {
		mEdge = edge;
	}

	public IProgramVarOrConst getProgramVarOrConstForTerm(final Term term) {
		return TransFormulaUtils.getProgramVarOrConstForTerm(mEdge.getTransformula(), term);
	}

	public IcfgLocation getSourceLocation() {
		return mEdge.getSource();
	}

	public IcfgEdge getEdge() {
		return mEdge;
	}

	@Override
	public String toString() {
		return "(" + mEdge + ")";
	}
}
