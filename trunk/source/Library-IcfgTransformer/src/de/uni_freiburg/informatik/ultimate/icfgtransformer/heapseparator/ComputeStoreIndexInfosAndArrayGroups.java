package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityAllowStores;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityLocUpdateInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SubtreePosition;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * A Note on the notion of array writes in our setting:
 * <li>array writes are to an array group
 * <li>a write to an array group is given by a store term in the program whose
 * base array is an array of the group
 * <li>as the base arrays on both sides of an equation are always in the same
 * array group, the write is also to the array on the side of the equation other
 * from where the store term is (so the standard notion of array updates is
 * covered, but also for example assume statements in Boogie can constitute an
 * array write)
 *
 * We compute array groups per TransFormula and globally, where the per
 * transformula partitions form the constraints for the global partition. Aux
 * vars may also belong to an array group, because they are equated to some term
 * that belongs to a pvoc in their TransFormula.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LOC>
 */
class ComputeStoreInfosAndArrayGroups<LOC extends IcfgLocation> {

	private final NestedMap2<EdgeInfo, Term, StoreInfo> mEdgeToStoreToStoreInfo = new NestedMap2<>();

	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup = new HashMap<>();

	/**
	 * (Actually, we are probably only interested if each term belongs to the array
	 * group of any heap array)
	 */
	private final NestedMap2<EdgeInfo, Term, ArrayGroup> mEdgeToTermToArrayGroup = new NestedMap2<>();

	/**
	 * We need this internal partitions when inserting the loc-array updates later.
	 */

	/**
	 * Note that index -1 is reserved for the "NoStoreInfo" object. This counter
	 * should always be non-negative, so no mId-clash occurs.
	 */
	private int mStoreInfoCounter;

	private final MemlocArrayManager mLocArrayManager;

	private final ManagedScript mMgdScript;

	private NestedMap2<EdgeInfo, SubtreePosition, ArrayEqualityLocUpdateInfo> mEdgeToPositionToLocUpdateInfo;

	private final Set<HeapSepProgramConst> mLocLiterals;


	final HashRelation<EdgeInfo, TermVariable> mEdgeToUnconstrainedVariables = new HashRelation<>();

	public ComputeStoreInfosAndArrayGroups(final IIcfg<LOC> icfg, final List<IProgramVarOrConst> heapArrays,
			final ManagedScript mgdScript) {

		mMgdScript = mgdScript;

		mLocArrayManager = new MemlocArrayManager(mgdScript);

		mLocLiterals = new HashSet<>();

		run(icfg, heapArrays);
	}

	private void run(final IIcfg<LOC> icfg, final List<IProgramVarOrConst> heapArrays) throws AssertionError {
		final UnionFind<IProgramVarOrConst> globalArrayPartition = new UnionFind<>();
		// base line for the array groups: the heap arrays
		heapArrays.forEach(globalArrayPartition::findAndConstructEquivalenceClassIfNeeded);

		/*
		 * Build edge-level array groups.
		 * I.e. Terms that are weakly/strongly equivalent in an edge are in an edge-level array group.
		 *
		 * Note that the notion of edge-level array group is already imprecise in some sense:
		 *  Example: edge formula: a = b \/ b = c
		 *      we would put a, b, c into one array group here, even though a and c are never related in the edge.
		 * (our algorithm here does not account for Boolean structure of the formula, it simply considers all =
		 *  predicates)
		 * However this overapproximation does not hurt soundness of our heap separation.
		 *
		 */
		final Map<EdgeInfo, UnionFind<Term>> edgeToPerEdgeArrayPartition = new HashMap<>();
		{
			final IcfgEdgeIterator edgeIt = new IcfgEdgeIterator(icfg);
			while (edgeIt.hasNext()) {
				final IcfgEdge edge = edgeIt.next();
				final UnmodifiableTransFormula tf = edge.getTransformula();
				final EdgeInfo edgeInfo = new EdgeInfo(edge);

				if (SmtUtils.containsFunctionApplication(tf.getFormula(), "or")
						|| !SmtUtils.isNNF(tf.getFormula())) {
					throw new UnsupportedOperationException("this computation can only handle conjunctive formulas at"
							+ "the moment");
				}

				/*
				 * construct the per-edge (or per-transformula, the difference does not matter here) array partition
				 */
				final UnionFind<Term> perTfArrayPartition = new UnionFind<>();

				final List<ArrayEqualityAllowStores> aeass = ArrayEqualityAllowStores
						.extractArrayEqualityAllowStores(tf.getFormula());

				// compute edge-specific array groups
				for (final ArrayEqualityAllowStores aeas : aeass) {
					final Term lhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getLhsArray());
					final Term rhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getRhsArray());

					perTfArrayPartition.findAndConstructEquivalenceClassIfNeeded(lhsArrayTerm);
					perTfArrayPartition.findAndConstructEquivalenceClassIfNeeded(rhsArrayTerm);
					perTfArrayPartition.union(lhsArrayTerm, rhsArrayTerm);
				}
				edgeToPerEdgeArrayPartition.put(edgeInfo, perTfArrayPartition);

				/*
				 * update the global array partition
				 */
				for (final Set<Term> eqc : perTfArrayPartition.getAllEquivalenceClasses()) {
					// pick some element that has a pvoc from the group of array terms

					final Set<IProgramVarOrConst> eqcPvocs = eqc.stream()
							.map(term -> TransFormulaUtils.getProgramVarOrConstForTerm(tf, term))
							.filter(pvoc -> pvoc != null).collect(Collectors.toSet());
					eqcPvocs.forEach(globalArrayPartition::findAndConstructEquivalenceClassIfNeeded);
					globalArrayPartition.union(eqcPvocs);
				}

				// compute constrained variables
				final Set<TermVariable> unconstrainedVars = computeUnconstrainedVariables(tf, aeass);
				mEdgeToUnconstrainedVariables.addAllPairs(edgeInfo, unconstrainedVars);
			}
		}

		/*
		 * Construct the program-level array groups.
		 */
		{
			final Set<ArrayGroup> arrayGroups = new HashSet<>();
			for (final Set<IProgramVarOrConst> block : globalArrayPartition.getAllEquivalenceClasses()) {
				arrayGroups.add(new ArrayGroup(block));
			}

			for (final ArrayGroup ag : arrayGroups) {
				if (DataStructureUtils.intersection(new HashSet<>(heapArrays), ag.getArrays()).isEmpty()) {
					/* we are only interested in writes to heap arrays */
					continue;
				}
				for (final IProgramVarOrConst a : ag.getArrays()) {
					mArrayToArrayGroup.put(a, ag);
				}
			}
		}

		/**
		 * Construct the map {@link #mEdgeToTermToArrayGroup}, which link each Term in an edge to a program-level
		 * array group. (or to null, if we do not track the term)
		 */
		{
			for (final Entry<EdgeInfo, UnionFind<Term>> en : edgeToPerEdgeArrayPartition.entrySet()) {
				final EdgeInfo edgeInfo = en.getKey();

				for (final Set<Term> block : en.getValue().getAllEquivalenceClasses()) {
					/*
					 * find a Term that has an IProgramVarOrConst according to the EdgeInfo (there
					 * must be one as the above analysis starts from IProgramVarOrConsts, right (the
					 * heap arrays)? (a formula relating a group of auxVars only within itself would
					 * be weird anyway) (if that assertion does not hold, see commented out code
					 * below for a possible fix)
					 */
					final Optional<IProgramVarOrConst> opt = block.stream()
							.map(t -> edgeInfo.getProgramVarOrConstForTerm(t)).filter(pvoc -> pvoc != null).findAny();
					if (!opt.isPresent()) {
						throw new AssertionError("see comment");
					}
					final ArrayGroup arrayGroup = mArrayToArrayGroup.get(opt.get());

					for (final Term t : block) {
						mEdgeToTermToArrayGroup.put(edgeInfo, t, arrayGroup);
					}
				}
			}
		}

		/*
		 * Construct StoreInfos for later use. Store them in a map with keys in EdgeInfos x SubtreePositions.
		 */
		{
			final IcfgEdgeIterator it = new IcfgEdgeIterator(icfg);
			while (it.hasNext()) {
				final IcfgEdge edge = it.next();
				final EdgeInfo edgeInfo = new EdgeInfo(edge);

				final Map<Term, ArrayGroup> termToArrayGroupForCurrentEdge = mEdgeToTermToArrayGroup.get(edgeInfo);

				final BuildStoreInfos bsi = new BuildStoreInfos(edgeInfo, termToArrayGroupForCurrentEdge, mMgdScript,
						mLocArrayManager, mStoreInfoCounter);
				bsi.buildStoreInfos();
				for (final Entry<SubtreePosition, ArrayEqualityLocUpdateInfo> en :
						bsi.getLocArrayUpdateInfos().entrySet()) {
					mEdgeToPositionToLocUpdateInfo.put(edgeInfo, en.getKey(), en.getValue());
				}
				mLocLiterals.addAll(bsi.getLocLiterals());
				// (managing the store counter this way is a bit inelegant..)
				mStoreInfoCounter = bsi.getStoreInfoCounter();
			}
		}
	}

	private Set<TermVariable> computeUnconstrainedVariables(final UnmodifiableTransFormula tf,
			final List<ArrayEqualityAllowStores> aeass) {
		final Set<TermVariable> constrainedVars = new HashSet<>();
		final Set<TermVariable> unconstrainedVars =
				new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
		boolean goOn = true;
		while (goOn) {
			goOn = false;
			for (final ArrayEqualityAllowStores aeas : aeass) {
				final Term lhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getLhsArray());
				final Term rhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getRhsArray());

				final TermVariable lhsArrayTv =
						(lhsArrayTerm instanceof TermVariable) ? (TermVariable) lhsArrayTerm : null;
				final TermVariable rhsArrayTv =
								(rhsArrayTerm instanceof TermVariable) ? (TermVariable) rhsArrayTerm : null;

				// code for determining which variables are unconstrained ("havocced") in this edge
				final boolean lhsIsAStore = lhsArrayTerm != aeas.getLhsArray();
				final boolean rhsIsAStore = rhsArrayTerm != aeas.getRhsArray();
				final boolean neitherIsAStore = !lhsIsAStore && !rhsIsAStore;

				if (lhsArrayTv == null && rhsArrayTv != null) {
					// constants are constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, rhsArrayTv);
				}
				if (rhsArrayTv == null && lhsArrayTv != null) {
					// constants are constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, lhsArrayTv);
				}

				if (tf.getInVars().containsValue(lhsArrayTv)) {
					// in vars are constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, lhsArrayTv);
				}
				if (tf.getInVars().containsValue(rhsArrayTv)) {
					// in vars are constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, rhsArrayTv);
				}

				if (neitherIsAStore && constrainedVars.contains(lhsArrayTv) && rhsArrayTv != null) {
					// strong equality, lhs is constrained --> rhs is constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, rhsArrayTv);
				}

				if (neitherIsAStore && constrainedVars.contains(rhsArrayTv) && lhsArrayTv != null) {
					// strong equality, rhs is constrained --> lhs is constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, lhsArrayTv);
				}

				if (lhsIsAStore && rhsArrayTv != null && unconstrainedVars.contains(rhsArrayTv)) {
					// lhs is a store --> rhs is constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, rhsArrayTv);
				}
				if (rhsIsAStore && lhsArrayTv != null && unconstrainedVars.contains(lhsArrayTv)) {
					// rhs is a store --> lhs is constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, lhsArrayTv);
				}
			}
		}
		return unconstrainedVars;
	}

	/**
	 *
	 * @param constrainedVars
	 * @param unconstrainedVars
	 * @param tv
	 * @return true iff changes were made
	 */
	private boolean markAsConstrainedIfNecessary(final Set<TermVariable> constrainedVars,
			final Set<TermVariable> unconstrainedVars, final TermVariable tv) {
		if (constrainedVars.contains(tv)) {
			assert !unconstrainedVars.contains(tv);
			return false;
		}
		unconstrainedVars.remove(tv);
		constrainedVars.add(tv);
		return true;
	}

	public Map<IProgramVarOrConst, ArrayGroup> getArrayToArrayGroup() {
		return Collections.unmodifiableMap(mArrayToArrayGroup);
	}

	public MemlocArrayManager getLocArrayManager() {
		return mLocArrayManager;
	}

	public NestedMap2<EdgeInfo, SubtreePosition, ArrayEqualityLocUpdateInfo> getEdgeToPositionToLocUpdateInfo() {
		return mEdgeToPositionToLocUpdateInfo;
	}

	public Set<HeapSepProgramConst> getLocLiterals() {
		return mLocLiterals;
	}

	/**
	 * @return per edge, the variables that are unconstrained/havocced by that edge. (Assuming purely conjunctive edges
	 *  at the moment.)
	 */
	public HashRelation<EdgeInfo, TermVariable> getEdgeToUnconstrainedVariables() {
		return mEdgeToUnconstrainedVariables;
	}
}

class BuildStoreInfos extends NonRecursive {

	/**
	 * The edge the store infos belong to.
	 */
	private final EdgeInfo mEdge;
	private final Map<Term, ArrayGroup> mTermToArrayGroup;
	private final ManagedScript mMgdScript;

	private final Map<SubtreePosition, StoreInfo> mCollectedStoreInfos = new HashMap<>();
	private final MemlocArrayManager mLocArrayManager;
	private final List<HeapSepProgramConst> mLocLiterals = new ArrayList<>();
	private int mSiidCtr;
	private Map<SubtreePosition, ArrayEqualityLocUpdateInfo> mPositionToLocArrayUpdateInfos;


	BuildStoreInfos(final EdgeInfo edge, final Map<Term, ArrayGroup> termToArrayGroup, final ManagedScript mgdScript,
			final MemlocArrayManager locArrayManager, final int storeInfoCounter) {
		mEdge = edge;
		mTermToArrayGroup = termToArrayGroup;
		mMgdScript = mgdScript;
		mLocArrayManager = locArrayManager;
		mSiidCtr = storeInfoCounter;
	}

	public Map<SubtreePosition, ArrayEqualityLocUpdateInfo> getLocArrayUpdateInfos() {
		return mPositionToLocArrayUpdateInfos;
	}

	public void buildStoreInfos() {
		run(new BuildStoreInfoWalker(mEdge.getEdge().getTransformula().getFormula(), new SubtreePosition(),
				new ArrayIndex(), null, null));
	}

	public Map<SubtreePosition, StoreInfo> getStoreInfos() {
		return mCollectedStoreInfos;
	}

	public Map<SubtreePosition, ArrayEqualityLocUpdateInfo> getPositionToLocArrayUpdateInfos() {
		return mPositionToLocArrayUpdateInfos;
	}

	public List<HeapSepProgramConst> getLocLiterals() {
		return mLocLiterals;
	}

	public int getStoreInfoCounter() {
		return mSiidCtr;
	}

	/**
	 * Note that this walks the Term "tree-style". For Terms with extensive sharing of sub-terms this may explode.
	 * (But we want to take the surrounding of each store Term into account, so we must do it this way.)
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
//	private class BuildStoreInfoWalker extends PositionTrackingTermWalker {
	private class BuildStoreInfoWalker extends TermWalker {

		private final ArrayIndex mEnclosingStoreIndices;
		private final SubtreePosition mSubTreePosition;
		/**
		 * position relative to the equality the current Term occurs in.
		 */
		private final SubtreePosition mRelativePosition;
//		private final StoreInfo mOuterMostStore;
		private final ArrayEqualityLocUpdateInfo mEnclosingEquality;

		public BuildStoreInfoWalker(final Term term, final SubtreePosition position,
				final ArrayIndex enclosingStoreIndices, final ArrayEqualityLocUpdateInfo enclosingEquality,
				final SubtreePosition relativePosition) {
//			super(term, position);
			super(term);
			mEnclosingStoreIndices = enclosingStoreIndices;
			mSubTreePosition = position;
//			mOuterMostStore = outerMostStore;
			mEnclosingEquality = enclosingEquality;
			mRelativePosition = relativePosition;
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// do nothing
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubterm(), mSubTreePosition.append(0),
					mEnclosingStoreIndices, mEnclosingEquality, mRelativePosition.append(0)));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			final String funcName = term.getFunction().getName();
			switch (funcName) {
			case "store":
			{
				final int siId = getNextStoreInfoId();
				final int siDim = mEnclosingStoreIndices.size() + 1;
				final StoreInfo si = StoreInfo.buildStoreInfo(siId, mEdge, mSubTreePosition, term,
						mTermToArrayGroup.get(term), mEnclosingStoreIndices,
						constructLocationLiteral(mEdge, siId, siDim), mEnclosingEquality, mRelativePosition);
				mCollectedStoreInfos.put(mSubTreePosition, si);
			}
			{
				// dive deeper into the array (no change to enclosing store indices)
				walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[0], mSubTreePosition.append(0),
						mEnclosingStoreIndices, mEnclosingEquality, mRelativePosition.append(0)));
				// dive deeper into the value
				final ArrayIndex newEnclosingStoreIndicesForValue =
						mEnclosingStoreIndices.append(term.getParameters()[1]);
				walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[2], mSubTreePosition.append(2),
						newEnclosingStoreIndicesForValue, mEnclosingEquality, mRelativePosition.append(2)));
			}
				break;
			case "=":
				if (term.getParameters()[0].getSort().isArraySort()) {
					assert mEnclosingEquality == null;
					final ArrayEqualityLocUpdateInfo newEnclosingEquality =
							new ArrayEqualityLocUpdateInfo(mEdge, mLocArrayManager);
					walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[0], mSubTreePosition.append(0),
						 mEnclosingStoreIndices, newEnclosingEquality, new SubtreePosition().append(0)));
					walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[1], mSubTreePosition.append(1),
							mEnclosingStoreIndices, newEnclosingEquality, new SubtreePosition().append(1)));
					mPositionToLocArrayUpdateInfos.put(mSubTreePosition, newEnclosingEquality);
				}
				// do nothing if the equated terms are not of array type
				break;
			default:
				if ("Bool".equals(term.getSort().getName()) && SmtUtils.allParamsAreBool(term)) {
					assert mEnclosingEquality == null;
					// we have a Boolean connective --> dive deeper
					for (int i = 0; i < term.getParameters().length; i++) {
						final Term param = term.getParameters()[i];
						walker.enqueueWalker(new BuildStoreInfoWalker(param, mSubTreePosition.append(i),
								mEnclosingStoreIndices, null, null));
					}
				} else {
					// do nothing
				}
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubTerm(), mSubTreePosition.append(0),
					mEnclosingStoreIndices, mEnclosingEquality, mRelativePosition.append(0)));
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			assert mEnclosingEquality == null;
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubformula(), mSubTreePosition.append(0),
					mEnclosingStoreIndices, null, null));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// do nothing
		}

	}

	private int getNextStoreInfoId() {
		mSiidCtr++;
		return mSiidCtr;
	}

	private IProgramConst constructLocationLiteral(final EdgeInfo edgeInfo, final int storeInfoId, final int storeDim) {

		assert storeInfoId > 0 : "use a long if this may overflow";

		mMgdScript.lock(this);

		final String locLitName = getLocationLitName(edgeInfo, storeInfoId);

		final Sort sort = mLocArrayManager.getMemlocSort(storeDim);

		mMgdScript.declareFun(this, locLitName, new Sort[0], sort);
		final ApplicationTerm locLitTerm = (ApplicationTerm) mMgdScript.term(this, locLitName);

		mMgdScript.unlock(this);

		final HeapSepProgramConst result = new HeapSepProgramConst(locLitTerm);
		mLocLiterals .add(result);
		return result;
	}

	private String getLocationLitName(final EdgeInfo location, final int storeInfoId) {
		return "lit_" + location.getSourceLocation() + "_" + storeInfoId;
	}
}