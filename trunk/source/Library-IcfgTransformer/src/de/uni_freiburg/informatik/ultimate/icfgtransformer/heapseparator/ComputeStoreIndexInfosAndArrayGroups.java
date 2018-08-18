package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
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

	private int mMemLocLitCounter;

//	private final Map<StoreInfo, IProgramConst> mStoreInfoToLocLiteral = new HashMap<>();

	private final MemlocArrayManager mLocArrayManager;

	private final ManagedScript mMgdScript;

	public ComputeStoreInfosAndArrayGroups(final IIcfg<LOC> icfg, final List<IProgramVarOrConst> heapArrays,
			final ManagedScript mgdScript) {

		mMgdScript = mgdScript;

		mLocArrayManager = new MemlocArrayManager(mgdScript);

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

				/*
				 * construct the per-edge (or per-transformula, the difference does not matter here) array partition
				 */
				final UnionFind<Term> perTfArrayPartition = new UnionFind<>();

				final List<ArrayEqualityAllowStores> aeass = ArrayEqualityAllowStores
						.extractArrayEqualityAllowStores(tf.getFormula());
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

		// more or less accidentally duplicated this code above.. leaving the old for
		// comparison, for the moment.
		// // set up the mapping of terms to ArrayGroups for each edge/TransFormula
		// final NestedMap2<EdgeInfo, Term, ArrayGroup> edgeToTermToArrayGroup = new
		// NestedMap2<>();
		// {
		// for (final Entry<EdgeInfo, UnionFind<Term>> en :
		// edgeToPerEdgeArrayPartition.entrySet()) {
		// for (final Term arrayTerm : en.getValue().getAllElements()) {
		//
		// /*
		// * does the current arrayTerm's partition block contain a term that belongs to
		// a pvoc?
		// * if yes: map it to that pvoc's array group
		// * if no: map it to the "NoArrayGroup" dummy array group
		// */
		// final IProgramVarOrConst pvocInSameBlock =
		// findPvoc(en.getKey().getEdge().getTransformula(),
		// en.getValue().getEquivalenceClassMembers(arrayTerm));
		// if (pvocInSameBlock == null) {
		// edgeToTermToArrayGroup.put(en.getKey(), arrayTerm,
		// ArrayGroup.getNoArrayGroup());
		// } else {
		// edgeToTermToArrayGroup.put(en.getKey(), arrayTerm,
		// mArrayToArrayGroup.get(pvocInSameBlock));
		// }
		// }
		// }
		// }

		/*
		 * Construct StoreInfos for later use
		 */
		{
			final IcfgEdgeIterator it = new IcfgEdgeIterator(icfg);
			while (it.hasNext()) {
				final IcfgEdge edge = it.next();
				final EdgeInfo edgeInfo = new EdgeInfo(edge);

				final Map<Term, ArrayGroup> termToArrayGroupForCurrentEdge = mEdgeToTermToArrayGroup.get(edgeInfo);

				final BuildStoreInfos bsi = new BuildStoreInfos(edgeInfo, termToArrayGroupForCurrentEdge, mMgdScript,
						mLocArrayManager);
				bsi.buildStoreInfos();
				bsi.getLocLiterals();
				bsi.getStoreInfos();

//				final Map<Term, ArrayGroup> arrayTermToArrayGroup = mEdgeToTermToArrayGroup.get(edgeInfo);
//
//				/*
//				 * construct the StoreInfos
//				 */
//				for (final StoreInfo2 store : StoreInfo2.extractStores(tf.getFormula(), arrayTermToArrayGroup)) {
//
//					if (DataStructureUtils.intersection(new HashSet<>(heapArrays), store.getArrayGroup().getArrays())
//							.isEmpty()) {
//						/* we are only interested in writes to heap arrays */
//						continue;
//					}
//
//					// final StoreInfo storeIndexInfo = getOrConstructStoreInfo(edgeInfo,
//					// store.getWriteIndex());
//					// storeIndexInfo.addArrayAccessDimension(store.getWrittenArray(),
//					// store.getWrittenDimension());
//					getOrConstructStoreInfo(edgeInfo, store.getStoreTerm(), store.getArrayGroup());
//				}
			}
		}
	}

//	/**
//	 * Search through the set of terms for a term that belongs to a pvoc according
//	 * to the given TransFormula.
//	 *
//	 * @return
//	 */
//	private static IProgramVarOrConst findPvoc(final TransFormula edge, final Set<Term> terms) {
//		for (final Term term : terms) {
//			final IProgramVarOrConst pvoc = TransFormulaUtils.getProgramVarOrConstForTerm(edge, term);
//			if (pvoc != null) {
//				return pvoc;
//			}
//		}
//		return null;
//	}

	// public NestedMap2<EdgeInfo, Term, StoreInfo> getEdgeToIndexToStoreIndexInfo()
	// {
	// return mEdgeToStoreToArrayToStoreInfo;
	// }

	public Map<IProgramVarOrConst, ArrayGroup> getArrayToArrayGroup() {
		return Collections.unmodifiableMap(mArrayToArrayGroup);
	}

	public NestedMap2<EdgeInfo, Term, StoreInfo> getEdgeToStoreToStoreInfo() {
		return mEdgeToStoreToStoreInfo;
	}

	// public Map<EdgeInfo, UnionFind<Term>> getEdgeToPerEdgeArrayPartition() {
	// return edgeToPerEdgeArrayPartition;
	// }

	public NestedMap2<EdgeInfo, Term, ArrayGroup> getEdgeToTermToArrayGroup() {
		return mEdgeToTermToArrayGroup;
	}



	public MemlocArrayManager getLocArrayManager() {
		return mLocArrayManager;
	}

//	/**
//	 * updates mEdgeToIndexToStoreInfo
//	 *
//	 * @param tfInfo
//	 * @param storeTerm
//	 * @param array
//	 *            (aux info, not part of the identifier of a StoreInfo)
//	 * @return
//	 */
//	private StoreInfo getOrConstructStoreInfo(final EdgeInfo tfInfo, final Term storeTerm, final ArrayGroup array) {
//		StoreInfo sii = mEdgeToStoreToStoreInfo.get(tfInfo, storeTerm);
//		if (sii == null) {
//			// sii = new StoreInfo(tfInfo, indexTerm, mStoreIndexInfoCounter++);
//			final int storeInfoId = mStoreInfoCounter++;
//
//			locLit = getOrConstructLocationLiteral(tfInfo, storeInfoId, storeDim);
//
//			sii = new StoreInfo(tfInfo, storeTerm, array, storeInfoId);
////			final sii.addLoc
//			mEdgeToStoreToStoreInfo.put(tfInfo, storeTerm, sii);
//		}
//		return sii;
//	}
//
//	private IProgramConst getOrConstructLocationLiteral(final EdgeInfo edgeInfo, final int storeInfoId,
//			final int storeDim) {
//
//		assert storeInfoId > 0 : "use a long if this may overflow";
//
//		mMgdScript.lock(this);
//
//		final String locLitName = getLocationLitName(edgeInfo, storeInfoId);
//
//		final Sort sort = mLocArrayManager.getMemlocSort(storeDim);
//
//		mMgdScript.declareFun(this, locLitName, new Sort[0], sort);
//		final ApplicationTerm locLitTerm = (ApplicationTerm) mMgdScript.term(this, locLitName);
//
//		mMgdScript.unlock(this);
//
//		return new HeapSepProgramConst(locLitTerm);
//
//	}

	private String getLocationLitName(final EdgeInfo location, final int storeInfoId) {
		return "lit_" + location.getSourceLocation() + "_" + storeInfoId;
	}

//	static class StoreInfo2 {
//
//		// private final IProgramVarOrConst mWrittenArray;
//		private final Term mStoreTerm;
//		private final ArrayGroup mArrayGroup;
//		private final int mWrittenDimension;
//		private final Term mWriteIndex;
//
//		// public StoreInfo(final IProgramVarOrConst writtenArray, final int
//		// writtenDimension, final Term writeIndex) {
//		public StoreInfo2(final Term storeTerm, final ArrayGroup arrayGroup, final int writtenDimension,
//				final Term writeIndex) {
//			mStoreTerm = storeTerm;
//			mArrayGroup = arrayGroup;
//			mWrittenDimension = writtenDimension;
//			mWriteIndex = writeIndex;
//		}
//
//		public static Set<StoreInfo2> extractStores(final Term inputTerm,
//				final Map<Term, ArrayGroup> termToArrayGroup) {
//			final Set<StoreInfo2> result = new HashSet<>();
//
//			final Set<ApplicationTerm> allStores = new ApplicationTermFinder("store", false)
//					.findMatchingSubterms(inputTerm);
//
//			for (final ApplicationTerm storeTerm : allStores) {
//
//				final Term arrayTerm = storeTerm.getParameters()[0];
//				final Term index = storeTerm.getParameters()[1];
//
//				final Term arrayId = SmtUtils.getBasicArrayTerm(arrayTerm);
//
//				/*
//				 * @formatter:off Example: 1 (store a i1 2 (store (select a i1) i2 3 (store
//				 * (select (select a i1) i2) i3 v))) Now say the current storeTerm is the one in
//				 * line 3 and we want to know at which dimension a is accessed by i3. We compute
//				 * (dimensionality of a) - (dimensionality of store3) = 3 - 1 = 2 . (so, by
//				 * convention we count the access dimensions starting from 0)
//				 *
//				 * @formatter:on
//				 */
//				final int writtenDimension = new MultiDimensionalSort(arrayId.getSort()).getDimension()
//						- new MultiDimensionalSort(storeTerm.getSort()).getDimension();
//
//				final ArrayGroup arrayPvoc = termToArrayGroup.get(arrayId);
//				if (arrayPvoc == null) {
//					// array is not tracked: do not make a StoreInfo for it
//					continue;
//				}
//				// assert arrayPvoc != null;
//
//				result.add(new StoreInfo2(storeTerm, arrayPvoc, writtenDimension, index));
//			}
//
//			return result;
//		}
//
//		// public IProgramVarOrConst getWrittenArray() {
//		public ArrayGroup getArrayGroup() {
//			return mArrayGroup;
//		}
//
//		public int getWrittenDimension() {
//			return mWrittenDimension;
//		}
//
//		public Term getWriteIndex() {
//			return mWriteIndex;
//		}
//
//		public Term getStoreTerm() {
//			return mStoreTerm;
//		}
//
//		@Override
//		public int hashCode() {
//			final int prime = 31;
//			int result = 1;
//			result = prime * result + ((mArrayGroup == null) ? 0 : mArrayGroup.hashCode());
//			result = prime * result + mWrittenDimension;
//			result = prime * result + ((mWriteIndex == null) ? 0 : mWriteIndex.hashCode());
//			return result;
//		}
//
//		@Override
//		public boolean equals(final Object obj) {
//			if (this == obj) {
//				return true;
//			}
//			if (obj == null) {
//				return false;
//			}
//			if (getClass() != obj.getClass()) {
//				return false;
//			}
//			final StoreInfo2 other = (StoreInfo2) obj;
//			if (mArrayGroup == null) {
//				if (other.mArrayGroup != null) {
//					return false;
//				}
//			} else if (!mArrayGroup.equals(other.mArrayGroup)) {
//				return false;
//			}
//			if (mWrittenDimension != other.mWrittenDimension) {
//				return false;
//			}
//			if (mWriteIndex == null) {
//				if (other.mWriteIndex != null) {
//					return false;
//				}
//			} else if (!mWriteIndex.equals(other.mWriteIndex)) {
//				return false;
//			}
//			return true;
//		}
//
//	}
}

class BuildStoreInfos extends NonRecursive {

	/**
	 * The edge the store infos belong to.
	 */
	private final EdgeInfo mEdge;
	private final Map<Term, ArrayGroup> mTermToArrayGroup;
	private final ManagedScript mMgdScript;

	private final List<StoreInfo> mCollectedStoreInfos = new ArrayList<>();
	private final MemlocArrayManager mLocArrayManager;
	private final List<HeapSepProgramConst> mLocLiterals = new ArrayList<>();


	BuildStoreInfos(final EdgeInfo edge, final Map<Term, ArrayGroup> termToArrayGroup, final ManagedScript mgdScript,
			final MemlocArrayManager locArrayManager) {
		mEdge = edge;
		mTermToArrayGroup = termToArrayGroup;
		mMgdScript = mgdScript;
		mLocArrayManager = locArrayManager;
	}

	public void buildStoreInfos() {
		run();
	}

	public List<StoreInfo> getStoreInfos() {
		return mCollectedStoreInfos;
	}

	public List<HeapSepProgramConst> getLocLiterals() {
		return mLocLiterals;
	}

	/**
	 * Note that this walks the Term "tree-style". For Terms with extensive sharing of sub-terms this may explode.
	 * (But we want to take the surrounding of each store Term into account, so we must do it this way.)
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	private class BuildStoreInfoWalker extends TermWalker {

		private final ArrayIndex mEnclosingStoreIndices;

		public BuildStoreInfoWalker(final Term term, final ArrayIndex enclosingStoreIndices) {
			super(term);
			mEnclosingStoreIndices = enclosingStoreIndices;
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// do nothing
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubterm(), mEnclosingStoreIndices));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			final String funcName = term.getFunction().getName();
			switch (funcName) {
			case "store":
			{
				final int siId = getNextStoreInfoId();
				final int siDim = mEnclosingStoreIndices.size() + 1;
				final StoreInfo si = new StoreInfo(siId, mEdge, term, mTermToArrayGroup.get(term),
						mEnclosingStoreIndices, constructLocationLiteral(mEdge, siId, siDim));
				mCollectedStoreInfos.add(si);
			}

			{
				final ArrayIndex newEnclosingStoreIndices = new ArrayIndex(mEnclosingStoreIndices);
				newEnclosingStoreIndices.add(term.getParameters()[1]);
				walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[2], newEnclosingStoreIndices));
			}
				break;
			case "=":
				if (term.getParameters()[0].getSort().isArraySort()) {
					walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[1], mEnclosingStoreIndices));
					walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[2], mEnclosingStoreIndices));
				}
				break;
			default:
				if ("Bool".equals(term.getSort().getName()) && SmtUtils.allParamsAreBool(term)) {
					// we have a Boolean connective --> dive deeper
					for (final Term param : term.getParameters()) {
						walker.enqueueWalker(new BuildStoreInfoWalker(param, mEnclosingStoreIndices));
					}

				} else {
					// do nothing
				}
			}

		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubTerm(), mEnclosingStoreIndices));
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubformula(), mEnclosingStoreIndices));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// do nothing
		}

	}

	private int getNextStoreInfoId() {
		// TODO Auto-generated method stub
		return 0;
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