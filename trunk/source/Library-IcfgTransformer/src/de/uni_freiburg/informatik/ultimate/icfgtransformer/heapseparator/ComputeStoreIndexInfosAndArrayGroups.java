package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityAllowStores;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * A Note on the notion of array writes in our setting:
 * <li> array writes are to an array group
 * <li> a write to an array group is given by a store term in the program whose base array is an array of the group
 * <li> as the base arrays on both sides of an equation are always in the same array group, the write is also to the
 *   array on the side of the equation other from where the store term is (so the standard notion of array updates is
 *    covered, but also for example assume statements in Boogie can constitute an array write)
 *
 * We compute array groups per TransFormula and globally, where the per transformula partitions form the constraints
 * for the global partition.
 * Aux vars may also belong to an array group, because they are equated to some term that belongs to a pvoc in their
 * TransFormula.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LOC>
 */
class ComputeStoreInfosAndArrayGroups<LOC extends IcfgLocation> {

	private final NestedMap3<EdgeInfo, Term, ArrayGroup, StoreInfo> mEdgeToStoreToArrayToStoreInfo = new NestedMap3<>();

	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup = new HashMap<>();
	/**
	 * We need this internal partitions when inserting the loc-array updates later.
	 */
	private final Map<EdgeInfo, UnionFind<Term>> mEdgeToPerEdgeArrayPartition = new HashMap<>();

	/**
	 * Note that index -1 is reserved for the "NoStoreInfo" object. This counter should always be non-negative, so no
	 * mId-clash occurs.
	 */
	private int mStoreInfoCounter;

	public ComputeStoreInfosAndArrayGroups(final IIcfg<LOC> icfg, final List<IProgramVarOrConst> heapArrays) {

		final UnionFind<IProgramVarOrConst> globalArrayPartition = new UnionFind<>();
		// base line for the array groups: the heap arrays
		heapArrays.forEach(globalArrayPartition::findAndConstructEquivalenceClassIfNeeded);

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

				final List<ArrayEqualityAllowStores> aeass =
						ArrayEqualityAllowStores.extractArrayEqualityAllowStores(tf.getFormula());
				for (final ArrayEqualityAllowStores aeas : aeass) {
					final Term lhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getLhsArray());
					final Term rhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getRhsArray());
					perTfArrayPartition.findAndConstructEquivalenceClassIfNeeded(lhsArrayTerm);
					perTfArrayPartition.findAndConstructEquivalenceClassIfNeeded(rhsArrayTerm);
					perTfArrayPartition.union(lhsArrayTerm, rhsArrayTerm);
				}

				mEdgeToPerEdgeArrayPartition.put(edgeInfo, perTfArrayPartition);

				/*
				 * update the global array partition
				 */
				for (final Set<Term> eqc : perTfArrayPartition.getAllEquivalenceClasses()) {
					// pick some element that has a pvoc from the group of array terms

					final Set<IProgramVarOrConst> eqcPvocs = eqc.stream()
							.map(term -> TransFormulaUtils.getProgramVarOrConstForTerm(tf, term))
							.filter(pvoc -> pvoc != null)
							.collect(Collectors.toSet());
					eqcPvocs.forEach(globalArrayPartition::findAndConstructEquivalenceClassIfNeeded);
					globalArrayPartition.union(eqcPvocs);
				}
			}
		}

		/*
		 * Construct the array groups and their map.
		 */
		{
			final Set<ArrayGroup> arrayGroups = new HashSet<>();
			for (final Set<IProgramVarOrConst> block : globalArrayPartition.getAllEquivalenceClasses()) {
				arrayGroups.add(new ArrayGroup(block));
			}

			for (final ArrayGroup ag : arrayGroups) {
				if (DataStructureUtils.intersection(new HashSet<>(heapArrays), ag.getArrays())
						.isEmpty()) {
					/* we are only interested in writes to heap arrays */
					continue;
				}
				for (final IProgramVarOrConst a : ag.getArrays()) {
					mArrayToArrayGroup.put(a, ag);
				}
			}
		}

		// set up the mapping of terms to ArrayGroups for each edge/TransFormula
		final NestedMap2<EdgeInfo, Term, ArrayGroup> edgeToTermToArrayGroup = new NestedMap2<>();
		{
			for (final Entry<EdgeInfo, UnionFind<Term>> en : mEdgeToPerEdgeArrayPartition.entrySet()) {
				for (final Term arrayTerm : en.getValue().getAllElements()) {

					/*
					 * does the current arrayTerm's partition block contain a term that belongs to a pvoc?
					 *  if yes: map it to that pvoc's array group
					 *  if no: map it to the "NoArrayGroup" dummy array group
					 */
					final IProgramVarOrConst pvocInSameBlock =
							findPvoc(en.getKey().getEdge().getTransformula(),
									en.getValue().getEquivalenceClassMembers(arrayTerm));
					if (pvocInSameBlock == null) {
						edgeToTermToArrayGroup.put(en.getKey(), arrayTerm, ArrayGroup.getNoArrayGroup());
					} else {
						edgeToTermToArrayGroup.put(en.getKey(), arrayTerm, mArrayToArrayGroup.get(pvocInSameBlock));
					}
				}
			}
		}

		{
			final IcfgEdgeIterator it = new IcfgEdgeIterator(icfg);
			while (it.hasNext()) {
				final IcfgEdge edge = it.next();
				final UnmodifiableTransFormula tf = edge.getTransformula();
				final EdgeInfo edgeInfo = new EdgeInfo(edge);

				final Map<Term, ArrayGroup> arrayTermToArrayGroup = edgeToTermToArrayGroup.get(edgeInfo);

				/*
				 * construct the StoreInfos
				 */
				for (final StoreInfo2 store : StoreInfo2.extractStores(tf.getFormula(), arrayTermToArrayGroup)) {

					if (DataStructureUtils.intersection(new HashSet<>(heapArrays), store.getWrittenArray().getArrays())
							.isEmpty()) {
						/* we are only interested in writes to heap arrays */
						continue;
					}

//					final StoreInfo storeIndexInfo = getOrConstructStoreInfo(edgeInfo, store.getWriteIndex());
//					storeIndexInfo.addArrayAccessDimension(store.getWrittenArray(), store.getWrittenDimension());
					getOrConstructStoreInfo(edgeInfo, store.getStoreTerm(), store.getWrittenArray());
				}
			}
		}
	}

	/**
	 * Search through the set of terms for a term that belongs to a pvoc according to the given TransFormula.
	 *
	 * @return
	 */
	private static IProgramVarOrConst findPvoc(final TransFormula edge, final Set<Term> terms) {
		for (final Term term : terms) {
			final IProgramVarOrConst pvoc = TransFormulaUtils.getProgramVarOrConstForTerm(edge, term);
			if (pvoc != null) {
				return pvoc;
			}
		}
		return null;
	}

//	public NestedMap2<EdgeInfo, Term, StoreInfo> getEdgeToIndexToStoreIndexInfo() {
//		return mEdgeToStoreToArrayToStoreInfo;
//	}



	public Map<IProgramVarOrConst, ArrayGroup> getArrayToArrayGroup() {
		return Collections.unmodifiableMap(mArrayToArrayGroup);
	}

	public NestedMap3<EdgeInfo, Term, ArrayGroup, StoreInfo> getEdgeToStoreToArrayToStoreInfo() {
		return mEdgeToStoreToArrayToStoreInfo;
	}

	public Map<EdgeInfo, UnionFind<Term>> getEdgeToPerEdgeArrayPartition() {
		return mEdgeToPerEdgeArrayPartition;
	}

	/**
	 * updates mEdgeToIndexToStoreInfo
	 *
	 * @param tfInfo
	 * @param storeTerm
	 * @return
	 */
	private StoreInfo getOrConstructStoreInfo(final EdgeInfo tfInfo, final Term storeTerm,
			final ArrayGroup array) {
		StoreInfo sii = mEdgeToStoreToArrayToStoreInfo.get(tfInfo, storeTerm, array);
		if (sii == null) {
//			sii = new StoreInfo(tfInfo, indexTerm, mStoreIndexInfoCounter++);
			sii = new StoreInfo(tfInfo, storeTerm, array, mStoreInfoCounter++);
			mEdgeToStoreToArrayToStoreInfo.put(tfInfo, storeTerm, array, sii);
		}
		return sii;
	}


	static class StoreInfo2 {

		//	private final IProgramVarOrConst mWrittenArray;
		private final Term mStoreTerm;
		private final ArrayGroup mWrittenArray;
		private final int mWrittenDimension;
		private final Term mWriteIndex;

		//	public StoreInfo(final IProgramVarOrConst writtenArray, final int writtenDimension, final Term writeIndex) {
		public StoreInfo2(final Term storeTerm, final ArrayGroup writtenArray, final int writtenDimension,
				final Term writeIndex) {
			mStoreTerm = storeTerm;
			mWrittenArray = writtenArray;
			mWrittenDimension = writtenDimension;
			mWriteIndex = writeIndex;
		}


		//	public static Set<StoreInfo> extractStores(final Term inputTerm, final TransFormula tf) {
		public static Set<StoreInfo2> extractStores(final Term inputTerm, final Map<Term, ArrayGroup> termToArrayGroup) {
			final Set<StoreInfo2> result = new HashSet<>();

			final Set<ApplicationTerm> allStores = new ApplicationTermFinder("store", false)
					.findMatchingSubterms(inputTerm);

			for (final ApplicationTerm storeTerm : allStores) {

				final Term arrayTerm = storeTerm.getParameters()[0];
				final Term index = storeTerm.getParameters()[1];

				final Term arrayId = SmtUtils.getBasicArrayTerm(arrayTerm);

				/*
				 * @formatter:off
				 * Example:
				 * 1 (store a i1
				 * 2   (store (select a i1) i2
				 * 3      (store (select (select a i1) i2) i3 v)))
				 * Now say the current storeTerm is the one in line 3 and we want to know at which dimension a is
				 *  accessed by i3.
				 * We compute (dimensionality of a) - (dimensionality of store3) = 3 - 1 = 2 .
				 *  (so, by convention we count the access dimensions starting from 0)
				 * @formatter:on
				 */
				final int writtenDimension = new MultiDimensionalSort(arrayId.getSort()).getDimension()
						- new MultiDimensionalSort(storeTerm.getSort()).getDimension();

				final ArrayGroup arrayPvoc = termToArrayGroup.get(arrayId);
				if (arrayPvoc == null) {
					// array is not tracked: do not make a StoreInfo for it
					continue;
				}
//				assert arrayPvoc != null;

				result.add(new StoreInfo2(storeTerm, arrayPvoc, writtenDimension, index));
			}

			return result;
		}

		//	public IProgramVarOrConst getWrittenArray() {
		public ArrayGroup getWrittenArray() {
			return mWrittenArray;
		}


		public int getWrittenDimension() {
			return mWrittenDimension;
		}


		public Term getWriteIndex() {
			return mWriteIndex;
		}

		public Term getStoreTerm() {
			return mStoreTerm;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mWrittenArray == null) ? 0 : mWrittenArray.hashCode());
			result = prime * result + mWrittenDimension;
			result = prime * result + ((mWriteIndex == null) ? 0 : mWriteIndex.hashCode());
			return result;
		}


		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final StoreInfo2 other = (StoreInfo2) obj;
			if (mWrittenArray == null) {
				if (other.mWrittenArray != null) {
					return false;
				}
			} else if (!mWrittenArray.equals(other.mWrittenArray)) {
				return false;
			}
			if (mWrittenDimension != other.mWrittenDimension) {
				return false;
			}
			if (mWriteIndex == null) {
				if (other.mWriteIndex != null) {
					return false;
				}
			} else if (!mWriteIndex.equals(other.mWriteIndex)) {
				return false;
			}
			return true;
		}

	}
}