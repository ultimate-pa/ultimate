package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.ComputeStoreIndexInfosAndArrayGroups.StoreInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityAllowStores;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreIndexInfo;
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
class ComputeStoreIndexInfosAndArrayGroups<LOC extends IcfgLocation> {

	final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo = new NestedMap2<>();
	final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup = new HashMap<>();

	private int mStoreIndexInfoCounter;

	public ComputeStoreIndexInfosAndArrayGroups(final IIcfg<LOC> icfg, final List<IProgramVarOrConst> heapArrays) {

		final UnionFind<IProgramVarOrConst> globalArrayPartition = new UnionFind<>();
		// base line for the array groups: the heap arrays
		heapArrays.forEach(globalArrayPartition::findAndConstructEquivalenceClassIfNeeded);

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

				final List<ArrayEqualityAllowStores> aeass =
						ArrayEqualityAllowStores.extractArrayEqualityAllowStores(tf.getFormula());
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
			for (final Entry<EdgeInfo, UnionFind<Term>> en : edgeToPerEdgeArrayPartition.entrySet()) {
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
				 * construct the StoreIndexInfos
				 */
				for (final StoreInfo store : StoreInfo.extractStores(tf.getFormula(), arrayTermToArrayGroup)) {

					if (DataStructureUtils.intersection(new HashSet<>(heapArrays), store.getWrittenArray().getArrays())
							.isEmpty()) {
						/* we are only interested in writes to heap arrays */
						continue;
					}

					final StoreIndexInfo storeIndexInfo = getOrConstructStoreIndexInfo(edgeInfo, store.getWriteIndex());
					storeIndexInfo.addArrayAccessDimension(store.getWrittenArray(), store.getWrittenDimension());
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

	public NestedMap2<EdgeInfo, Term, StoreIndexInfo> getEdgeToIndexToStoreIndexInfo() {
		return mEdgeToIndexToStoreIndexInfo;
	}

	public Map<IProgramVarOrConst, ArrayGroup> getArrayToArrayGroup() {
		return Collections.unmodifiableMap(mArrayToArrayGroup);
	}

	/**
	 * updates mEdgeToIndexToStoreIndexInfo
	 *
	 * @param tfInfo
	 * @param indexTerm
	 * @return
	 */
	private StoreIndexInfo getOrConstructStoreIndexInfo(final EdgeInfo tfInfo, final Term indexTerm) {
		StoreIndexInfo sii = mEdgeToIndexToStoreIndexInfo.get(tfInfo, indexTerm);
		if (sii == null) {
			sii = new StoreIndexInfo(tfInfo, indexTerm, mStoreIndexInfoCounter++);
			mEdgeToIndexToStoreIndexInfo.put(tfInfo, indexTerm, sii);
		}
		return sii;
	}


	static class StoreInfo {

		//	private final IProgramVarOrConst mWrittenArray;
		private final ArrayGroup mWrittenArray;
		private final int mWrittenDimension;
		private final Term writeIndex;

		//	public StoreInfo(final IProgramVarOrConst writtenArray, final int writtenDimension, final Term writeIndex) {
		public StoreInfo(final ArrayGroup writtenArray, final int writtenDimension, final Term writeIndex) {
			super();
			mWrittenArray = writtenArray;
			mWrittenDimension = writtenDimension;
			this.writeIndex = writeIndex;
		}


		//	public static Set<StoreInfo> extractStores(final Term inputTerm, final TransFormula tf) {
		public static Set<StoreInfo> extractStores(final Term inputTerm, final Map<Term, ArrayGroup> termToArrayGroup) {
			final Set<StoreInfo> result = new HashSet<>();

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

				result.add(new StoreInfo(arrayPvoc, writtenDimension, index));
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
			return writeIndex;
		}


		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mWrittenArray == null) ? 0 : mWrittenArray.hashCode());
			result = prime * result + mWrittenDimension;
			result = prime * result + ((writeIndex == null) ? 0 : writeIndex.hashCode());
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
			final StoreInfo other = (StoreInfo) obj;
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
			if (writeIndex == null) {
				if (other.writeIndex != null) {
					return false;
				}
			} else if (!writeIndex.equals(other.writeIndex)) {
				return false;
			}
			return true;
		}

	}
}