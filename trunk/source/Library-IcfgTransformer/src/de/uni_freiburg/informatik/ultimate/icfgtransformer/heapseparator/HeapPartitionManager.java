/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreLocationBlock;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingIntermediateState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.NoStoreInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SelectInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class HeapPartitionManager {

	// output
	private final NestedMap2<SelectInfo, Integer, StoreLocationBlock> mSelectInfoToDimensionToLocationBlock;

	private final NestedMap2<ArrayGroup, Integer, UnionFind<StoreInfo>>
		mArrayGroupToDimensionToStoreIndexInfoPartition;

	/**
	 * maps a selectInfo to any one of the StoreIndexInfos that may be equal to the selectInfo
	 */
	NestedMap2<SelectInfo, Integer, StoreInfo> mSelectInfoToDimensionToToSampleStoreIndexInfo;

	private boolean mIsFinished = false;

	private final List<IProgramVarOrConst> mHeapArrays;

	private final ILogger mLogger;

	/**
	 * map for caching/unifying LocationBlocks
	 */
	private final NestedMap3<Set<StoreInfo>, ArrayGroup, Integer, StoreLocationBlock>
		mStoreIndexInfosToArrayGroupToDimensionToLocationBlock;

	private final HeapSeparatorBenchmark mStatistics;

	private final ManagedScript mMgdScript;

	private final MemlocArrayManager mMemLocArrayManager;

private final ComputeStoreInfosAndArrayGroups<?> mCsiaag;

	/**
	 * for memloc style
	 * @param logger
	 * @param arrayToArrayGroup
	 * @param storeIndexInfos
	 * @param heapArrays
	 * @param statistics
	 * @param memLocArray
	 * @param locLitToStoreInfo
	 */
	public HeapPartitionManager(final ILogger logger, final ManagedScript mgdScript,
			final List<IProgramVarOrConst> heapArrays, final HeapSeparatorBenchmark statistics,
			final MemlocArrayManager memlocArrayManager,
			final ComputeStoreInfosAndArrayGroups<?> csiaag) {
		mMgdScript = mgdScript;

		mLogger = logger;
		mHeapArrays = heapArrays;
		mStatistics = statistics;
		mMemLocArrayManager = memlocArrayManager;

		mCsiaag = csiaag;

		mArrayGroupToDimensionToStoreIndexInfoPartition = new NestedMap2<>();
		mSelectInfoToDimensionToLocationBlock = new NestedMap2<>();
		mSelectInfoToDimensionToToSampleStoreIndexInfo = new NestedMap2<>();
		mStoreIndexInfosToArrayGroupToDimensionToLocationBlock = new NestedMap3<>();
	}

	/**
	 * Merge all LocationBlocks (sets of StoreIndexInfos) that
	 *  <li> may write to the same array as the given SelectInfo reads from
	 *  <li> whose freezeVar may equal the SelectInfo's index at the SelectInfo's location (according to our equality
	 * 		 analysis)
	 *
	 * @param selectInfo
	 * @param eps
	 * @param preprocessing
	 */
	void processSelect(final SelectInfo selectInfo, final IEqualityProvidingIntermediateState eps) {

		if (eps.isBottom()) {
			mLogger.warn("equality analysis on preprocessed graph computed array read to be unreachable: "
					+ selectInfo);
		}

		final ArrayIndex selectIndex = selectInfo.getIndex();

		// say a is the base array, i the indexvector
		for (int dim = 1; dim <= selectIndex.size(); dim++) {
			// i_dim is the index prefix up to the current dimension
			final ArrayIndex indexForCurrentDim = selectIndex.getFirst(dim);

			final LocArrayInfo locArray = mMemLocArrayManager.getOrConstructLocArray(selectInfo.getEdgeInfo(),
					selectInfo.getArrayCellAccess().getArray(), dim, true);

			// build the term a-loc-dim[i_dim]
			mMgdScript.lock(this);
			final Term locArraySelect =
					SmtUtils.multiDimensionalSelect(mMgdScript.getScript(), locArray.getTerm(), indexForCurrentDim);
			mMgdScript.unlock(this);

			// obtain the analysis result for a-loc-dim[i_dim]
			final Set<Term> setConstraint = eps.getSetConstraintForExpression(locArraySelect);

			if (setConstraint == null) {
				/* analysis found no constraint --> having to merge all (this may be ok, in the sense that there still
				 * may be separation, in particular if it happens in a dimension > 1)
				 */
				mLogger.warn("No literal set constraint found for loc-array access " + locArraySelect + " at "
						+ locArray.getEdge());
				final List<StoreInfo> allStoreInfos = mCsiaag.getStoreInfosForDimensionAndArrayGroup(dim,
						selectInfo.getArrayGroup());
				mergeBlocks(selectInfo, dim, allStoreInfos);
			} else {
				final List<StoreInfo> setConstraintAsStoreInfos =
						setConstraint.stream().map(t -> mCsiaag.getStoreInfoForLocLitTerm(t))
							.collect(Collectors.toList());
				mergeBlocks(selectInfo, dim, setConstraintAsStoreInfos);
			}
		}
	}

	private void mergeBlocks(final SelectInfo selectInfo, final int dim,
			final List<StoreInfo> setConstraintAsStoreInfos) {
		assert setConstraintAsStoreInfos != null && !setConstraintAsStoreInfos.isEmpty();

		final ArrayGroup arrayGroup = selectInfo.getArrayGroup();

		createPartitionAndBlockIfNecessary(selectInfo, dim, setConstraintAsStoreInfos.iterator().next());

		final UnionFind<StoreInfo> partition = mArrayGroupToDimensionToStoreIndexInfoPartition.get(arrayGroup, dim);
		if (partition == null) {
			throw new AssertionError("should have been created in createBlockIfNecessary");
		}

		partition.findAndConstructEquivalenceClassIfNeeded(setConstraintAsStoreInfos.get(0));
		for (int i = 1; i < setConstraintAsStoreInfos.size(); i++) {
			final StoreInfo si1 = setConstraintAsStoreInfos.get(i - 1);
			final StoreInfo si2 = setConstraintAsStoreInfos.get(i);
			partition.findAndConstructEquivalenceClassIfNeeded(si2);
			if (si1 instanceof NoStoreInfo || si2 instanceof NoStoreInfo) {
				// partition intersection on "uninitialized/havoc array writes" does not trigger a merge
				continue;
			}
			partition.union(si1, si2);
		}
	}

	private void createPartitionAndBlockIfNecessary(final SelectInfo selectInfo, final int dim, final StoreInfo sample) {
		final ArrayGroup arrayGroup = selectInfo.getArrayGroup();//mArrayToArrayGroup.get(array);
		assert selectInfo.getArrayGroup().equals(sample.getArrayGroup()) || sample instanceof NoStoreInfo;

		UnionFind<StoreInfo> partition = mArrayGroupToDimensionToStoreIndexInfoPartition.get(arrayGroup, dim);
		if (partition == null) {
			partition = new UnionFind<>();
			mArrayGroupToDimensionToStoreIndexInfoPartition.put(arrayGroup, dim, partition);
		}
		mSelectInfoToDimensionToToSampleStoreIndexInfo.put(selectInfo, dim, sample);
		partition.findAndConstructEquivalenceClassIfNeeded(sample);
	}

	public void finish() {
		/*
		 * rewrite the collected information into our output format
		 */
		for (final Triple<SelectInfo, Integer, StoreInfo> en :
				mSelectInfoToDimensionToToSampleStoreIndexInfo.entrySet()) {

			final StoreInfo sampleSii = en.getThird();

			final SelectInfo selectInfo = en.getFirst();
			final Integer dim = en.getSecond();

			final ArrayGroup arrayGroup = selectInfo.getArrayGroup();

			final UnionFind<StoreInfo> partition =
					mArrayGroupToDimensionToStoreIndexInfoPartition.get(arrayGroup, dim);
			final Set<StoreInfo> eqc = partition.getEquivalenceClassMembers(sampleSii);

			final StoreLocationBlock locationBlock = getOrConstructLocationBlock(eqc, arrayGroup, dim);
			mSelectInfoToDimensionToLocationBlock.put(selectInfo, dim, locationBlock);
			mLogger.debug("adding LocationBlock " + locationBlock);
			mLogger.debug("\t at dimension " + dim + " for " + selectInfo);
			mLogger.debug("\t write locations: " + locationBlock.getLocations());

		}


		mLogger.info("partitioning result:");
		for (final ArrayGroup arrayGroup : mCsiaag.getArrayGroups()) {

			mStatistics.registerArrayGroup(arrayGroup);

			mLogger.info("\t location blocks for array group " + arrayGroup);

			for (int dim = 1; dim <= arrayGroup.getDimensionality(); dim++) {
				final UnionFind<StoreInfo> partition =
						mArrayGroupToDimensionToStoreIndexInfoPartition.get(arrayGroup, dim);
				final int noWrites = partition == null ? 0 : partition.getAllElements().size();

				final int noBlocks = partition == null ? 0 : partition.getAllEquivalenceClasses().size();

				mLogger.info("\t at dimension " + dim);
				mLogger.info("\t # array writes (possibly including 1 dummy write/NoStoreIndexInfo) : " + noWrites);
				mLogger.info("\t # location blocks :" + noBlocks);

				mStatistics.registerPerArrayAndDimensionInfo(arrayGroup, dim,
						HeapSeparatorStatistics.COUNT_ARRAY_WRITES, noWrites);
				mStatistics.registerPerArrayAndDimensionInfo(arrayGroup, dim,
						HeapSeparatorStatistics.COUNT_BLOCKS, noBlocks);

				mLogger.debug("\t location block contents:");
				if (mLogger.isDebugEnabled() && partition != null) {
					for (final Set<StoreInfo> eqc : partition.getAllEquivalenceClasses()) {
						mLogger.debug("\t\t " + eqc);
					}
				}
			}
		}

		mIsFinished = true;
		assert sanityCheck();
	}

	private StoreLocationBlock getOrConstructLocationBlock(final Set<StoreInfo> eqc, final ArrayGroup arrayGroup,
			final Integer dim) {
		StoreLocationBlock result = mStoreIndexInfosToArrayGroupToDimensionToLocationBlock.get(eqc, arrayGroup, dim);
		if (result == null) {
			result = new StoreLocationBlock(eqc, arrayGroup, dim);
			mStoreIndexInfosToArrayGroupToDimensionToLocationBlock.put(eqc, arrayGroup, dim, result);

			mLogger.debug("creating LocationBlock " + result);
			mLogger.debug("\t with contents " + result.getLocations());

		}
		return result;
	}


	private boolean sanityCheck() {
		// nothing here, yet
		return true;
	}

	public NestedMap2<SelectInfo, Integer, StoreLocationBlock> getSelectInfoToDimensionToLocationBlock() {
		if (!mIsFinished) {
			throw new AssertionError();
		}
		return mSelectInfoToDimensionToLocationBlock;
	}

	public StoreLocationBlock getLocationBlock(final SelectInfo si, final Integer dim) {
		if (!mIsFinished) {
			throw new AssertionError();
		}
		return mSelectInfoToDimensionToLocationBlock.get(si, dim);
	}
}