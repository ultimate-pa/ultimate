package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingIntermediateState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

class HeapPartitionManager {

	// input
	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

//	// input
//	private final Map<IProgramVar, StoreIndexInfo> mFreezeVarToStoreIndexInfo;
	private final Map<StoreIndexInfo, IProgramNonOldVar> mStoreIndexInfoToFreezeVar;

	// output
	private final NestedMap2<SelectInfo, Integer, LocationBlock> mSelectInfoToDimensionToLocationBlock;

	private final NestedMap2<ArrayGroup, Integer, UnionFind<StoreIndexInfo>>
		mArrayGroupToDimensionToStoreIndexInfoPartition;

	/**
	 * maps a selectInfo to any one of the StoreIndexInfos that may be equal to the selectInfo
	 */
	NestedMap2<SelectInfo, Integer, StoreIndexInfo> mSelectInfoToDimensionToToSampleStoreIndexInfo;

	private boolean mIsFinished = false;

	private final List<IProgramVarOrConst> mHeapArrays;

	private final ILogger mLogger;

	/**
	 * map for caching/unifying LocationBlocks
	 */
	private final NestedMap3<Set<StoreIndexInfo>, ArrayGroup, Integer, LocationBlock>
		mStoreIndexInfosToArrayGroupToDimensionToLocationBlock;

	private final HeapSeparatorBenchmark mStatistics;

	private final Set<StoreIndexInfo> mStoreIndexInfos;

	private final Preprocessing mPreprocessing;

	private final ManagedScript mMgdScript;

//	private final TermVariable mMemLocArrayTv;

	private final Map<StoreIndexInfo, IProgramConst> mStoreIndexInfoToLocLiteral;

private final MemlocArrayManager mMemLocArrayManager;

	/**
	 * for freeze var style
	 * @param logger
	 * @param arrayToArrayGroup
	 * @param storeIndexInfoToFreezeVar
	 * @param heapArrays
	 * @param statistics
	 * @param mgdScript
	 */
	public HeapPartitionManager(final ILogger logger, final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup,
			final Map<StoreIndexInfo, IProgramNonOldVar> storeIndexInfoToFreezeVar,
			final List<IProgramVarOrConst> heapArrays, final HeapSeparatorBenchmark statistics,
			final ManagedScript mgdScript) {
		mLogger = logger;
		mMgdScript = mgdScript;
		mArrayToArrayGroup = arrayToArrayGroup;
		mStoreIndexInfos = storeIndexInfoToFreezeVar.keySet();
		mStoreIndexInfoToFreezeVar = storeIndexInfoToFreezeVar;
		mHeapArrays = heapArrays;
		mStatistics = statistics;
		mPreprocessing = Preprocessing.FREEZE_VARIABLES;

//		mMemLocArrayTv = null;
		mMemLocArrayManager = null;
		mStoreIndexInfoToLocLiteral = null;

		mArrayGroupToDimensionToStoreIndexInfoPartition = new NestedMap2<>();
		mSelectInfoToDimensionToLocationBlock = new NestedMap2<>();
		mSelectInfoToDimensionToToSampleStoreIndexInfo = new NestedMap2<>();
		mStoreIndexInfosToArrayGroupToDimensionToLocationBlock = new NestedMap3<>();
	}

	/**
	 * for memloc style
	 * @param logger
	 * @param arrayToArrayGroup
	 * @param storeIndexInfos
	 * @param heapArrays
	 * @param statistics
	 * @param memLocArray
	 * @param storeIndexInfoToLocLiteral
	 */
	public HeapPartitionManager(final ILogger logger, final ManagedScript mgdScript,
			final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup,
			final List<IProgramVarOrConst> heapArrays, final HeapSeparatorBenchmark statistics,
			final MemlocArrayManager memlocArrayManager,
			final Map<StoreIndexInfo, IProgramConst> storeIndexInfoToLocLiteral) {
		mPreprocessing = Preprocessing.MEMLOC_ARRAY;
		mMgdScript = mgdScript;

		mLogger = logger;
		mArrayToArrayGroup = arrayToArrayGroup;
		mStoreIndexInfos = storeIndexInfoToLocLiteral.keySet();
		mHeapArrays = heapArrays;
		mStatistics = statistics;
//		mMemLocArrayTv = memLocArray.getTermVariable();
		mMemLocArrayManager = memlocArrayManager;
		mStoreIndexInfoToLocLiteral = storeIndexInfoToLocLiteral;

		mStoreIndexInfoToFreezeVar = null;


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
		final HashRelation<Integer, StoreIndexInfo> dimensionToMayEqualStoreIndexInfos = new HashRelation<>();

		final ArrayIndex selectIndex = selectInfo.getIndex();

		for (final StoreIndexInfo sii : mStoreIndexInfos) {

			final IProgramVar freezeVar;
			final IProgramConst locLit;
			if (mPreprocessing == Preprocessing.FREEZE_VARIABLES) {
				freezeVar = mStoreIndexInfoToFreezeVar.get(sii);
				locLit = null;
			} else {
				freezeVar = null;
				locLit = mStoreIndexInfoToLocLiteral.get(sii);
			}

			if (!sii.getArrays().contains(mArrayToArrayGroup.get(selectInfo.getArrayPvoc()))) {
				// arrays don't match (coarse check failed..)
				continue;
			}

			// EDIT: this is a hack, commented it
//			if (selectInfo.getArrayPvoc() instanceof IProgramNonOldVar &&
//					eps.areEqual(selectInfo.getArrayPvoc().getTerm(),
//							((IProgramNonOldVar) selectInfo.getArrayPvoc()).getOldVar().getTerm())) {
//				/* the array that is read at the current select is in its uninitialized state -- the current
//				 *  storeIndexInfo (or any other for that matter) does not influence the select, thus cannot trigger
//				 *  a merge of heap partitions.
//				 */
//				continue;
//			}

			for (int dim = 0; dim < selectIndex.size(); dim++) {

				if (!sii.getArrayToAccessDimensions()
						.containsPair(mArrayToArrayGroup.get(selectInfo.getArrayPvoc()), dim)) {
					/*
					 * not the right base-array/dimension combination --> continue
					 *  (more detailed: the array write(s) that the storeIndexInfo represents are not to the array that
					 *   the SelectInfo reads or not to the current dimension dim that the current element of the
					 *   SelectInfo's index tuple refers to)
					 */
					continue;
				}
				final Term selectIndexNormalized = selectInfo.getNormalizedArrayIndex(dim);

				if (mPreprocessing == Preprocessing.FREEZE_VARIABLES) {
					if (eps.areUnequal(selectIndexNormalized, freezeVar.getTerm())) {
						// nothing to do
					} else {
						// select index and freezeVar may be equal at this location
						dimensionToMayEqualStoreIndexInfos.addPair(dim, sii);
					}
				} else {
					// aliasing question to ask: memloc[selectIndex] (mayequal) locLiteral_sii
					final Term memlocSelect = SmtUtils.select(mMgdScript.getScript(),
							mMemLocArrayManager.getMemlocArray(dim).getTermVariable(),
							selectIndexNormalized);
					if (eps.areUnequal(memlocSelect, locLit.getTerm())) {
						// nothing to do
					} else {
						dimensionToMayEqualStoreIndexInfos.addPair(dim, sii);
					}
				}
			}
		}


		for (int dim = 0; dim < selectIndex.size(); dim++) {
			final Set<StoreIndexInfo> mayEqualStoreIndexInfos = dimensionToMayEqualStoreIndexInfos.getImage(dim);


			if (mayEqualStoreIndexInfos.size() == 0) {
				/* there is no array write/StoreIndexInfo that has a data flow to this array read/SelectInfo
				 *  --> this is a special case, we can replace the array that is read here with an uninitialized array
				 *    of the correct sort
				 */
				final NoStoreIndexInfo nsii = new NoStoreIndexInfo();
				createPartitionAndBlockIfNecessary(selectInfo, dim, nsii);
				mSelectInfoToDimensionToToSampleStoreIndexInfo.put(selectInfo, dim, nsii);
				continue;
			}

			final StoreIndexInfo sample = mayEqualStoreIndexInfos.iterator().next();

			mSelectInfoToDimensionToToSampleStoreIndexInfo.put(selectInfo, dim, sample);

			createPartitionAndBlockIfNecessary(selectInfo, dim, sample);

			for (final StoreIndexInfo sii : mayEqualStoreIndexInfos) {
				if (sii == sample) {
					// no need to merge sii with itself
					continue;
				}
//				mLogger.debug("merging partition blocks for array " + selectInfo.getArrayPvoc() + " :");
				mLogger.debug("merging partition blocks for array group" +
							mArrayToArrayGroup.get(selectInfo.getArrayPvoc()) + " :");
				mLogger.debug("\t" + sii);
				mLogger.debug("\t and");
				mLogger.debug("\t" + sample);
				mLogger.debug("\t because of possible aliasing at dimension " + dim);
				mLogger.debug("\t at array read " + selectInfo + ".");
				mergeBlocks(selectInfo, dim, sii, sample);
			}
//			}
		}
	}

	private void createPartitionAndBlockIfNecessary(final SelectInfo selectInfo, final int dim, final StoreIndexInfo sample) {
		final IProgramVarOrConst array = selectInfo.getArrayPvoc();
		final ArrayGroup arrayGroup = mArrayToArrayGroup.get(array);

		UnionFind<StoreIndexInfo> partition = mArrayGroupToDimensionToStoreIndexInfoPartition.get(arrayGroup, dim);
		if (partition == null) {
			partition = new UnionFind<>();
			mArrayGroupToDimensionToStoreIndexInfoPartition.put(arrayGroup, dim, partition);
		}
		partition.findAndConstructEquivalenceClassIfNeeded(sample);
	}

	private void mergeBlocks(final SelectInfo selectInfo, final int dim, final StoreIndexInfo sii1,
			final StoreIndexInfo sii2) {
		final IProgramVarOrConst array = selectInfo.getArrayPvoc();
		final ArrayGroup arrayGroup = mArrayToArrayGroup.get(array);

		final UnionFind<StoreIndexInfo> partition = mArrayGroupToDimensionToStoreIndexInfoPartition.get(arrayGroup, dim);
		if (partition == null) {
			throw new AssertionError("should have been created in createBlockIfNecessary");
		}

		partition.findAndConstructEquivalenceClassIfNeeded(sii1);
		partition.findAndConstructEquivalenceClassIfNeeded(sii2);
		partition.union(sii1, sii2);
	}

	public void finish() {

		/*
		 * rewrite the collected information into our output format
		 */
		for (final Triple<SelectInfo, Integer, StoreIndexInfo> en :
				mSelectInfoToDimensionToToSampleStoreIndexInfo.entrySet()) {

			final StoreIndexInfo sampleSii = en.getThird();

			final SelectInfo selectInfo = en.getFirst();
			final Integer dim = en.getSecond();

			final ArrayGroup arrayGroup = mArrayToArrayGroup.get(selectInfo.getArrayPvoc());

			final UnionFind<StoreIndexInfo> partition =
					mArrayGroupToDimensionToStoreIndexInfoPartition.get(arrayGroup, dim);
			final Set<StoreIndexInfo> eqc = partition.getEquivalenceClassMembers(sampleSii);

			final LocationBlock locationBlock = getOrConstructLocationBlock(eqc, arrayGroup, dim);
			mSelectInfoToDimensionToLocationBlock.put(selectInfo, dim, locationBlock);
			mLogger.debug("adding LocationBlock " + locationBlock);
			mLogger.debug("\t at dimension " + dim + " for " + selectInfo);
			mLogger.debug("\t write locations: " + locationBlock.getLocations());

		}


		mLogger.info("partitioning result:");
		for (final ArrayGroup arrayGroup : mArrayToArrayGroup.values()) {

			mStatistics.registerArrayGroup(arrayGroup);

			mLogger.info("\t location blocks for array group " + arrayGroup);

			for (int dim = 0; dim < arrayGroup.getDimensionality(); dim++) {
				final UnionFind<StoreIndexInfo> partition =
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
					for (final Set<StoreIndexInfo> eqc : partition.getAllEquivalenceClasses()) {
						mLogger.debug("\t\t " + eqc);
					}
				}
			}
		}

		mIsFinished = true;
		assert sanityCheck();
	}

	private LocationBlock getOrConstructLocationBlock(final Set<StoreIndexInfo> eqc, final ArrayGroup arrayGroup,
			final Integer dim) {
		LocationBlock result = mStoreIndexInfosToArrayGroupToDimensionToLocationBlock.get(eqc, arrayGroup, dim);
		if (result == null) {
			result = new LocationBlock(eqc, arrayGroup, dim);
			mStoreIndexInfosToArrayGroupToDimensionToLocationBlock.put(eqc, arrayGroup, dim, result);

			mLogger.debug("creating LocationBlock " + result);
			mLogger.debug("\t with contents " + result.getLocations());

		}
		return result;
	}

	private boolean assertWritesAreToReadArray(final Set<StoreIndexInfo> eqc, final SelectInfo selectInfo) {
		for (final StoreIndexInfo sii : eqc) {
			if (sii instanceof NoStoreIndexInfo) {
				continue;
			}
			if (!sii.getArrays().contains(mArrayToArrayGroup.get(selectInfo.getArrayPvoc()))) {
				assert false;
				return false;
			}
		}
		return true;
	}

	private boolean sanityCheck() {
		/*
		 * each location block in the image of a selectInfo must only contain StoreIndexInfos that refer to the same
		 *  array
		 * (a write cannot influence a read if it is to a different array)
		 */
		for (final Triple<SelectInfo, Integer, LocationBlock> en : mSelectInfoToDimensionToLocationBlock.entrySet()) {
			assert assertWritesAreToReadArray(en.getThird().getLocations(), en.getFirst());

			if (!en.getSecond().equals(en.getThird().getDimension())) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public NestedMap2<SelectInfo, Integer, LocationBlock> getSelectInfoToDimensionToLocationBlock() {
		if (!mIsFinished) {
			throw new AssertionError();
		}
		return mSelectInfoToDimensionToLocationBlock;
	}

	public LocationBlock getLocationBlock(final SelectInfo si, final Integer dim) {
		if (!mIsFinished) {
			throw new AssertionError();
		}
		return mSelectInfoToDimensionToLocationBlock.get(si, dim);
	}
}