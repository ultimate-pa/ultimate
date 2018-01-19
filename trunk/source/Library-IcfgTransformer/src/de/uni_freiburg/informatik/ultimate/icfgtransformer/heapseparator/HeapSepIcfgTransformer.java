package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class HeapSepIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private IIcfg<OUTLOC> mResultIcfg;

	private final Preprocessing mPreprocessing = Preprocessing.FREEZE_VARIABLES;

	private ILogger mLogger;

	private final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> mEqualityProvider;

	private final HeapSeparatorBenchmark mStatistics;

	/**
	 * Default constructor.
	 *
	 * @param originalIcfg
	 *            an input {@link IIcfg}.
	 * @param funLocFac
	 *            A location factory.
	 * @param backtranslationTracker
	 *            A backtranslation tracker.
	 * @param outLocationClass
	 *            The class object of the type of locations of the output {@link IIcfg}.
	 * @param newIcfgIdentifier
	 *            The identifier of the new {@link IIcfg}
	 * @param statistics
	 * @param transformer
	 *            The transformer that should be applied to each transformula of each transition of the input
	 *            {@link IIcfg} to create a new {@link IIcfg}.
	 */
	public HeapSepIcfgTransformer(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final ReplacementVarFactory replacementVarFactory, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {
		mEqualityProvider = equalityProvider;
		mStatistics = new HeapSeparatorBenchmark();
		computeResult(originalIcfg, funLocFac, replacementVarFactory, backtranslationTracker, outLocationClass,
				newIcfgIdentifier);
	}

	/**
	 * Steps in the transformation:
	 * <ul>
	 *  <li> two options for preprocessing
	 *   <ol>
	 *    <li> execute the ArrayIndexExposer: transform the input Icfg into an Icfg with additional "freeze-variables"
	 *    <li> introduce the "memloc"-array
	 *   </ol>
	 *  <li> run the equality analysis (VPDomain/map equality domain) on the preprocessed Icfg
	 *  <li> compute an array partitioning according to the analysis result
	 *  <li> transform the input Icfg into an Icfg where the arrays have been split
	 * </ul>
	 *
	 * @param originalIcfg
	 * @param funLocFac
	 * @param replacementVarFactory
	 * @param backtranslationTracker
	 * @param outLocationClass
	 * @param newIcfgIdentifier
	 * @return
	 */
	private void computeResult(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final ReplacementVarFactory replacementVarFactory, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier) {


//		final CfgSmtToolkit oldCsToolkit = originalIcfg.getCfgSmtToolkit();
//		final IUltimateServiceProvider services;
		// TOOD
		final ILocationFactory<OUTLOC, OUTLOC> outToOutLocFac = null;

		// TODO : where do we get this variable from?
		final IProgramVar validArray = null;

//		final NestedMap2<Term, EdgeInfo, IProgramNonOldVar> writeIndexTermToTfInfoToFreezeVar;
		final Map<StoreIndexInfo, IProgramNonOldVar> arrayAccessInfoToFreezeVar;

		/*
		 * 1. Execute the preprocessing
		 */
		final IIcfg<OUTLOC> preprocessedIcfg;
		if (mPreprocessing == Preprocessing.FREEZE_VARIABLES) {
			/*
			 * add the freeze var updates to each transition with an array update
			 */
			final StoreIndexFreezerIcfgTransformer<INLOC, OUTLOC> sifit =
					new StoreIndexFreezerIcfgTransformer<>(mLogger, "icfg_with_uninitialized_freeze_vars",
							outLocationClass, originalIcfg, funLocFac, backtranslationTracker);
			final IIcfg<OUTLOC> icfgWFreezeVarsUninitialized = sifit.getResult();
//			writeIndexTermToTfInfoToFreezeVar = sifit.getWriteIndexToTfInfoToFreezeVar();
			arrayAccessInfoToFreezeVar = sifit.getArrayAccessInfoToFreezeVar();

			/*
			 * Create a fresh literal/constant for each freeze variable that was introduced, we call them freeze
			 * literals.
			 * Announce them to the equality analysis as special literals, which are, by axiom, pairwise disjoint.
			 */
			final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit = new HashMap<>();

//			for (final IProgramNonOldVar freezeVar : writeIndexTermToTfInfoToFreezeVar.values()
			for (final IProgramNonOldVar freezeVar : arrayAccessInfoToFreezeVar.values()) {
//					.collect(Collectors.toList())) {
				// FIXME: how to construct a fresh IProgramConst???
				freezeVarTofreezeVarLit.put(freezeVar,
						(IProgramConst) replacementVarFactory.getOrConstuctReplacementVar(null, false));
			}
			mEqualityProvider.announceAdditionalLiterals(freezeVarTofreezeVarLit.values());

			/*
			 * Add initialization code for each of the newly introduced freeze variables.
			 * Each freeze variable is initialized to its corresponding freeze literal.
			 * Furthermore the valid-array (of the memory model) is assumed to be 1 at each freeze literal.
			 */
			final FreezeVarInitializer<OUTLOC, OUTLOC> fvi = new FreezeVarInitializer<>(mLogger,
					"icfg_with_initialized_freeze_vars", outLocationClass, icfgWFreezeVarsUninitialized, outToOutLocFac,
					backtranslationTracker, freezeVarTofreezeVarLit, validArray);
			final IIcfg<OUTLOC> icfgWFreezeVarsInitialized = fvi.getResult();

			preprocessedIcfg = icfgWFreezeVarsInitialized;
		} else {
			assert mPreprocessing == Preprocessing.MEMLOC_ARRAY;
			// TODO implement..
			preprocessedIcfg = null;

//			writeIndexTermToTfInfoToFreezeVar = null;
			arrayAccessInfoToFreezeVar = null;
		}


		/*
		 * 2. run the equality analysis
		 */
		mEqualityProvider.preprocess(preprocessedIcfg);

		/*
		 * 3a. look up all locations where
		 *  <li> an array cell is accessed
		 *  <li> two arrays are related
		 */
		final HeapSepPreAnalysis heapSepPreanalysis = new HeapSepPreAnalysis(mLogger,
				originalIcfg.getCfgSmtToolkit().getManagedScript());
		new IcfgEdgeIterator(originalIcfg).forEachRemaining(edge -> heapSepPreanalysis.processEdge(edge));


		final Set<ArrayGroup> arrayGroups = heapSepPreanalysis.getArrayGroups();

		final PartitionManager partitionManager = new PartitionManager(arrayGroups, arrayAccessInfoToFreezeVar);

		/*
		 * 3b. compute an array partitioning
		 */
		final NewArrayIdProvider newArrayIdProvider;
		if (mPreprocessing == Preprocessing.FREEZE_VARIABLES) {

//			Map<ArrayGroup, UnionFind<StoreIndexInfo>>
//			UnionFind<StoreIndexInfo> partition = new UnionFind<>();


			for (final SelectInfo si : heapSepPreanalysis.getSelectInfos()) {
				partitionManager.processSelect(si, getEqualityProvidingState(si.getEdgeInfo()));
			}


			newArrayIdProvider = new NewArrayIdProvider(originalIcfg.getCfgSmtToolkit(),
//					mEqualityProvider, heapSepPreanalysis, writeIndexTermToTfInfoToFreezeVar, mStatistics);
					mEqualityProvider, heapSepPreanalysis, arrayAccessInfoToFreezeVar, mStatistics);
		} else {
			newArrayIdProvider = null;
		}

		/*
		 * 4. Execute the transformer that splits up the arrays according to the result from the equality analysis.
		 *  Note that this transformation is done on the original input Icfg, not on the output of the
		 *  ArrayIndexExposer, which we ran the equality analysis on.
		 */
//		final BasicIcfg<OUTLOC> resultIcfg =
//				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
//		final ITransformulaTransformer transformer = new HeapSepTransFormulaTransformer(originalIcfg.getCfgSmtToolkit(),
//				mLogger, newArrayIdProvider);
//		final TransformedIcfgBuilder<INLOC, OUTLOC> lst =
//				new TransformedIcfgBuilder<>(funLocFac, backtranslationTracker, transformer, originalIcfg, resultIcfg);
//		processLocations(originalIcfg.getInitialNodes(), lst);
//		lst.finish();
//		mResultIcfg = resultIcfg;
		final PartitionProjectionTransitionTransformer<INLOC, OUTLOC> heapSeparatingTransformer =
				new PartitionProjectionTransitionTransformer<>(mLogger, "HeapSeparatedIcfg", outLocationClass,
						originalIcfg, funLocFac, backtranslationTracker);
		mResultIcfg = heapSeparatingTransformer.getResult();
	}

	/**
	 * For the moment this will return the EqState of the source location of edgeInfo, but in order to be able to
	 *  deal with select indices that are aux vars, we need to have something different here TODO (the interface
	 *  IEqualityProvidingState can remain unchanged for this)
	 *
	 * @param edgeInfo
	 * @return
	 */
	private IEqualityProvidingState getEqualityProvidingState(final EdgeInfo edgeInfo) {
		// TODO Auto-generated method stub
		return null;
	}

//	private void processLocations(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {
//		final IcfgLocationIterator<INLOC> iter = new IcfgLocationIterator<>(init);
//
//		// we need to create new return transitions after new call transitions have been created
//		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();
//
//		while (iter.hasNext()) {
//			final INLOC oldSource = iter.next();
//			final OUTLOC newSource = lst.createNewLocation(oldSource);
//			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
//				@SuppressWarnings("unchecked")
//				final OUTLOC newTarget = lst.createNewLocation((INLOC) oldTransition.getTarget());
//				if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
//					rtrTransitions.add(new Triple<>(newSource, newTarget, oldTransition));
//				} else {
//					lst.createNewTransition(newSource, newTarget, oldTransition);
//				}
//			}
//		}
//
//		rtrTransitions.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
//	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}


	enum Preprocessing {
		FREEZE_VARIABLES, MEMLOC_ARRAY;
	}


	public String getHeapSeparationSummary() {
		// TODO Auto-generated method stub
		return null;
	}

	public HeapSeparatorBenchmark getStatistics() {
		return mStatistics;
	}
}

class PartitionManager {

	// input
	Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	// input
	Map<IProgramVar, StoreIndexInfo> mFreezeVarToStoreIndexInfo;

	// output
	Map<SelectInfo, LocationBlock> mSelectInfoToLocationBlock;

	Map<ArrayGroup, UnionFind<StoreIndexInfo>> mArrayGroupToStoreIndexInfoPartition;

//	Set<SelectInfo> mAllSelectInfos;

	/**
	 * maps a selectInfo to any one of the StoreIndexInfos that may be equal to the selectInfo
	 */
	Map<SelectInfo, StoreIndexInfo> mSelectInfoToToSampleStoreIndexInfo;

	public PartitionManager(final Set<ArrayGroup> arrayGroups,
			final Map<StoreIndexInfo, IProgramNonOldVar> arrayAccessInfoToFreezeVar) {

		mArrayToArrayGroup = new HashMap<>();
		for (final ArrayGroup ag : arrayGroups) {
			for (final IProgramVarOrConst a : ag.getArrays()) {
				mArrayToArrayGroup.put(a, ag);
			}
		}

		mFreezeVarToStoreIndexInfo = new HashMap<>();
		for (final Entry<StoreIndexInfo, IProgramNonOldVar> en : arrayAccessInfoToFreezeVar.entrySet()) {
			mFreezeVarToStoreIndexInfo.put(en.getValue(), en.getKey());
		}

		mArrayGroupToStoreIndexInfoPartition = new HashMap<>();
		mSelectInfoToLocationBlock = new HashMap<>();

		mSelectInfoToToSampleStoreIndexInfo = new HashMap<>();
	}

	void processSelect(final SelectInfo selectInfo, final IEqualityProvidingState eps) {

//		final Set<Term> mayEqualFreezeVars = new HashSet<>();
//		final Set<IProgramVar> mayEqualFreezeVars = new HashSet<>();
		final Set<StoreIndexInfo> mayEqualStoreIndexInfos = new HashSet<>();

		final Term selectIndex = selectInfo.getArrayCellAccess().getIndex();

		final IProgramVarOrConst selectArrayPvoc = selectInfo.getEdgeInfo()
				.getProgramVarOrConstForTerm(selectInfo.getArrayCellAccess().getArray());

		for (final Entry<IProgramVar, StoreIndexInfo> en : mFreezeVarToStoreIndexInfo.entrySet()) {
			final IProgramVar freezeVar = en.getKey();
			final StoreIndexInfo sii = en.getValue();

			if (eps.areUnequal(selectIndex, freezeVar.getTerm())) {
				// nothing to do
			} else {
				// select index and freezeVar may be equal at this location
//				mayEqualFreezeVars.add(freezeVar.getTerm());
//				mayEqualFreezeVars.add(freezeVar);
				mayEqualStoreIndexInfos.add(sii);
			}
		}


//		if (mayEqualFreezeVars.isEmpty()) {
//		if (mayEqualFreezeVars.size() <= 1) {
		if (mayEqualStoreIndexInfos.size() <= 1) {
			// nothing to do
		} else {
//			final IProgramVar sample = mayEqualFreezeVars.iterator().next();
			final StoreIndexInfo sample = mayEqualStoreIndexInfos.iterator().next();

			mSelectInfoToToSampleStoreIndexInfo.put(selectInfo, sample);

//			for (final IProgramVar mefv : mayEqualFreezeVars) {
			for (final StoreIndexInfo sii : mayEqualStoreIndexInfos) {
//				mergeBlocks(selectArrayPvoc, sii, sample);
				mergeBlocks(selectInfo, sii, sample);
			}

		}

		//		final EdgeInfo location = selectInfo.getEdgeInfo();
//		final IProgramVarOrConst array = location.getProgramVarOrConstForTerm(
//				selectInfo.getArrayCellAccess().getArray());
//		final ArrayGroup arrayGroup = mArrayToArrayGroup.get(array);

//		selectInfo.getArrayCellAccess().getIndex()
	}

	public void finish() {
//		for (final Entry<ArrayGroup, UnionFind<StoreIndexInfo>> en : mArrayGroupToStoreIndexInfoPartition.entrySet()) {
//			mSelectInfoToLocationBlock.put()
//		}

		/*
		 * rewrite the collected information into our output format
		 */
		for (final Entry<SelectInfo, StoreIndexInfo> en : mSelectInfoToToSampleStoreIndexInfo.entrySet()) {

			final StoreIndexInfo sampleSii = en.getValue();

			final SelectInfo selectInfo = en.getKey();
			final ArrayGroup arrayGroup = mArrayToArrayGroup.get(selectInfo.getArrayPvoc());
			final UnionFind<StoreIndexInfo> partition = mArrayGroupToStoreIndexInfoPartition.get(arrayGroup);

			final Set<StoreIndexInfo> eqc = partition.getEquivalenceClassMembers(sampleSii);

			mSelectInfoToLocationBlock.put(selectInfo, new LocationBlock(eqc, arrayGroup));
		}
	}

//	private void mergeBlocks(final IProgramVarOrConst array, final StoreIndexInfo sii1, final StoreIndexInfo sii2) {
	private void mergeBlocks(final SelectInfo selectInfo, final StoreIndexInfo sii1, final StoreIndexInfo sii2) {
		final IProgramVarOrConst array = selectInfo.getArrayPvoc();
		final ArrayGroup arrayGroup = mArrayToArrayGroup.get(array);

		UnionFind<StoreIndexInfo> partition = mArrayGroupToStoreIndexInfoPartition.get(arrayGroup);
		if (partition == null) {
			partition = new UnionFind<>();
			mArrayGroupToStoreIndexInfoPartition.put(arrayGroup, partition);
		}

		partition.findAndConstructEquivalenceClassIfNeeded(sii1);
		partition.findAndConstructEquivalenceClassIfNeeded(sii2);
		partition.union(sii1, sii2);

//		mSelectInfoToLocationBlock.put(selectInfo, value)
	}

	LocationBlock getLocationBlock(final SelectInfo selectInfo) {
		return mSelectInfoToLocationBlock.get(selectInfo);
	}
}
