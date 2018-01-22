package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingIntermediateState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class HeapSepIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private IIcfg<OUTLOC> mResultIcfg;

	private final Preprocessing mPreprocessing = Preprocessing.FREEZE_VARIABLES;

	private final ILogger mLogger;

//	private final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> mEqualityProvider;

	private final HeapSeparatorBenchmark mStatistics;

	private final ManagedScript mManagedScript;

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
	 * @param validArray
	 * @param statistics
	 * @param transformer
	 *            The transformer that should be applied to each transformula of each transition of the input
	 *            {@link IIcfg} to create a new {@link IIcfg}.
	 */
	public HeapSepIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final ReplacementVarFactory replacementVarFactory, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final IProgramNonOldVar validArray) {
		assert logger != null;
		mStatistics = new HeapSeparatorBenchmark();
		mManagedScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mLogger = logger;

		computeResult(originalIcfg, funLocFac, replacementVarFactory, backtranslationTracker, outLocationClass,
				newIcfgIdentifier, equalityProvider, validArray);
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
	 * @param equalityProvider
	 * @param validArray
	 * @return
	 */
	private void computeResult(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final ReplacementVarFactory replacementVarFactory, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final IProgramNonOldVar validArray) {


		final ILocationFactory<OUTLOC, OUTLOC> outToOutLocFac =
				(ILocationFactory<OUTLOC, OUTLOC>) createIcfgLocationToIcfgLocationFactory();

		// TODO : where do we get this variable from?
//		final IProgramVar validArray = originalIcfg.getCfgSmtToolkit().getSymbolTable().getProgramVar(
//		final IProgramVar validArray = originalIcfg.getCfgSmtToolkit().getSymbolTable().getProgramVar(
//				mManagedScript.variable(validArrayName, null));

		/*
		 * 1. Execute the preprocessing
		 */
		final IIcfg<OUTLOC> preprocessedIcfg;
		final Map<StoreIndexInfo, IProgramNonOldVar> storeIndexInfoToFreezeVar;
		if (mPreprocessing == Preprocessing.FREEZE_VARIABLES) {
			/*
			 * add the freeze var updates to each transition with an array update
			 */
			final StoreIndexFreezerIcfgTransformer<INLOC, OUTLOC> sifit =
					new StoreIndexFreezerIcfgTransformer<>(mLogger, "icfg_with_uninitialized_freeze_vars",
							outLocationClass, originalIcfg, funLocFac, backtranslationTracker);
			final IIcfg<OUTLOC> icfgWFreezeVarsUninitialized = sifit.getResult();

			storeIndexInfoToFreezeVar = sifit.getArrayAccessInfoToFreezeVar();

			/*
			 * Create a fresh literal/constant for each freeze variable that was introduced, we call them freeze
			 * literals.
			 * Announce them to the equality analysis as special literals, which are, by axiom, pairwise disjoint.
			 */
			final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit = new HashMap<>();

			mManagedScript.lock(this);
			for (final IProgramNonOldVar freezeVar : storeIndexInfoToFreezeVar.values()) {

				final String freezeVarLitName = getFreezeVarLitName(freezeVar);
				mManagedScript.declareFun(this, freezeVarLitName, new Sort[0], freezeVar.getSort());
				final ApplicationTerm freezeVarLitTerm = (ApplicationTerm) mManagedScript.term(this, freezeVarLitName);

				freezeVarTofreezeVarLit.put(freezeVar, new HeapSepProgramConst(freezeVarLitTerm));
//						(IProgramConst) replacementVarFactory.getOrConstuctReplacementVar(null, false));
			}
			mManagedScript.unlock(this);
			equalityProvider.announceAdditionalLiterals(freezeVarTofreezeVarLit.values());

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
			storeIndexInfoToFreezeVar = null;
		}

		/*
		 * 2. run the equality analysis
		 */
		equalityProvider.preprocess(preprocessedIcfg);

		/*
		 * 3a. look up all locations where
		 *  <li> an array cell is accessed
		 *  <li> two arrays are related
		 */
		final HeapSepPreAnalysis heapSepPreanalysis = new HeapSepPreAnalysis(mLogger, mManagedScript);
		new IcfgEdgeIterator(originalIcfg).forEachRemaining(edge -> heapSepPreanalysis.processEdge(edge));
		heapSepPreanalysis.finish();
		final Set<ArrayGroup> arrayGroups = heapSepPreanalysis.getArrayGroups();

		final PartitionManager partitionManager = new PartitionManager(arrayGroups, storeIndexInfoToFreezeVar);

		/*
		 * 3b. compute an array partitioning
		 */
		if (mPreprocessing == Preprocessing.FREEZE_VARIABLES) {
			for (final SelectInfo si : heapSepPreanalysis.getSelectInfos()) {
				partitionManager.processSelect(si, getEqualityProvidingIntermediateState(si.getEdgeInfo(),
						equalityProvider));
			}
			partitionManager.finish();
		} else {
			// TODO
			assert false;
		}

		/*
		 * 4. Execute the transformer that splits up the arrays according to the result from the equality analysis.
		 *  Note that this transformation is done on the original input Icfg, not on the output of the
		 *  ArrayIndexExposer, which we ran the equality analysis on.
		 */
		final PartitionProjectionTransitionTransformer<INLOC, OUTLOC> heapSeparatingTransformer =
				new PartitionProjectionTransitionTransformer<>(mLogger, "HeapSeparatedIcfg", outLocationClass,
						originalIcfg, funLocFac, backtranslationTracker,
						partitionManager.getSelectInfoToLocationBlock());
		mResultIcfg = heapSeparatingTransformer.getResult();
	}

	private String getFreezeVarLitName(final IProgramNonOldVar freezeVar) {
		// TODO make _really_ sure that the new id is unique
		return freezeVar.getGloballyUniqueId() + "_lit";
	}

	/**
	 * For the moment this will return the EqState of the source location of edgeInfo, but in order to be able to
	 *  deal with select indices that are aux vars, we need to have something different here
	 * @param edgeInfo
	 * @param equalityProvider
	 * @return
	 */
	private IEqualityProvidingIntermediateState getEqualityProvidingIntermediateState(final EdgeInfo edgeInfo,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {
		return equalityProvider.getEqualityProvidingIntermediateState(edgeInfo.getEdge());
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}


	enum Preprocessing {
		FREEZE_VARIABLES, MEMLOC_ARRAY;
	}


//	public String getHeapSeparationSummary() {
//		return null;
//	}

	public HeapSeparatorBenchmark getStatistics() {
		return mStatistics;
	}

	/**
	 * (almost) a copy from IcfgTranformationObserver
	 *  --> should probably replace this with a less ad-hoc solution some time
	 *
	 * @return
	 */
//	private static ILocationFactory<IcfgLocation, IcfgLocation> createIcfgLocationToIcfgLocationFactory() {
	private static ILocationFactory<BoogieIcfgLocation, BoogieIcfgLocation> createIcfgLocationToIcfgLocationFactory() {
		return (oldLocation, debugIdentifier, procedure) -> {
				final BoogieIcfgLocation rtr = new BoogieIcfgLocation(debugIdentifier, procedure,
					oldLocation.isErrorLocation(), oldLocation.getBoogieASTNode());
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};

//		return (oldLocation, debugIdentifier, procedure) -> {
//			final IcfgLocation rtr = new IcfgLocation(debugIdentifier, procedure);
//			ModelUtils.copyAnnotations(oldLocation, rtr);
//			return rtr;
//		};
	}


//		private static ILocationFactory<BoogieIcfgLocation, BoogieIcfgLocation> createBoogieLocationFactory() {
//		return (oldLocation, debugIdentifier, procedure) -> {
//			final BoogieIcfgLocation rtr = new BoogieIcfgLocation(debugIdentifier, procedure,
//					oldLocation.isErrorLocation(), oldLocation.getBoogieASTNode());
//			ModelUtils.copyAnnotations(oldLocation, rtr);
//			return rtr;
//		};
//	}
//
//	private static <INLOC extends IcfgLocation> ILocationFactory<INLOC, IcfgLocation> createIcfgLocationFactory() {
//		return (oldLocation, debugIdentifier, procedure) -> {
//			final IcfgLocation rtr = new IcfgLocation(debugIdentifier, procedure);
//			ModelUtils.copyAnnotations(oldLocation, rtr);
//			return rtr;
//		};
//	}
}

class PartitionManager {

	// input
	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	// input
	private final Map<IProgramVar, StoreIndexInfo> mFreezeVarToStoreIndexInfo;

	// output
	private final Map<SelectInfo, LocationBlock> mSelectInfoToLocationBlock;

	private final Map<ArrayGroup, UnionFind<StoreIndexInfo>> mArrayGroupToStoreIndexInfoPartition;

	/**
	 * maps a selectInfo to any one of the StoreIndexInfos that may be equal to the selectInfo
	 */
	Map<SelectInfo, StoreIndexInfo> mSelectInfoToToSampleStoreIndexInfo;

	private boolean mIsFinished = false;

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

	void processSelect(final SelectInfo selectInfo, final IEqualityProvidingIntermediateState eps) {
		final Set<StoreIndexInfo> mayEqualStoreIndexInfos = new HashSet<>();

		final Term selectIndex = selectInfo.getArrayCellAccess().getIndex();

		for (final Entry<IProgramVar, StoreIndexInfo> en : mFreezeVarToStoreIndexInfo.entrySet()) {
			final IProgramVar freezeVar = en.getKey();
			final StoreIndexInfo sii = en.getValue();

			if (eps.areUnequal(selectIndex, freezeVar.getTerm())) {
				// nothing to do
			} else {
				// select index and freezeVar may be equal at this location
				mayEqualStoreIndexInfos.add(sii);
			}
		}


		if (mayEqualStoreIndexInfos.size() <= 1) {
			// nothing to do
		} else {
			final StoreIndexInfo sample = mayEqualStoreIndexInfos.iterator().next();

			mSelectInfoToToSampleStoreIndexInfo.put(selectInfo, sample);

			for (final StoreIndexInfo sii : mayEqualStoreIndexInfos) {
				mergeBlocks(selectInfo, sii, sample);
			}

		}
	}

	public void finish() {
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
		mIsFinished = true;
	}

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
	}

	public Map<SelectInfo, LocationBlock> getSelectInfoToLocationBlock() {
		if (!mIsFinished) {
			throw new AssertionError();
		}
		return Collections.unmodifiableMap(mSelectInfoToLocationBlock);
	}

	public LocationBlock getLocationBlock(final SelectInfo si) {
		if (!mIsFinished) {
			throw new AssertionError();
		}
		return mSelectInfoToLocationBlock.get(si);
	}
}
