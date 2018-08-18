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

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.AxiomsAdderIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SelectInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers.AddInitializingEdgesIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers.MemlocArrayUpdaterIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers.PartitionProjectionTransitionTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.CongruenceClosureSmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingIntermediateState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <INLOC>
 * @param <OUTLOC>
 */
public class HeapSepIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private IIcfg<OUTLOC> mResultIcfg;

	/**
	 * The IProgramVarOrConsts that model the heap in our memory model.
	 */
	private final List<IProgramVarOrConst> mHeapArrays;

	private final ILogger mLogger;

	private final HeapSeparatorBenchmark mStatistics;

	private final ManagedScript mMgdScript;

	private final HeapSepSettings mSettings;

	private final IUltimateServiceProvider mServices;


	/**
	 * prefix of heap arrays (copied from class "SFO" in C to Boogie translation)
	 */
	public static final String MEMORY = "#memory";


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
	public HeapSepIcfgTransformer(final ILogger logger, final IUltimateServiceProvider services,
			final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final ReplacementVarFactory replacementVarFactory, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final IProgramNonOldVar validArray) {
		assert logger != null;
		mStatistics = new HeapSeparatorBenchmark();
		mMgdScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mLogger = logger;
		mServices = services;

		mSettings = new HeapSepSettings();

		// TODO: complete, make nicer..
//		final List<String> heapArrayNames = Arrays.asList("#memory_int", "memory_$Pointer$");
		mHeapArrays = originalIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals().stream()
				.filter(pvoc -> pvoc.getGloballyUniqueId().startsWith(MEMORY)).collect(Collectors.toList());

		mLogger.info("HeapSepIcfgTransformer: Starting heap partitioning");
		mLogger.info("To be partitioned heap arrays found " + mHeapArrays);

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

		if (mSettings.isDumpPrograms()) {
//			CFG2NestedWordAutomaton.printIcfg(mServices, originalIcfg);
		}

		final ILocationFactory<OUTLOC, OUTLOC> outToOutLocFac =
				(ILocationFactory<OUTLOC, OUTLOC>) createIcfgLocationToIcfgLocationFactory();

		/*
		 * Some analysis upfront:
		 *  Discover all relevant store terms, construct StoreInfo objects for them.
		 *  To know what is relevant (i.e. Pvocs and Terms related to heap arrays), we need array groups, both on
		 *   program level and on edge level (i.e. for each term).
		 */
		final NestedMap3<EdgeInfo, Term, ArrayGroup, StoreInfo> edgeToStoreToArrayGroupToStoreInfo;
		final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup;
		NestedMap2<EdgeInfo, Term, ArrayGroup> edgeToTermToArrayGroup;
		final MemlocArrayManager locArrayManager;
//		final Map<StoreInfo, IProgramConst> storeIndexInfoToLocLiteral;
		{
			final ComputeStoreInfosAndArrayGroups<INLOC> csiiaag =
					new ComputeStoreInfosAndArrayGroups<>(originalIcfg, mHeapArrays);
			edgeToStoreToArrayGroupToStoreInfo =
					csiiaag.getEdgeToStoreToArrayToStoreInfo();
			arrayToArrayGroup = csiiaag.getArrayToArrayGroup();
			edgeToTermToArrayGroup = csiiaag.getEdgeToTermToArrayGroup();
			locArrayManager = csiiaag.getLocArrayManager();
		}

		/*
		 * 1. Preprocess the program for the static analysis.
		 */
		final IIcfg<OUTLOC> preprocessedIcfg;


		mLogger.info("Heap separator: starting loc-array-style preprocessing");

//		memlocArrayManager = new MemlocArrayManager(mMgdScript);

		/*
		 * add the memloc array updates to each transition with an array update
		 * the values the memloc array is set to are location literals, those are pairwise different by axiom
		 */
		final Set<IProgramConst> memlocLiterals = new HashSet<>();
		final IIcfg<OUTLOC> icfgWithMemlocUpdates;
		{
			final MemlocArrayUpdaterIcfgTransformer<INLOC, OUTLOC> mauit =
					new MemlocArrayUpdaterIcfgTransformer<>(mLogger,
							originalIcfg.getCfgSmtToolkit(),
							locArrayManager,
							mHeapArrays, edgeToStoreToArrayGroupToStoreInfo);



			final IcfgTransformer<INLOC, OUTLOC> icgtf = new IcfgTransformer<>(mLogger, originalIcfg, funLocFac,
					backtranslationTracker, outLocationClass, "icfg_with_locarrays", mauit);

			storeIndexInfoToLocLiteral = mauit.getStoreInfoToLocLiteral();
			/*
			 * make sure the literals are all treated as pairwise unequal
			 *			equalityProvider.announceAdditionalLiterals(mauit.getLocationLiterals());
			 */
			memlocLiterals.addAll(mauit.getLocationLiterals());


			icfgWithMemlocUpdates = icgtf.getResult();


			mLogger.info("finished MemlocArrayUpdater, created " + mauit.getLocationLiterals().size() +
					" location literals (each corresponds to one heap write)");
		}




		/*
		 * Add initialization code for the memloc arrays.
		 * Each memloc array is initialized with a constant array. The value of the constant array is a memloc
		 * literal that is different from all other memloc literals we use.
		 */
		IIcfg<OUTLOC> icfgWMemlocInitialized;
		{

			final ComputeMemlocInitializingTransformula mlit =
					new ComputeMemlocInitializingTransformula(locArrayManager, validArray, mSettings,
							mMgdScript);

			final AddInitializingEdgesIcfgTransformer<OUTLOC, OUTLOC> initTf =
					new AddInitializingEdgesIcfgTransformer<>(mLogger,
							icfgWithMemlocUpdates.getCfgSmtToolkit(),
							outToOutLocFac,
							backtranslationTracker,
							outLocationClass,
							icfgWithMemlocUpdates,
							mlit.getResult(),
							"icfg_with_initialized_freeze_vars");

			icfgWMemlocInitialized = initTf.getResult();

			//				final MemlocInitializer<OUTLOC, OUTLOC> mli = new MemlocInitializer<>(mLogger,
			//						icfgWithMemlocUpdates.getCfgSmtToolkit(),
			//						memlocArrayManager, validArray, mSettings,
			//						icfgWithMemlocUpdates.getInitialNodes());


			//				final IcfgTransformer<OUTLOC, OUTLOC> icgtf = new IcfgTransformer<>(icfgWithMemlocUpdates,
			//						outToOutLocFac, backtranslationTracker, outLocationClass, "icfgmemlocinitialized", mli);

			//				icfgWMemlocInitialized = icgtf.getResult();

			memlocLiterals.addAll(locArrayManager.getMemLocLits());
			//			}


			// literal handling (different ways)
			{

				equalityProvider.announceAdditionalLiterals(memlocLiterals);

				final Set<Term> literalTerms = memlocLiterals.stream()
						.map(pvoc -> pvoc.getTerm())
						.collect(Collectors.toSet());
				if (mSettings.isAssertFreezeVarLitDisequalitiesIntoScript()) {
					/*
					 * TODO: this is somewhere between inelegant and highly problematic -- make the axiom-style solution
					 * work!
					 */
					assertLiteralDisequalitiesIntoScript(literalTerms);
				}
				if (mSettings.isAddLiteralDisequalitiesAsAxioms()) {

					final Term allLiteralDisequalities = SmtUtils.and(mMgdScript.getScript(),
							CongruenceClosureSmtUtils.createDisequalityTermsForNonTheoryLiterals(mMgdScript.getScript(),
									literalTerms));
					icfgWMemlocInitialized = new AxiomsAdderIcfgTransformer<>( mLogger,
							"icfg_with_memloc_updates_and_literal_axioms", outLocationClass,
							icfgWithMemlocUpdates, outToOutLocFac, backtranslationTracker, allLiteralDisequalities)
							.getResult();
				}
			}

			preprocessedIcfg = icfgWMemlocInitialized;

		}
		mLogger.info("finished preprocessing for the equality analysis");

		mLogger.debug("storeIndexInfoToLocLiteral: " + DataStructureUtils.prettyPrint(storeIndexInfoToLocLiteral));

		mLogger.debug("edgeToIndexToStoreInfo: " + DataStructureUtils.prettyPrint(edgeToStoreToArrayGroupToStoreInfo));

		/*
		 * 2. run the equality analysis
		 */
		equalityProvider.preprocess(preprocessedIcfg);
		mLogger.info("finished equality analysis");


		/*
		 * 3a.
		 */
		final HeapSepPreAnalysis heapSepPreanalysis = new HeapSepPreAnalysis(mLogger, mMgdScript, mHeapArrays,
				mStatistics, arrayToArrayGroup);
		new IcfgEdgeIterator(originalIcfg).forEachRemaining(edge -> heapSepPreanalysis.processEdge(edge));
		heapSepPreanalysis.finish();
		mLogger.info("Finished pre analysis before partitioning");
		mLogger.info("  array groups: " + DataStructureUtils.prettyPrint(
				new HashSet<>(heapSepPreanalysis.getArrayToArrayGroup().values())));
		mLogger.info("  select infos: " + DataStructureUtils.prettyPrint(heapSepPreanalysis.getSelectInfos()));

		final HeapPartitionManager partitionManager = new HeapPartitionManager(mLogger, mMgdScript, arrayToArrayGroup,
				mHeapArrays, mStatistics, locArrayManager, storeIndexInfoToLocLiteral);

		/*
		 * 3b. compute an array partitioning
		 */
		for (final SelectInfo si : heapSepPreanalysis.getSelectInfos()) {
			partitionManager.processSelect(si, getEqualityProvidingIntermediateState(si.getEdgeInfo(),
					equalityProvider));
		}
		partitionManager.finish();

		/*
		 * 4. Execute the transformer that splits up the arrays according to the result from the equality analysis.
		 *  Note that this transformation is done on the original input Icfg, not on the output of the
		 *  ArrayIndexExposer, which we ran the equality analysis on.
		 */
		final PartitionProjectionTransitionTransformer<INLOC, OUTLOC> heapSeparatingTransformer =
				new PartitionProjectionTransitionTransformer<>(mLogger,
						partitionManager.getSelectInfoToDimensionToLocationBlock(),
						edgeToStoreToArrayGroupToStoreInfo,
						arrayToArrayGroup,
						mHeapArrays,
						mStatistics,
						originalIcfg.getCfgSmtToolkit());
		final IcfgTransformer<INLOC, OUTLOC> icfgtf = new IcfgTransformer<>(mLogger, originalIcfg, funLocFac,
				backtranslationTracker, outLocationClass, "memPartitionedIcfg", heapSeparatingTransformer);
		mResultIcfg = icfgtf.getResult();
	}



	public void assertLiteralDisequalitiesIntoScript(final Set<Term> literalTerms) {
		mMgdScript.lock(this);
		final Term allLiteralDisequalities = SmtUtils.and(mMgdScript.getScript(),
				CongruenceClosureSmtUtils.createDisequalityTermsForNonTheoryLiterals(
						mMgdScript.getScript(), literalTerms));
		mMgdScript.assertTerm(this, allLiteralDisequalities);
		mMgdScript.unlock(this);
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
		final IEqualityProvidingIntermediateState result =
				equalityProvider.getEqualityProvidingIntermediateState(edgeInfo.getEdge());
		return result;
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}


	public HeapSeparatorBenchmark getStatistics() {
		return mStatistics;
	}

	/**
	 * (almost) a copy from IcfgTransformationObserver
	 *  --> should probably replace this with a less ad-hoc solution some time
	 *
	 * @return
	 */
	private static ILocationFactory<BoogieIcfgLocation, BoogieIcfgLocation> createIcfgLocationToIcfgLocationFactory() {
		return (oldLocation, debugIdentifier, procedure) -> {
				final BoogieIcfgLocation rtr = new BoogieIcfgLocation(debugIdentifier, procedure,
					oldLocation.isErrorLocation(), oldLocation.getBoogieASTNode());
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};
	}
}