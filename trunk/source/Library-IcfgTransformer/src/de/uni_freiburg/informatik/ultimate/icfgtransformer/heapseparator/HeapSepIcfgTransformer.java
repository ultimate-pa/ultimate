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

import java.util.ArrayList;
import java.util.HashMap;
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
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SelectInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers.AddInitializingEdgesIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers.MemlocArrayUpdaterTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers.PartitionProjectionTransitionTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.CongruenceClosureSmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingIntermediateState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

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
	 * @param heapSepBacktranslationTracker
	 * @param outLocationClass
	 * @param newIcfgIdentifier
	 * @param equalityProvider
	 * @param validArray
	 * @return
	 */
	private void computeResult(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final ReplacementVarFactory replacementVarFactory,
			final IBacktranslationTracker heapSepBacktranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final IProgramNonOldVar validArray) {

		if (mSettings.isDumpPrograms()) {
//			CFG2NestedWordAutomaton.printIcfg(mServices, originalIcfg);
		}

		final ILocationFactory<OUTLOC, OUTLOC> outToOutLocFac =
				(ILocationFactory<OUTLOC, OUTLOC>) createIcfgLocationToIcfgLocationFactory();

		final ComputeStoreInfosAndArrayGroups<INLOC> csiiaag =
					new ComputeStoreInfosAndArrayGroups<>(originalIcfg, mHeapArrays, mMgdScript);
		final MemlocArrayManager locArrayManager = csiiaag.getLocArrayManager();

		/*
		 * 1. Preprocess the program for the static analysis.
		 */
		final IIcfg<OUTLOC> preprocessedIcfg;


		mLogger.info("Heap separator: starting loc-array-style preprocessing");

		/*
		 * add the memloc array updates to each transition with an array update
		 * the values the memloc array is set to are location literals, those are pairwise different by axiom
		 */
		final IIcfg<OUTLOC> icfgWithMemlocUpdates;
		final Map<IcfgEdge, IcfgEdge> originalEdgeToTransformedEdgeMapping = new HashMap<>();
		{
			final MemlocArrayUpdaterTransformulaTransformer<INLOC, OUTLOC> mauit =
					new MemlocArrayUpdaterTransformulaTransformer<>(
							mServices,
							mLogger,
							originalIcfg.getCfgSmtToolkit(),
							locArrayManager,
							mHeapArrays, csiiaag.getEdgeToPositionToLocUpdateInfo());

			final IBacktranslationTracker preprocBtt =
					(e1, e2) -> originalEdgeToTransformedEdgeMapping.put((IcfgEdge) e1, (IcfgEdge) e2);

			final IcfgTransformer<INLOC, OUTLOC> icgtf = new IcfgTransformer<>(mLogger, originalIcfg, funLocFac,
					preprocBtt, outLocationClass, "icfg_with_locarrays", mauit);

//			originalEdgeToTransformedEdgeMapping =
//					icgtf.getOriginalEdgeToTransformedEdgeMapping();
			icfgWithMemlocUpdates = icgtf.getResult();

			locArrayManager.freeze();
			mLogger.info("finished MemlocArrayUpdater");
//			mLogger.info("finished MemlocArrayUpdater, created " + mauit.getLocationLiterals().size() +
//					" location literals (each corresponds to one heap write)");
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
							(e1, e2) -> {},
							outLocationClass,
							icfgWithMemlocUpdates,
							mlit.getResult(),
							"icfg_with_initialized_loc_arrays");

			icfgWMemlocInitialized = initTf.getResult();


			final Set<IProgramConst> locLiterals = new HashSet<>();
			locLiterals.addAll(csiiaag.getLocLiterals());
			locLiterals.addAll(locArrayManager.getInitLocLits());

			// literal handling (different ways)
			{
				equalityProvider.announceAdditionalLiterals(locLiterals);

				final Set<Term> literalTerms = locLiterals.stream()
						.map(pvoc -> pvoc.getTerm())
						.collect(Collectors.toSet());
				assert mSettings.isAssertFreezeVarLitDisequalitiesIntoScript() !=
						 mSettings.isAddLiteralDisequalitiesAsAxioms() : "exactly one solution for literals in script "
						 		+ "should be enabled";
				if (mSettings.isAssertFreezeVarLitDisequalitiesIntoScript()) {
					assertLiteralDisequalitiesIntoScript(literalTerms);
				}
				if (mSettings.isAddLiteralDisequalitiesAsAxioms()) {

					final Term allLiteralDisequalities = SmtUtils.and(mMgdScript.getScript(),
							CongruenceClosureSmtUtils.createDisequalityTermsForNonTheoryLiterals(mMgdScript.getScript(),
									literalTerms));
					icfgWMemlocInitialized = new AxiomsAdderIcfgTransformer<>( mLogger,
							"icfg_with_memloc_updates_and_literal_axioms", outLocationClass,
							icfgWithMemlocUpdates, outToOutLocFac, heapSepBacktranslationTracker, allLiteralDisequalities)
							.getResult();
				}
			}
			preprocessedIcfg = icfgWMemlocInitialized;
		}
		mLogger.info("finished preprocessing for the equality analysis");

//		mLogger.debug("storeIndexInfoToLocLiteral: " + DataStructureUtils.prettyPrint(storeIndexInfoToLocLiteral));

//		mLogger.debug("edgeToIndexToStoreInfo: " + DataStructureUtils.prettyPrint(edgeToStoreToArrayGroupToStoreInfo));

		/*
		 * 2. run the equality analysis
		 */
		{

			/*
			 * tracked arrays are
			 *  - the loc arrays, because we want information about them
			 *  - the valid array, because it is important in order for inferring that malloc always returns fresh
			 *   (valid) values
			 */
			final List<String> trackedArraySubstrings = new ArrayList<>();
			trackedArraySubstrings.add(MemlocArrayManager.LOC_ARRAY_PREFIX);
			trackedArraySubstrings.add("valid");
//			trackedArraySubstrings.add("rep");

			equalityProvider.setTrackedArrays(trackedArraySubstrings);
			equalityProvider.preprocess(preprocessedIcfg);
			mLogger.info("finished equality analysis");
		}


		/*
		 * 3a.
		 */
		final FindSelects findSelects = new FindSelects(mLogger, mMgdScript, mHeapArrays,
				mStatistics, csiiaag);
		new IcfgEdgeIterator(originalIcfg).forEachRemaining(edge -> findSelects.processEdge(edge));
//		new IcfgEdgeIterator(preprocessedIcfg).forEachRemaining(edge -> findSelects.processEdge(edge));
		findSelects.finish();
		mLogger.info("Finished detection of select terms (\"array reads\")");
//		mLogger.info("  array groups: " + DataStructureUtils.prettyPrint(
//				new HashSet<>(findSelects.getArrayToArrayGroup().values())));
//		mLogger.info("  select infos: " + DataStructureUtils.prettyPrint(findSelects.getSelectInfos()));

		final HeapPartitionManager partitionManager = new HeapPartitionManager(mLogger, mMgdScript,
				mHeapArrays, mStatistics, locArrayManager, csiiaag);

		/*
		 * 3b. compute an array partitioning
		 */
		for (final SelectInfo si : findSelects.getSelectInfos()) {
			final IcfgEdge preprocessedEdge = originalEdgeToTransformedEdgeMapping.get(si.getEdgeInfo().getEdge());
			partitionManager.processSelect(si,
					getEqualityProvidingIntermediateState(preprocessedEdge, equalityProvider));
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
						csiiaag,
						mHeapArrays,
						mStatistics,
						originalIcfg.getCfgSmtToolkit());
		final IcfgTransformer<INLOC, OUTLOC> icfgtf = new IcfgTransformer<>(mLogger, originalIcfg, funLocFac,
				heapSepBacktranslationTracker, outLocationClass, "memPartitionedIcfg", heapSeparatingTransformer);
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
	 * In order to be able to deal with selects where not all TermVariables are in-vars, we need a "intermediate states"
	 * here.
	 *
	 * The intermediate state for an edge is the meet of the analysis result of its source location with the abstracted
	 * transition relation of the edge.
	 *
	 * @param edgeInfo
	 * @param equalityProvider
	 * @return
	 */
	private IEqualityProvidingIntermediateState getEqualityProvidingIntermediateState(final IcfgEdge edge, //final EdgeInfo edgeInfo,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {
//		final IEqualityProvidingIntermediateState result =
//				equalityProvider.getEqualityProvidingIntermediateState(edge);
////				equalityProvider.getEqualityProvidingIntermediateState(edgeInfo.getEdge());
//		return result;
		return equalityProvider.getEqualityProvidingIntermediateState(edge);
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