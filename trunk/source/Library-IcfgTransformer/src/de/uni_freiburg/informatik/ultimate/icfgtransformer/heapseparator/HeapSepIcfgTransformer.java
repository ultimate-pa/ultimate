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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.CongruenceClosureSmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingIntermediateState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

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

		final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo;
		final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup;
		{
			final ComputeStoreIndexInfosAndArrayGroups<INLOC> csiiaag =
					new ComputeStoreIndexInfosAndArrayGroups<>(originalIcfg, mHeapArrays);
			edgeToIndexToStoreIndexInfo =
					csiiaag.getEdgeToIndexToStoreIndexInfo();
			arrayToArrayGroup = csiiaag.getArrayToArrayGroup();
		}

		/*
		 * 1. Execute the preprocessing
		 */
		final IIcfg<OUTLOC> preprocessedIcfg;
		final Map<StoreIndexInfo, IProgramNonOldVar> storeIndexInfoToFreezeVar;

		final Map<StoreIndexInfo, IProgramConst> storeIndexInfoToLocLiteral;
		final MemlocArrayManager memlocArrayManager;

		//			assert mSettings.getPreprocessing() == Preprocessing.MEMLOC_ARRAY;
		mLogger.info("Heap separator: starting memloc-array-style preprocessing");

		memlocArrayManager = new MemlocArrayManager(mMgdScript);

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
							memlocArrayManager,
							mHeapArrays, edgeToIndexToStoreIndexInfo);



			final IcfgTransformer<INLOC, OUTLOC> icgtf = new IcfgTransformer<>(mLogger, originalIcfg, funLocFac,
					backtranslationTracker, outLocationClass, "icfg_with_uninitialized_freeze_vars", mauit);

			storeIndexInfoToLocLiteral = mauit.getStoreIndexInfoToLocLiteral();
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
					new ComputeMemlocInitializingTransformula(memlocArrayManager, validArray, mSettings,
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

			memlocLiterals.addAll(memlocArrayManager.getMemLocLits());
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

			storeIndexInfoToFreezeVar = null;
		}
		mLogger.info("finished preprocessing for the equality analysis");

		mLogger.debug("storeIndexInfoToLocLiteral: " + DataStructureUtils.prettyPrint(storeIndexInfoToLocLiteral));

		mLogger.debug("edgeToIndexToStoreIndexInfo: " + DataStructureUtils.prettyPrint(edgeToIndexToStoreIndexInfo));

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
				mHeapArrays, mStatistics, memlocArrayManager, storeIndexInfoToLocLiteral);

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
						edgeToIndexToStoreIndexInfo,
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

class HeapSepSettings {


	private final boolean mDumpPrograms = true;

	private final String mDumpProgramsPath = "C:\\Temp\\automata";

	private final boolean mCrashOnArrayAssume = true;

	/**
	 *
	 * not clear:
	 *  <li> how much of a slowdown this causes
	 *  <li> if it is only necessary for assertions or not
	 */
	private final boolean mAssumeFreezeVarLitDisequalitiesAtInitEdges = false;

	private final boolean mAssertFreezeVarLitDisequalitiesIntoScript = true;

	private final boolean mAddLiteralDisequalitiesAsAxioms = false;

	public boolean isAssumeFreezeVarLitDisequalitiesAtInitEdges() {
		return mAssumeFreezeVarLitDisequalitiesAtInitEdges;
	}

	public boolean isAddLiteralDisequalitiesAsAxioms() {
		return mAddLiteralDisequalitiesAsAxioms;
	}

	public boolean isAssertFreezeVarLitDisequalitiesIntoScript() {
		return mAssertFreezeVarLitDisequalitiesIntoScript;
	}

	/**
	 * Dump the programs (input program, program as fed to equality domain, transformed program) to disk as automata
	 * (via {@link CFG2Automaton}.
	 *
	 * @return
	 */
	public boolean isDumpPrograms() {
		return mDumpPrograms;
	}

	/**
	 * Path used if {@link #isDumpPrograms()} is set.
	 *
	 * @return
	 */
	public String getDumpProgramsPath() {
		return mDumpProgramsPath;
	}

	/**
	 * Our technique does not handle assumes between arrays, if those arrays are supposed to be separated.
	 * (Not yet used, not clear what else to do but crash..)
	 *
	 * @return
	 */
	public boolean isCrashOnArrayAssume() {
		return mCrashOnArrayAssume;
	}
}

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

class MemlocArrayManager {

	private boolean mIsFrozen;

	public static final String MEMLOC = "##memloc";
	public static final String MEMLOC_SORT_INT = "##mmlc_sort_int";

	final Map<Integer, IProgramNonOldVar> mDimToMemlocArrayInt = new HashMap<>();
	final Map<Integer, Sort> mDimToMemLocSort = new HashMap<>();

	boolean mAlreadyDeclaredMemlocSort;

	private final ManagedScript mMgdScript;

	private Map<IProgramNonOldVar, Term> mMemlocArrayToInitConstArray;

	private Map<IProgramVarOrConst, IProgramConst> mMemlocArrayToLit;

	public MemlocArrayManager(final ManagedScript mgdScript) {
		mMgdScript = mgdScript;
		mIsFrozen = false;
	}

	IProgramNonOldVar getMemlocArray(final int dim) {
		IProgramNonOldVar result = mDimToMemlocArrayInt.get(dim);
		if (result == null) {
			assert !mIsFrozen;
			mMgdScript.lock(this);
			final Sort intToLocations = SmtSortUtils.getArraySort(mMgdScript.getScript(),
					SmtSortUtils.getIntSort(mMgdScript), getMemlocSort(dim));
			result = ProgramVarUtils.constructGlobalProgramVarPair(MEMLOC + "_int_" + dim, intToLocations, mMgdScript,
					this);
			mMgdScript.unlock(this);

			mDimToMemlocArrayInt.put(dim, result);

		}
		return result;
	}

	Sort getMemlocSort(final int dim) {
		// TODO: should we have a different sort per dimension?
		if (!mAlreadyDeclaredMemlocSort) {
			mMgdScript.getScript().declareSort(MEMLOC_SORT_INT, 0);
			mAlreadyDeclaredMemlocSort = true;
		}
		return mMgdScript.getScript().sort(MEMLOC_SORT_INT);
	}

	public Map<IProgramNonOldVar, Term> getMemlocArrayToInitConstantArray() {
		// this may be called only after all memloc arrays that we need have been created.";

		if (!mIsFrozen){
			mIsFrozen = true;
			mMgdScript.lock(this);

			assert mMemlocArrayToInitConstArray == null;
			mMemlocArrayToInitConstArray = new HashMap<>();
			assert mMemlocArrayToLit == null;
			mMemlocArrayToLit = new HashMap<>();

			for (final Entry<Integer, IProgramNonOldVar> en : mDimToMemlocArrayInt.entrySet()) {
				final Integer dim = en.getKey();
				final IProgramNonOldVar memlocArray = en.getValue();

				// literal has value sort (the sort of the memloc literals), we will create a constant array from it
				final String memlocLitName = getMemlocLitName(memlocArray);
				mMgdScript.declareFun(this, memlocLitName, new Sort[0], getMemlocSort(dim));

				final ApplicationTerm memlocLitTerm = (ApplicationTerm) mMgdScript.term(this, memlocLitName);

				mMemlocArrayToLit.put(memlocArray, new HeapSepProgramConst(memlocLitTerm));

				final Term constArray = mMgdScript.term(this, "const", null, memlocArray.getSort(), memlocLitTerm);
				mMemlocArrayToInitConstArray.put(memlocArray, constArray);
			}
			mMgdScript.unlock(this);
		}
		return mMemlocArrayToInitConstArray;
	}

	private String getMemlocLitName(final IProgramNonOldVar memlocVar) {
		// TODO make _really_ sure that the new id is unique
		return memlocVar.getGloballyUniqueId() + "_lit";
	}

	public Set<IProgramConst> getMemLocLits() {
		return new HashSet<>(mMemlocArrayToLit.values());
	}
}