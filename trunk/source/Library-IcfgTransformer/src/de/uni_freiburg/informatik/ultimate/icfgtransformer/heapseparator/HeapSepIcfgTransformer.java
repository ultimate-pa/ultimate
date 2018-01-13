package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class HeapSepIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private IIcfg<OUTLOC> mResultIcfg;

	private final Preprocessing mPreprocessing = Preprocessing.FREEZE_VARIABLES;

	private ILogger mLogger;

	private final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> mEqualityProvider;

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
	 * @param transformer
	 *            The transformer that should be applied to each transformula of each transition of the input
	 *            {@link IIcfg} to create a new {@link IIcfg}.
	 */
	public HeapSepIcfgTransformer(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {
		mEqualityProvider = equalityProvider;
		computeResult(originalIcfg, funLocFac, backtranslationTracker, outLocationClass, newIcfgIdentifier);
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
	 * @param backtranslationTracker
	 * @param outLocationClass
	 * @param newIcfgIdentifier
	 * @return
	 */
	private void computeResult(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier) {


		final CfgSmtToolkit oldCsToolkit = originalIcfg.getCfgSmtToolkit();
		final IUltimateServiceProvider services;
		// TOOD
		final ILocationFactory<OUTLOC, OUTLOC> outToOutLocFac = null;


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

			/*
			 * Create a fresh literal/constant for each freeze variable that was introduced, we call them freeze
			 * literals.
			 * Announce them to the equality analysis as special literals, which are, by axiom, pairwise disjoint.
			 */
			final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit = new HashMap<>();
			for (final IProgramNonOldVar freezeVar :
				sifit.getWriteIndexToTfInfoToFreezeVar().values().collect(Collectors.toList())) {
				// TODO
//				oldCsToolkit.ge
			}

			mEqualityProvider.announceAdditionalLiterals(freezeVarTofreezeVarLit.values());

			/*
			 * Add initialization code for each of the newly introduce freeze variables.
			 * Each freeze variable is initialized to its corresponding freeze literal.
			 * Furthermore the valid-array (of the memory model) is assumed to be 1 at each freeze literal.
			 */
			final FreezeVarInitializer<OUTLOC, OUTLOC> fvi = new FreezeVarInitializer<>(mLogger,
					"icfg_with_initialized_freeze_vars", outLocationClass, icfgWFreezeVarsUninitialized, outToOutLocFac,
					backtranslationTracker, freezeVarTofreezeVarLit);
			final IIcfg<OUTLOC> icfgWFreezeVarsInitialized = fvi.getResult();

			preprocessedIcfg = icfgWFreezeVarsInitialized;
		} else {
			assert mPreprocessing == Preprocessing.MEMLOC_ARRAY;
			// TODO implement..
			preprocessedIcfg = null;
		}


		/*
		 * 2. run the equality analysis
		 */
		mEqualityProvider.preprocess(preprocessedIcfg);

		/*
		 * 3. compute an array partitioning
		 */


//		final HeapSepPreAnalysis heapSepPreanalysis = new HeapSepPreAnalysis(mLogger,
//				csToolkit.getManagedScript());
//		new IcfgEdgeIterator(icfg).forEachRemaining(edge -> heapSepPreanalysis.processEdge(edge));


//		final NewArrayIdProvider newArrayIdProvider = new NewArrayIdProvider(csToolkit, equalityProvider, hspav, statistics);

		/*
		 * 4. Execute the transformer that splits up the arrays according to the result from the equality analysis.
		 *  Note that this transformation is done on the original input Icfg, not on the output of the
		 *  ArrayIndexExposer, which we ran the equality analysis on.
		 */
//		final HeapSepTransFormulaTransformer hstftf = new HeapSepTransFormulaTransformer(csToolkit, services,
//				equalityProvider);
//
//		hstftf.preprocessIcfg(originalIcfg);
//		final BasicIcfg<OUTLOC> resultIcfg =
//				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
//		final TransformedIcfgBuilder<INLOC, OUTLOC> lst =
//				new TransformedIcfgBuilder<>(funLocFac, backtranslationTracker, transformer, originalIcfg, resultIcfg);
//		processLocations(originalIcfg.getInitialNodes(), lst);
//		lst.finish();
//		return resultIcfg;
//		final BasicIcfg<OUTLOC> resultIcfg =
//				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
//		mResultIcfg = null;
	}

	private void processLocations(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {
		final IcfgLocationIterator<INLOC> iter = new IcfgLocationIterator<>(init);

		// we need to create new return transitions after new call transitions have been created
		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		while (iter.hasNext()) {
			final INLOC oldSource = iter.next();
			final OUTLOC newSource = lst.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				@SuppressWarnings("unchecked")
				final OUTLOC newTarget = lst.createNewLocation((INLOC) oldTransition.getTarget());
				if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
					rtrTransitions.add(new Triple<>(newSource, newTarget, oldTransition));
				} else {
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}

		rtrTransitions.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

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

	public ICsvProviderProvider<Number> getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}
}
