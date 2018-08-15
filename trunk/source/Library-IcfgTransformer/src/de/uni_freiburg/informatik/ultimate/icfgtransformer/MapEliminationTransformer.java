package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminationSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MapEliminationTransformer implements ITransformulaTransformer {
	private final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> mEqualityProvider;
	private final Map<TransFormula, ModifiableTransFormula> mTransFormulas;
	private final Map<TransFormula, IcfgLocation> mSourceLocations;
	private final Map<TransFormula, IcfgLocation> mTargetLocations;
	private MapEliminator mMapEliminator = null;
	private final ManagedScript mManagedScript;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IIcfgSymbolTable mSymbolTable;
	private final MapEliminationSettings mSettings;

	public MapEliminationTransformer(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable,
			final ReplacementVarFactory replacementVarFactory, final MapEliminationSettings settings,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {
		mServices = services;
		mLogger = logger;
		mSymbolTable = symbolTable;
		mSettings = settings;
		mEqualityProvider = equalityProvider;
		mTransFormulas = new HashMap<>();
		mSourceLocations = new HashMap<>();
		mTargetLocations = new HashMap<>();
		mManagedScript = Objects.requireNonNull(managedScript);
		mReplacementVarFactory = Objects.requireNonNull(replacementVarFactory);
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		final IcfgEdgeIterator iter = new IcfgEdgeIterator(icfg);
		while (iter.hasNext()) {
			final IIcfgTransition<?> transition = iter.next();
			final IcfgLocation sourceLocation = transition.getSource();
			final IcfgLocation targetLocation = transition.getTarget();
			if (transition instanceof IIcfgReturnTransition<?, ?>) {
				final IIcfgReturnTransition<?, ?> retTrans = (IIcfgReturnTransition<?, ?>) transition;
				saveTransformula(retTrans.getAssignmentOfReturn(), sourceLocation, targetLocation);
				saveTransformula(retTrans.getLocalVarsAssignmentOfCall(), sourceLocation, targetLocation);
			} else {
				final TransFormula transformula = IcfgUtils.getTransformula(transition);
				saveTransformula(transformula, sourceLocation, targetLocation);
			}

		}
		mMapEliminator = new MapEliminator(mServices, mLogger, mManagedScript, mSymbolTable, mReplacementVarFactory,
				mTransFormulas.values(), mSettings);
		// TODO: This is only necessary, if the icfg contains maps
		mEqualityProvider.preprocess(icfg);
	}

	private void saveTransformula(final TransFormula transformula, final IcfgLocation sourceLocation,
			final IcfgLocation targetLocation) {
		final ModifiableTransFormula modifiable =
				ModifiableTransFormulaUtils.buildTransFormula(transformula, mReplacementVarFactory, mManagedScript);
		mTransFormulas.put(transformula, modifiable);
		mSourceLocations.put(transformula, sourceLocation);
		mTargetLocations.put(transformula, targetLocation);
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula transformula) {
		final ModifiableTransFormula modifiable = mTransFormulas.get(transformula);
		final EqualityAnalysisResult equalityAnalysisBefore =
				mEqualityProvider.getAnalysisResult(mSourceLocations.get(transformula), mMapEliminator.getDoubletons());
		final EqualityAnalysisResult equalityAnalysisAfter =
				mEqualityProvider.getAnalysisResult(mTargetLocations.get(transformula), mMapEliminator.getDoubletons());
		final ModifiableTransFormula newTf =
				mMapEliminator.getRewrittenTransFormula(modifiable, equalityAnalysisBefore, equalityAnalysisAfter);
		// TODO: How can we decide whether the transformation is an overapproximation or not?
		return new TransformulaTransformationResult(TransFormulaBuilder.constructCopy(mManagedScript, newTf,
				Collections.emptySet(), Collections.emptySet(), Collections.emptyMap()), true);
	}

	@Override
	public String getName() {
		return MapEliminationTransformer.class.getSimpleName();
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mReplacementVarFactory.constructIIcfgSymbolTable();
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		return mReplacementVarFactory.constructModifiableGlobalsTable().getProcToGlobals();
	}
}
