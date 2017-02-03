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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminationSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminator;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MapEliminationTransformer implements ITransformulaTransformer {
	private final IEqualityAnalysisResultProvider<IcfgLocation> mEqualityProvider;
	private final Map<TransFormula, ModifiableTransFormula> mTransFormulas;
	private final Map<TransFormula, IcfgLocation> mSourceLocations;
	private final Map<TransFormula, IcfgLocation> mTargetLocations;
	private final MapEliminator mMapEliminator;
	private final ManagedScript mManagedScript;
	private final ReplacementVarFactory mReplacementVarFactory;

	public MapEliminationTransformer(final IIcfg<?> icfg, final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable,
			final ReplacementVarFactory replacementVarFactory, final MapEliminationSettings settings,
			final IEqualityAnalysisResultProvider<IcfgLocation> equalityProvider) {
		mEqualityProvider = equalityProvider;
		mTransFormulas = new HashMap<>();
		mSourceLocations = new HashMap<>();
		mTargetLocations = new HashMap<>();
		mManagedScript = Objects.requireNonNull(managedScript);
		mReplacementVarFactory = Objects.requireNonNull(replacementVarFactory);
		preprocessIcfg(icfg, replacementVarFactory, managedScript);
		mMapEliminator = new MapEliminator(services, logger, managedScript, symbolTable, replacementVarFactory,
				mTransFormulas.values(), settings);
	}

	private void preprocessIcfg(final IIcfg<?> icfg, final ReplacementVarFactory replacementVarFactory,
			final ManagedScript managedScript) {
		final IcfgEdgeIterator iter = new IcfgEdgeIterator(icfg);
		while (iter.hasNext()) {
			final IIcfgTransition<?> transition = iter.next();
			final TransFormula transformula = IcfgUtils.getTransformula(transition);
			final IcfgLocation sourceLocation = transition.getSource();
			final IcfgLocation targetLocation = transition.getTarget();
			final ModifiableTransFormula modifiable =
					ModifiableTransFormulaUtils.buildTransFormula(transformula, replacementVarFactory, managedScript);
			mTransFormulas.put(transformula, modifiable);
			mSourceLocations.put(transformula, sourceLocation);
			mTargetLocations.put(transformula, targetLocation);
		}
	}

	@Override
	public UnmodifiableTransFormula transform(final UnmodifiableTransFormula transformula) {
		final ModifiableTransFormula modifiable = mTransFormulas.get(transformula);
		final EqualityAnalysisResult equalityAnalysisBefore =
				mEqualityProvider.getAnalysisResult(mSourceLocations.get(transformula), mMapEliminator.getDoubletons());
		final EqualityAnalysisResult equalityAnalysisAfter =
				mEqualityProvider.getAnalysisResult(mTargetLocations.get(transformula), mMapEliminator.getDoubletons());
		final ModifiableTransFormula newTf =
				mMapEliminator.getRewrittenTransFormula(modifiable, equalityAnalysisBefore, equalityAnalysisAfter);
		return TransFormulaBuilder.constructCopy(mManagedScript, newTf, Collections.emptySet(), Collections.emptySet(),
				Collections.emptyMap());
	}

	@Override
	public String getName() {
		return MapEliminationTransformer.class.getSimpleName();
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mReplacementVarFactory.constructIIcfgSymbolTable();
	}
}
