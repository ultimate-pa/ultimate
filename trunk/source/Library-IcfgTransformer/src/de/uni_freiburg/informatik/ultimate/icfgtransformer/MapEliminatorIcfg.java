package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminationSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminator;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MapEliminatorIcfg {
	private final IEqualityAnalysisResultProvider<IcfgLocation> mEqualityProvider;
	private final Map<TransFormula, ModifiableTransFormula> mTransFormulas;
	private final Map<TransFormula, IcfgLocation> mSourceLocations;
	private final Map<TransFormula, IcfgLocation> mTargetLocations;
	private final MapEliminator mMapEliminator;

	public MapEliminatorIcfg(final IIcfg<?> icfg, final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable,
			final ReplacementVarFactory replacementVarFactory, final MapEliminationSettings settings,
			final IEqualityAnalysisResultProvider<IcfgLocation> equalityProvider) {
		mEqualityProvider = equalityProvider;
		mTransFormulas = new HashMap<>();
		mSourceLocations = new HashMap<>();
		mTargetLocations = new HashMap<>();
		preprocessIcfg(icfg, replacementVarFactory, managedScript);
		mMapEliminator = new MapEliminator(services, logger, managedScript, symbolTable, replacementVarFactory,
				mTransFormulas.values(), settings);
	}

	private void preprocessIcfg(final IIcfg<?> icfg, final ReplacementVarFactory replacementVarFactory,
			final ManagedScript managedScript) {
		final Deque<IcfgLocation> open = new ArrayDeque<>(icfg.getInitialNodes());
		final Set<IcfgLocation> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final IcfgLocation location = open.removeFirst();
			if (!closed.add(location)) {
				continue;
			}
			for (final IcfgEdge transition : location.getOutgoingEdges()) {
				final TransFormula transformula = IcfgUtils.getTransformula(transition);
				final IcfgLocation sourceLocation = transition.getSource();
				final IcfgLocation targetLocation = transition.getTarget();
				final ModifiableTransFormula modifiable = ModifiableTransFormulaUtils.buildTransFormula(transformula,
						replacementVarFactory, managedScript);
				mTransFormulas.put(transformula, modifiable);
				mSourceLocations.put(transformula, sourceLocation);
				mTargetLocations.put(transformula, targetLocation);
				open.add(targetLocation);
			}
		}
	}

	public ModifiableTransFormula transform(final TransFormula transformula) {
		final ModifiableTransFormula modifiable = mTransFormulas.get(transformula);
		final EqualityAnalysisResult equalityAnalysisBefore = mEqualityProvider
				.getAnalysisResult(mSourceLocations.get(transformula), mMapEliminator.getDoubletons());
		final EqualityAnalysisResult equalityAnalysisAfter = mEqualityProvider
				.getAnalysisResult(mTargetLocations.get(transformula), mMapEliminator.getDoubletons());
		return mMapEliminator.getRewrittenTransFormula(modifiable, equalityAnalysisBefore, equalityAnalysisAfter);
	}
}
