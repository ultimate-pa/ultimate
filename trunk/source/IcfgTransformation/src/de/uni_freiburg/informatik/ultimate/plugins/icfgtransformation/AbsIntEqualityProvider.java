package de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

public class AbsIntEqualityProvider implements IEqualityAnalysisResultProvider<IcfgLocation> {
	
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Map<IcfgLocation, Set<VPState<IcfgEdge>>> mLoc2States;
	
	public AbsIntEqualityProvider(final IUltimateServiceProvider services, final IIcfg<?> icfg) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLoc2States = runPreAnalysis(icfg);
	}
	
	private Map<IcfgLocation, Set<VPState<IcfgEdge>>> runPreAnalysis(final IIcfg<?> icfg) {
		final IProgressAwareTimer timer = mServices.getProgressMonitorService();
		final IAbstractInterpretationResult<VPState<IcfgEdge>, IcfgEdge, IProgramVarOrConst, IcfgLocation> absIntResult =
				AbstractInterpreter.runFutureEqualityDomain(icfg, timer, mServices, false, mLogger);
		return absIntResult.getLoc2States();
	}
	
	@Override
	public EqualityAnalysisResult getAnalysisResult(final IcfgLocation location,
			final Set<Doubleton<Term>> doubletons) {
		final Set<VPState<IcfgEdge>> states = mLoc2States.get(location);
		if (states == null) {
			return new EqualityAnalysisResult(doubletons);
		}
		
		final Set<Doubleton<Term>> equal = new HashSet<>();
		final Set<Doubleton<Term>> distinct = new HashSet<>();
		final Set<Doubleton<Term>> unknown = new HashSet<>();
		for (final Doubleton<Term> unorderedPair : doubletons) {
			if (states.stream()
					.allMatch(a -> a.areEqual(unorderedPair.getOneElement(), unorderedPair.getOtherElement()))) {
				equal.add(unorderedPair);
			} else if (states.stream()
					.allMatch(a -> a.areUnEqual(unorderedPair.getOneElement(), unorderedPair.getOtherElement()))) {
				distinct.add(unorderedPair);
			} else {
				unknown.add(unorderedPair);
			}
		}
		return new EqualityAnalysisResult(equal, distinct, unknown);
	}
	
}
