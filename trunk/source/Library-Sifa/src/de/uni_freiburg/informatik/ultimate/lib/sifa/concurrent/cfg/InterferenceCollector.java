package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Collects interferences by walking ICFGs. Building strategy is configurable.
 */
public class InterferenceCollector {

	private final TransFormulaToPredicate mTranslator;
	private final boolean mIncludePreState;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	/**
	 * Creates collector that ignores pre-state (maximal interference).
	 */
	public InterferenceCollector(final TransFormulaToPredicate translator) {
		this(translator, false, null, null);
	}

	/**
	 * Creates collector with configurable pre-state inclusion.
	 */
	public InterferenceCollector(final TransFormulaToPredicate translator, final boolean includePreState,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		mTranslator = translator;
		mIncludePreState = includePreState;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		if (includePreState && (managedScript == null || predicateFactory == null)) {
			throw new IllegalArgumentException("managedScript and predicateFactory required when includePreState=true");
		}
	}

	public InterferenceAbstraction collectFromAllThreads(final Map<String, ThreadAnalysisInput> analysisResults) {
		final Map<String, Set<IPredicate>> all = new HashMap<>();
		for (final Map.Entry<String, ThreadAnalysisInput> entry : analysisResults.entrySet()) {
			final ThreadAnalysisInput input = entry.getValue();
			all.put(entry.getKey(), collectFromThread(input.getLocationStates(), input.getIcfg()));
		}
		return InterferenceAbstraction.of(all);
	}

	private Set<IPredicate> collectFromThread(final Map<IcfgLocation, IPredicate> locationStates,
			final IIcfg<IcfgLocation> icfg) {
		final Set<IPredicate> result = new HashSet<>();
		for (final Map.Entry<IcfgLocation, IPredicate> entry : locationStates.entrySet()) {
			final IcfgLocation loc = entry.getKey();
			final IPredicate preState = entry.getValue();
			// When includePreState is true, skip entries with null predicates
			if (mIncludePreState && preState == null) {
				continue;
			}
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				final TransFormula tf = edge.getTransformula();
				if (tf != null) {
					result.add(buildInterference(preState, tf));
				}
			}
		}
		return result;
	}

	private IPredicate buildInterference(final IPredicate preState, final TransFormula tf) {
		final IPredicate transitionPred = mTranslator.translate(tf);
		if (!mIncludePreState) {
			return transitionPred;
		}
		final Term combined = SmtUtils.and(mManagedScript.getScript(), preState.getFormula(),
				transitionPred.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}

	public static class ThreadAnalysisInput {
		private final Map<IcfgLocation, IPredicate> mLocationStates;
		private final IIcfg<IcfgLocation> mIcfg;

		public ThreadAnalysisInput(final Map<IcfgLocation, IPredicate> locationStates, final IIcfg<IcfgLocation> icfg) {
			mLocationStates = locationStates;
			mIcfg = icfg;
		}

		public Map<IcfgLocation, IPredicate> getLocationStates() {
			return mLocationStates;
		}

		public IIcfg<IcfgLocation> getIcfg() {
			return mIcfg;
		}
	}
}
