package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.IInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Collects interferences by walking ICFGs, optionally applies merging.
 */
public class DefaultInterferenceAbstractor implements IInterferenceAbstractor {

	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IDomain mDomain;
	private final boolean mIncludePreState;
	private final IInterferenceMerger mMerger;

	public DefaultInterferenceAbstractor(final TransFormulaToInterferencePredicate translator,
			final RelationalPredicatePostcondition postcondition, final IDomain domain, final boolean includePreState,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final IInterferenceMerger merger) {
		mTranslator = translator;
		mPostcondition = postcondition;
		mDomain = domain;
		mIncludePreState = includePreState;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mMerger = merger;
		if (includePreState && (managedScript == null || predicateFactory == null)) {
			throw new IllegalArgumentException("managedScript and predicateFactory required when includePreState=true");
		}
	}

	@Override
	public IInterferenceAbstraction abstractTransitionsToInterferenceAbstraction(
			final Map<String, Map<IcfgLocation, IPredicate>> analysisResults,
			final Map<String, IIcfg<IcfgLocation>> threadIcfgs) {
		final Map<String, Set<IPredicate>> all = new HashMap<>();
		for (final Map.Entry<String, Map<IcfgLocation, IPredicate>> entry : analysisResults.entrySet()) {
			final String threadId = entry.getKey();
			final Map<IcfgLocation, IPredicate> locationStates = entry.getValue();
			Set<IPredicate> threadInterferences = collectFromThread(locationStates);

			if (mMerger != null) {
				threadInterferences = mMerger.merge(threadInterferences, mDomain);
			}

			all.put(threadId, threadInterferences);
		}
		return DefaultInterferenceAbstraction.of(all, mPostcondition);
	}

	private Set<IPredicate> collectFromThread(final Map<IcfgLocation, IPredicate> locationStates) {
		final Set<IPredicate> result = new HashSet<>();
		for (final Map.Entry<IcfgLocation, IPredicate> entry : locationStates.entrySet()) {
			final IcfgLocation loc = entry.getKey();
			final IPredicate preState = entry.getValue();
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
}
