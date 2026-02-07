package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class DefaultInterferenceAbstractor implements IInterferenceAbstractor {

	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IDomain mDomain;
	private final boolean mIncludePreState;

	private static boolean canBeDropped(final IPredicate interference) {
		return SmtUtils.isTrueLiteral(interference.getFormula()) || SmtUtils.isFalseLiteral(interference.getFormula());
	}

	private static boolean modifiesGlobals(final TransFormula tf) {
		return tf.getAssignedVars().stream().anyMatch(pv -> pv.isGlobal());
	}

	public DefaultInterferenceAbstractor(final TransFormulaToInterferencePredicate translator,
			final RelationalPredicatePostcondition postcondition, final IDomain domain, final boolean includePreState,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		mTranslator = translator;
		mPostcondition = postcondition;
		mDomain = domain;
		mIncludePreState = includePreState;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		if (includePreState && (managedScript == null || predicateFactory == null)) {
			throw new IllegalArgumentException("managedScript and predicateFactory required when includePreState=true");
		}
	}

	@Override
	public IInterferenceAbstraction abstractTransitionsToInterferenceAbstraction(
			final Map<String, Map<IcfgLocation, IPredicate>> analysisResults,
			final Map<String, IIcfg<IcfgLocation>> threadIcfgs) {
		final Map<String, Map<IcfgLocation, IPredicate>> all = new HashMap<>();
		for (final Map.Entry<String, Map<IcfgLocation, IPredicate>> entry : analysisResults.entrySet()) {
			final String threadId = entry.getKey();
			final Map<IcfgLocation, IPredicate> locationStates = entry.getValue();
			final Map<IcfgLocation, IPredicate> threadInterferences = collectFromThread(threadId, locationStates);
			all.put(threadId, threadInterferences);
		}
		return DefaultInterferenceAbstraction.of(all, mPostcondition);
	}

	private Map<IcfgLocation, IPredicate> collectFromThread(final String threadId,
			final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<IcfgLocation, IPredicate> result = new HashMap<>();
		for (final Map.Entry<IcfgLocation, IPredicate> entry : locationStates.entrySet()) {
			final IcfgLocation loc = entry.getKey();
			final IPredicate preState = entry.getValue();
			if (mIncludePreState && preState == null) {
				continue;
			}
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				final TransFormula tf = edge.getTransformula();
				if (tf != null && modifiesGlobals(tf)) {
					final IPredicate interference = buildInterference(threadId, preState, tf, loc, edge.getTarget());
					if (!canBeDropped(interference)) {
						// Join multiple edges from same location into one interference
						final IPredicate existing = result.get(loc);
						if (existing == null) {
							result.put(loc, interference);
						} else {
							result.put(loc, mDomain.join(existing, interference));
						}
					}
				}
			}
		}
		return result;
	}

	// Conjoining with pre-state makes the interference context-sensitive:
	// it can only fire from states the thread actually reaches.
	private IPredicate buildInterference(final String threadId, final IPredicate preState, final TransFormula tf,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation) {
		final IPredicate transitionPred = mTranslator.translateForInterference(tf, threadId, sourceLocation,
				targetLocation);

		if (!mIncludePreState) {
			return transitionPred;
		}

		final Term combined = SmtUtils.and(mManagedScript.getScript(), preState.getFormula(),
				transitionPred.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}
}
