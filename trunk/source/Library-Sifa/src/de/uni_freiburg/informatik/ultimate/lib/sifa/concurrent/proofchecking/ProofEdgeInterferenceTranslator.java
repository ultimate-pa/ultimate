package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeSemantics;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/** Basic translation regardless of interference settings, used for soundness proof of analysis. */
public final class ProofEdgeInterferenceTranslator {

	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final GhostVariableManager mGhostVariables;
	private final boolean mIncludeInterferencePreState;

	public ProofEdgeInterferenceTranslator(final TransFormulaToInterferencePredicate translator,
			final RelationalPredicatePostcondition postcondition, final GhostVariableManager ghostVariables,
			final boolean includeInterferencePreState) {
		mTranslator = Objects.requireNonNull(translator);
		mPostcondition = Objects.requireNonNull(postcondition);
		mGhostVariables = ghostVariables;
		mIncludeInterferencePreState = includeInterferencePreState;
	}

	public IPredicate tryTranslateInterferenceEdge(final String interferingThread, final IcfgLocation sourceLocation,
			final IPredicate sourcePreState, final IcfgEdge edge) {
		final IcfgLocation targetLocation = edge.getTarget();
		final TransFormula tf = edge.getTransformula();
		if (targetLocation == null || tf == null) {
			return null;
		}

		final String forkedThreadId = InterferenceEdgeSemantics.getForkedThreadOrNull(edge);
		final boolean locationChanges = mGhostVariables != null
				&& !mTranslator.isLocationStutterStep(sourceLocation, targetLocation);
		final boolean isInterferenceRelevant = InterferenceEdgeSemantics.modifiesGlobals(tf)
				|| InterferenceEdgeSemantics.isJoinAssigningGlobal(edge) || forkedThreadId != null || locationChanges;
		if (!isInterferenceRelevant) {
			return null;
		}
		if (mIncludeInterferencePreState && sourcePreState == null) {
			return null;
		}

		final IPredicate edgePredicate =
				createTransitionPredicate(interferingThread, sourceLocation, targetLocation, tf, forkedThreadId, edge);
		if (edgePredicate == null) {
			return null;
		}
		if (!mIncludeInterferencePreState) {
			return edgePredicate;
		}
		return withSourcePreState(sourcePreState, edgePredicate);
	}

	private IPredicate createTransitionPredicate(final String interferingThread, final IcfgLocation sourceLocation,
			final IcfgLocation targetLocation, final TransFormula tf, final String forkedThreadId, final IcfgEdge edge) {
		final Set<IProgramVar> additionallyModifiedGlobals = InterferenceEdgeSemantics.getJoinAssignedGlobals(edge);
		if (forkedThreadId != null) {
			final IcfgLocation forkedEntry = mTranslator.getEntryLocation(forkedThreadId);
			if (forkedEntry == null) {
				return null;
			}
			return mTranslator.translateForInterferenceWithFork(tf, interferingThread, sourceLocation, targetLocation,
					forkedThreadId, forkedEntry, additionallyModifiedGlobals);
		}
		return mTranslator.translateForInterference(tf, interferingThread, sourceLocation, targetLocation,
				additionallyModifiedGlobals);
	}

	private IPredicate withSourcePreState(final IPredicate sourcePreState, final IPredicate edgeInterference) {
		final var script = mPostcondition.getManagedScript().getScript();
		final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourcePreState);
		return mPostcondition.getPredicateFactory()
				.newPredicate(SmtUtils.and(script, sharedPreState.getFormula(), edgeInterference.getFormula()));
	}

}
