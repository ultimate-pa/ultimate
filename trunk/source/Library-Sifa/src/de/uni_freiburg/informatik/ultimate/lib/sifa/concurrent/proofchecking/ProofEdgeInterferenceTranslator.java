/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class ProofEdgeInterferenceTranslator {

	private final TransFormulaToInterferencePredicate mTranslator;
	private final RelationalPredicatePostcondition mPostcondition;
	private final GhostVariableManager mGhostVariables;

	public ProofEdgeInterferenceTranslator(final TransFormulaToInterferencePredicate translator,
			final RelationalPredicatePostcondition postcondition, final GhostVariableManager ghostVariables) {
		mTranslator = Objects.requireNonNull(translator);
		mPostcondition = Objects.requireNonNull(postcondition);
		mGhostVariables = ghostVariables;
	}

	public IPredicate tryTranslateInterferenceEdge(final String interferingThread, final IcfgLocation sourceLocation,
			final IPredicate sourcePreState, final IcfgEdge edge) {
		final IcfgLocation targetLocation = edge.getTarget();
		final TransFormula tf = edge.getTransformula();
		if (targetLocation == null || tf == null) {
			return null;
		}

		final String forkedThreadId = InterferenceUtils.getForkedThreadOrNull(edge);
		final boolean locationChanges = mGhostVariables != null
				&& !mTranslator.isLocationStutterStep(sourceLocation, targetLocation);
		final boolean isInterferenceRelevant =
				InterferenceUtils.hasRelevantInterferenceEffect(edge) || locationChanges;
		if (!isInterferenceRelevant || sourcePreState == null) {
			return null;
		}

		final IPredicate edgePredicate =
				createTransitionPredicate(interferingThread, sourceLocation, targetLocation, tf, forkedThreadId, edge);
		if (edgePredicate == null) {
			return null;
		}
		return withSourcePreState(sourcePreState, edgePredicate);
	}

	private IPredicate createTransitionPredicate(final String interferingThread, final IcfgLocation sourceLocation,
			final IcfgLocation targetLocation, final TransFormula tf, final String forkedThreadId, final IcfgEdge edge) {
		final var additionallyModifiedGlobals = InterferenceUtils.getAdditionalChangedGlobals(edge);
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
