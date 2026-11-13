/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.afa;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class TransFormulaSymmetricDifference<L extends IAction> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;
	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;

	// TODO: maybe it would be better to move this implementation to TransFormulaUtils?
	public TransFormulaSymmetricDifference(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		mServices = services;
		mManagedScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);

	}

	public UnmodifiableTransFormula compute(final L a, final L b) {
		final var compositions = buildCompositions(a, b);
		final var tfAB = compositions.getFirst();
		final var tfBA = compositions.getSecond();

		if (mManagedScript.isLocked()) {
			mLogger.warn("Requesting ManagedScript unlock before constructing transition");
			final boolean unlocked = mManagedScript.requestLockRelease();
			if (!unlocked) {
				mLogger.warn("Failed to unlock ManagedScript. Unable to construct transition.");
				return null; // TODO: maybe do something more useful than returning null
			}
		}
		return buildSymmetricDifference(tfAB, tfBA);
	}

	private Pair<UnmodifiableTransFormula, UnmodifiableTransFormula> buildCompositions(final L a, final L b) {
		final UnmodifiableTransFormula tfA = a.getTransformula();
		final UnmodifiableTransFormula tfB = b.getTransformula();

		// Compose the two transition formulas in both orders.
		final UnmodifiableTransFormula transFormulaAB = compose(tfA, tfB);
		final UnmodifiableTransFormula transFormulaBA = compose(tfB, tfA);

		return new Pair<>(transFormulaAB, transFormulaBA);
	}

	private final UnmodifiableTransFormula compose(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		// no need to do simplification, result is only used in one implication check
		final boolean simplify = false;

		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, simplify, false, false,
				SIMPLIFICATION_TECHNIQUE, Arrays.asList(first, second));
	}

	private final UnmodifiableTransFormula buildSymmetricDifference(final UnmodifiableTransFormula tfAB,
			final UnmodifiableTransFormula tfBA) {
		final var abNotBa = TransFormulaUtils.intersect(mManagedScript, tfAB,
				TransFormulaUtils.negate(tfBA, mManagedScript, mServices));

		final var baNotAb = TransFormulaUtils.intersect(mManagedScript, tfBA,
				TransFormulaUtils.negate(tfAB, mManagedScript, mServices));

		return TransFormulaUtils.parallelComposition(mLogger, mServices, mManagedScript, null, false, true, abNotBa,
				baNotAb);
	}
}
