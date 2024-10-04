/*
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * This class provides static auxiliary methods that are useful for several loop
 * acceleration techniques.
 *
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class LoopAccelerationUtils {

	private LoopAccelerationUtils() {
		// do not instantiate
	}

	/**
	 * Method that checks some properties that the result of a loop acceleration
	 * should have and writes logging output if something unexpected happens (e.g.,
	 * SMT solver was unable to perform check). This methods should be used as
	 * argument to an assert statement (in order to perform these costly checks only
	 * if assertions are enabled) and returns always true.
	 *
	 * TODO 20220724 Matthias: Use echo of script consistently in order to ease
	 * debugging.
	 *
	 * @param isAlsoReflexive If set to false, we expect that the accelerationResult
	 *                        is only the transitive closure of the loop. If set to
	 *                        true we expect that the accelerationResult is the
	 *                        reflexive transitive closure of the loop.
	 */
	public static boolean checkSomePropertiesOfLoopAccelerationFormula(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final UnmodifiableTransFormula loopTransFormula,
			final UnmodifiableTransFormula accelerationResult, final boolean isAlsoReflexive) {
		final ILogger logger = services.getLoggingService().getLogger(LoopAccelerationUtils.class);

		mgdScript.getScript().echo(new QuotedObject("Check if formula equivalent to false"));
		if (Util.checkSat(mgdScript.getScript(), accelerationResult.getClosedFormula()) == LBool.UNSAT) {
			logger.warn("Reflexive-transitive closure is equivalent to false");
		}

		final UnmodifiableTransFormula neg = TransFormulaUtils.negate(accelerationResult, mgdScript, services);
		if (isAlsoReflexive) {
			final UnmodifiableTransFormula and = TransFormulaUtils.intersect(mgdScript, loopTransFormula, neg);
			final LBool lbool = Util.checkSat(mgdScript.getScript(), and.getClosedFormula());
			if (lbool == LBool.SAT) {
				throw new AssertionError("Not reflexive");
			} else if (lbool == LBool.UNKNOWN) {
				logger.warn("Insufficient resources to check reflexivity");
			}
		}

		// Check whether input relation R(x,x') is a subset of the result res(x,x').
		// In order to implement this check, we determine if R(x,x') ∧ ¬res(x,x') is
		// satisfiable.
		{
			final UnmodifiableTransFormula and = TransFormulaUtils.intersect(mgdScript, loopTransFormula, neg);
			final LBool lbool = Util.checkSat(mgdScript.getScript(), and.getClosedFormula());
			if (lbool == LBool.SAT) {
				throw new AssertionError("Input relation is not a subset of the result");
			} else if (lbool == LBool.UNKNOWN) {
				logger.warn("Insufficient resources to check whether input relation is a subset of the result");
			}
		}

		{
			// Check whether concatenation of input relation with itself is a subset of the
			// result. In order to implement this check, we determine if R(x,x')⚬R(x,x') ∧
			// ¬res(x,x') is satisfiable.
			final UnmodifiableTransFormula loop2 = TransFormulaUtils.sequentialComposition(logger, services, mgdScript,
					true, true, false, SimplificationTechnique.NONE,
					Arrays.asList(new UnmodifiableTransFormula[] { loopTransFormula, loopTransFormula }));
			final UnmodifiableTransFormula and = TransFormulaUtils.intersect(mgdScript, loop2, neg);
			final LBool lbool = Util.checkSat(mgdScript.getScript(), and.getClosedFormula());
			if (lbool == LBool.SAT) {
				throw new AssertionError("Concatenation of input relation with itself is not a subset of the result");
			} else if (lbool == LBool.UNKNOWN) {
				logger.warn(
						"Insufficient resources to check whether concatenation of input relation with itself is a subset of the result");
			}
		}

		{
			// Check whether result is a subset of the havoced input relation.
			// In order to implement this check, we determine if res(x,x') ∧
			// ¬havoced(R)(x,x') is satisfiable.
			final UnmodifiableTransFormula guardedHavoc = TransFormulaUtils.computeGuardedHavoc(loopTransFormula,
					mgdScript, services, false);
			final UnmodifiableTransFormula negated;
			if (isAlsoReflexive) {
				final UnmodifiableTransFormula reflexiveClosure = TransFormulaBuilder.getTrivialTransFormula(mgdScript);
				final UnmodifiableTransFormula guardedHavocOrReflexiveClosure = TransFormulaUtils.parallelComposition(
						logger, services, mgdScript, null, false,
						false, guardedHavoc, reflexiveClosure);
				negated = TransFormulaUtils.negate(guardedHavocOrReflexiveClosure, mgdScript, services);
			} else {
				negated = TransFormulaUtils.negate(guardedHavoc, mgdScript, services);
			}
			final UnmodifiableTransFormula and = TransFormulaUtils.intersect(mgdScript, accelerationResult, negated);
			final LBool lbool = Util.checkSat(mgdScript.getScript(), and.getClosedFormula());
			if (lbool == LBool.SAT) {
				throw new AssertionError("Result is not a subset of the input relation's guarded havoc");
			} else if (lbool == LBool.UNKNOWN) {
				logger.warn(
						"Insufficient resources to check whether result is a subset of the input relation's guarded havoc");
			}
		}
		return true;
	}
}