/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;

/**
 * The {@link EvaluatorLogger} allows the issuing of warning messages without polluting the log.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class EvaluatorLogger {

	private static final String POSSIBLE_LOSS_OF_PRECISION = "Possible loss of precision. Operator ";

	private static final boolean MORE_LOGGING = false;

	private final ILogger mLogger;
	private final Set<UnaryExpression.Operator> mWarningsUnknownUnaryOps;
	private final Set<BinaryExpression.Operator> mWarningsUnknownBinaryOps;
	private final Set<BinaryExpression.Operator> mWarningsOverapproxBinaryOps;

	public EvaluatorLogger(final ILogger logger) {
		mLogger = logger;
		mWarningsUnknownUnaryOps = new HashSet<>(1);
		mWarningsUnknownBinaryOps = new HashSet<>(1);
		mWarningsOverapproxBinaryOps = new HashSet<>(1);
	}

	public void warnUnknownOperator(final UnaryExpression.Operator op) {
		if (!mLogger.isWarnEnabled()) {
			return;
		}
		if (!mWarningsUnknownUnaryOps.add(op)) {
			return;
		}
		mLogger.warn(POSSIBLE_LOSS_OF_PRECISION + op + " is not implemented.");
	}

	public void warnOverapproximatingOperator(final BinaryExpression.Operator op) {
		if (!mLogger.isWarnEnabled()) {
			return;
		}
		if (!mWarningsOverapproxBinaryOps.add(op)) {
			return;
		}
		mLogger.warn(POSSIBLE_LOSS_OF_PRECISION + op + " has no precise implementation.");
	}

	public void warnUnknownOperator(final BinaryExpression.Operator op) {
		if (!mLogger.isWarnEnabled()) {
			return;
		}
		if (!mWarningsUnknownBinaryOps.add(op)) {
			return;
		}
		mLogger.warn(POSSIBLE_LOSS_OF_PRECISION + op + " is not implemented.");
	}

	@SuppressWarnings("unused")
	public void logInverseEvaluation(final Object op, final Object result, final Object... args) {
		if (MORE_LOGGING && mLogger.isDebugEnabled()) {
			logEvaluation("I", op, result, args);
		}
	}

	@SuppressWarnings("unused")
	public void logEvaluation(final Object op, final Object result, final Object... args) {
		if (MORE_LOGGING && mLogger.isDebugEnabled()) {
			logEvaluation("E", op, result, args);
		}
	}

	private void logEvaluation(final String prefix, final Object op, final Object result, final Object... args) {
		final StringBuilder sb = new StringBuilder();
		Arrays.stream(args).forEach(a -> sb.append(' ').append(a));
		mLogger.debug(AbsIntPrefInitializer.DINDENT + prefix + " (" + op + sb + ") = " + result);
	}

	public ILogger getLogger() {
		return mLogger;
	}

}
