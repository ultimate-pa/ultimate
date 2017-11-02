/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Nontermination argument in form of an infinite program execution.
 *
 * It is composed of
 * <ul>
 * <li>an initial state at the begin of the lasso,
 * <li>a state at first visit of the honda,
 * <li>a list of rays of the loop's transition polyhedron, and
 * <li>a list of discount factors lambda and mu.
 * </ul>
 *
 * The infinite execution described by this nontermination argument is
 *
 * <pre>
 * state_init,
 * state_honda,
 * state_honda + ray_1 + ... + ray_n,
 * state_honda + (1 + lambda_1) ray_1 + (1 + lambda_2 + mu_1) ray_2 + ... + (1 + lambda_n + nu_(n-1)) ray_n,
 * ...
 * </pre>
 *
 * The general form is x + Y*(sumi J^i)*1 where
 * <ul>
 * <li>x is the initial state state_init
 * <li>Y is a matrix with the rays as columns
 * <li>J is a matrix with lamnbda_i on the diagonal and mu_i on the upper subdiagonal
 * <li>1 is a column vector of ones
 * </ul>
 *
 * This implementation nontermination argument is highly tailored to the nontermination arguments that the LassoRanker
 * plugin discovers and is unlikely to be useful anywhere else.
 *
 * @author Jan Leike
 * @param <P>
 *            program position class
 */
public class GeometricNonTerminationArgumentResult<P extends IElement, E> extends LassoShapedNonTerminationArgument<P, E> {
	/**
	 * How many steps the infinite execution should be schematically unwinded
	 */
	private final static int SCHEMATIC_EXECUTION_LENGTH = 3;
	private final static boolean ALTERNATIVE_LONG_DESCRIPTION = true;

	private final Map<E, Rational> mStateInit;
	private final Map<E, Rational> mStateHonda;
	private final List<Map<E, Rational>> mRays;
	private final List<Rational> mLambdas;
	private final List<Rational> mNus;

	public GeometricNonTerminationArgumentResult(final P position, final String plugin,
			final Map<E, Rational> stateInit, final Map<E, Rational> stateHonda, final List<Map<E, Rational>> rays,
			final List<Rational> lambdas, final List<Rational> nus, final IBacktranslationService translatorSequence,
			final Class<E> exprClazz, final IProgramExecution<P, E> stem, final IProgramExecution<P, E> loop) {
		super(position, plugin, translatorSequence, exprClazz, stem, loop);
		mStateInit = stateInit;
		mStateHonda = stateHonda;
		mRays = rays;
		mLambdas = lambdas;
		mNus = nus;
		assert mRays.size() == mLambdas.size();
	}

	@Override
	public String getShortDescription() {
		return "Nontermination argument in form of an infinite " + "program execution.";
	}

	@Override
	public String getLongDescription() {
		if (ALTERNATIVE_LONG_DESCRIPTION) {
			return alternativeLongDesciption();
		}
		return defaultLongDescription();
	}

	public String defaultLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Nontermination argument in form of an infinite execution\n");
		sb.append(mStateInit);
		assert (SCHEMATIC_EXECUTION_LENGTH > 0);
		final Rational[] geometric_sum = new Rational[mLambdas.size()]; // 1 + lambda_i + mu_(i-1) + ...
		for (int i = 0; i < mLambdas.size(); ++i) {
			geometric_sum[i] = Rational.ZERO;
		}
		for (int j = 0; j < SCHEMATIC_EXECUTION_LENGTH; ++j) {
			final Map<E, String> state = new HashMap<>();
			for (final E var : mStateHonda.keySet()) {
				Rational x = mStateHonda.get(var);
				for (int i = 0; i < mRays.size(); ++i) {
					final Rational y = mRays.get(i).get(var);
					if (y != null) {
						x = x.add(y.mul(geometric_sum[i]));
					}
				}
				state.put(var, x.toString());
			}
			for (int i = mRays.size() - 1; i >= 0; --i) {
				geometric_sum[i] = geometric_sum[i].mul(mLambdas.get(i)).add(Rational.ONE);
				if (i > 0) {
					geometric_sum[i] = geometric_sum[i].add(geometric_sum[i - 1].mul(mNus.get(i - 1)));
				}
			}
			sb.append("\n");
			sb.append(printState(state));
		}
		return sb.toString();
	}

	private String alternativeLongDesciption() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Nontermination argument in form of an infinite execution\n");

		// State 1 (before the honda)
		sb.append("State at position 0 is\n");
		final Map<E, String> statePos0 = new HashMap<>();
		for (final Entry<E, Rational> entry : mStateInit.entrySet()) {
			final E var = entry.getKey();
			final Rational x0 = mStateInit.get(var);
			statePos0.put(var, x0.toString());
		}
		sb.append(printState(statePos0));

		// State 2 (at the honda)
		sb.append("\nState at position 1 is\n");
		final Map<E, String> statePos1 = new HashMap<>();
		for (final Entry<E, Rational> entry : mStateHonda.entrySet()) {
			final E var = entry.getKey();
			final Rational x = mStateHonda.get(var);
			statePos1.put(var, x.toString());
		}
		sb.append(printState(statePos1));

		// Schematic execution afterwards
		sb.append("\nFor i>1, the state at position i is\n");
		final Map<E, String> statePosI = new HashMap<>();
		for (final E var : mStateHonda.keySet()) {
			final StringBuilder sb2 = new StringBuilder();
			final Rational x = mStateHonda.get(var);
			for (int i = 0; i < mRays.size(); ++i) {
				final Rational y = mRays.get(i).get(var);
				if (y != null && !y.equals(Rational.ZERO)) {
					if (sb2.length() > 0) {
						sb2.append(" + ");
					}
					for (int j = 0; j <= i && j < mRays.size(); ++j) {
						boolean ok = true;
						for (int s = i - j; s < i; ++s) {
							if (mNus.get(s).equals(Rational.ZERO)) {
								ok = false;
							}
						}
						if (!ok) {
							continue; // \prod_{s=i-j}^{i-1} mu_s == 0
										// => skip summand
						}
						if (j > 0) {
							sb2.append(" + ");
						}
						final Rational lambda = mLambdas.get(i - j);
						sb2.append(y);

						if (j == 1) {
							sb2.append("*k");
						} else if (j > 1) {
							sb2.append("*binomial(k, " + j + ")");
						}
						if (!lambda.equals(Rational.ONE)) {
							if (j == 0) {
								sb2.append("*" + lambda + "^k");
							} else {
								sb2.append("*" + lambda + "^(k-" + j + ")");
							}
						}
					}
				}
			}
			if (sb2.length() == 0) {
				sb2.append("0");
			}
			statePosI.put(var, x.toString() + " + sum_{k=0}^i " + sb2.toString());
		}
		sb.append(printState(statePosI));
		return sb.toString();
	}
}
