/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.GeometricNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.InfiniteFixpointRepetition;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class NonterminationArgumentStatistics implements ICsvProviderProvider<String> {
	private final String mNtar;
	private final boolean mLambdaZero;
	private final boolean mGEVZero;
	private final int mNumberOfGevs;

	public NonterminationArgumentStatistics(final NonTerminationArgument nta) {
		if (nta instanceof GeometricNonTerminationArgument) {
			final GeometricNonTerminationArgument gnta = (GeometricNonTerminationArgument) nta;
			mNumberOfGevs = computeNumberOfGevs(((GeometricNonTerminationArgument) nta).getGEVs());
			boolean lambdaZero = true;
			boolean gevZero = true;
			final List<Rational> lambdas = gnta.getLambdas();
			for (int i = 0; i < gnta.getNumberOfGEVs(); ++i) {
				lambdaZero &= gnta.getLambdas().get(i).numerator().equals(BigInteger.ZERO);
				gevZero &= isZero(gnta.getGEVs().get(i));
			}

			mLambdaZero = lambdaZero;
			mGEVZero = gevZero;
			mNtar = (isFixpoint() ? "Fixpoint " : "Unbounded Execution ") + mNumberOfGevs + "GEVs " + "Lambdas: "
					+ lambdas + " Mus: " + gnta.getNus();
		} else if (nta instanceof InfiniteFixpointRepetition) {
			mNtar = "Fixpoint";
			mLambdaZero = true;
			mGEVZero = true;
			mNumberOfGevs = 0;
		} else {
			throw new IllegalArgumentException("unknown NonTerminationArgument");
		}
	}
	
	private int computeNumberOfGevs(final List<Map<IProgramVar, Rational>> gevs) {
		return (int) gevs.stream().filter(x -> x.entrySet().stream().anyMatch(y -> !y.getValue().equals(Rational.ZERO)))
				.count();
	}

	private boolean isFixpoint() {
		return mLambdaZero || mGEVZero;
	}

	/**
	 * Return true iff all coefficients of generalized eigenvector are zero.
	 */
	private boolean isZero(final Map<IProgramVar, Rational> gev) {
		for (final Entry<IProgramVar, Rational> entry : gev.entrySet()) {
			if (!entry.getValue().numerator().equals(BigInteger.ZERO)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public ICsvProvider<String> createCsvProvider() {
		return new SimpleCsvProvider<>(Arrays.asList(new String[] { "nta" }));
	}

	@Override
	public String toString() {
		return mNtar;
	}

}
