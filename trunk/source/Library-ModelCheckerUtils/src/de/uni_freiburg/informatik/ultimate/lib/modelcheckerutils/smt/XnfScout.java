/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.CondisTermTransducer;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class XnfScout extends CondisTermTransducer<XnfScout.Result> {

	public enum Adk { ATOM, DISJUNCTION, CONJUNCTION }

	@Override
	protected Result transduceAtom(final Term term) {
		return new Result(Adk.ATOM, Arrays.asList(new Integer[] { 1 }));
	}

	@Override
	protected Result transduceConjunction(final List<Result> transducedArguments) {
		final List<Integer> result = new ArrayList<>();
		for (final Result input : transducedArguments) {
			if (input.getAdk() == Adk.ATOM) {
				result.add(1);
			} else if (input.getAdk() == Adk.DISJUNCTION) {
				result.addAll(applyDistributivity(input.getDualJuncts()));
			} else {
				throw new AssertionError("expected conjuntion-disjunction alternation");
			}
		}
		return new Result(Adk.CONJUNCTION, result);
	}

	@Override
	protected Result transduceDisjunction(final List<Result> transducedArguments) {
		final List<Integer> result = new ArrayList<>();
		for (final Result input : transducedArguments) {
			if (input.getAdk() == Adk.ATOM) {
				result.add(1);
			} else if (input.getAdk() == Adk.CONJUNCTION) {
				result.addAll(applyDistributivity(input.getDualJuncts()));
			} else {
				throw new AssertionError("expected conjuntion-disjunction alternation");
			}
		}
		return new Result(Adk.DISJUNCTION, result);
	}

	private static List<Integer> applyDistributivity(final List<Integer> inputXnf) {
		final int product = inputXnf.stream().reduce(Integer.valueOf(1), (x, y) -> (x * y));
		final List<Integer> result = new ArrayList<>(product);
		for (int i=0; i<product; i++) {
			result.add(inputXnf.size());
		}
		return result;
	}


	public static class Result {
		private final Adk mAdk;
		private final List<Integer> mDualJuncts;
		public Result(final Adk adk, final List<Integer> dualJuncts) {
			super();
			mAdk = adk;
			mDualJuncts = dualJuncts;
		}
		public Adk getAdk() {
			return mAdk;
		}
		public List<Integer> getDualJuncts() {
			return mDualJuncts;
		}
		@Override
		public String toString() {
			return mAdk.toString() + mDualJuncts.toString();
		}




	}
}
