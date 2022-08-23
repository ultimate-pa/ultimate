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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.CondisDepthCodeGenerator.CondisDepthCode;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO 2020025 Matthias: Revise and add documentation. Because of the SMT-COMP
 * deadline, I committed this without documentation or code review.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class CondisDepthCodeGenerator extends CondisTermTransducer<CondisDepthCode> {

	public enum Adk {
		ATOM, DISJUNCTION, CONJUNCTION;

		public String getSymbol() {
			final String result;
			switch (this) {
			case ATOM:
				result = this.toString();
				break;
			case CONJUNCTION:
				result = "∧";
				break;
			case DISJUNCTION:
				result = "∨";
				break;
			default:
				throw new AssertionError("unknown value " + this);
			}
			return result;
		}
	}

	/**
	 * Do not instantiate. Use method {@link CondisDepthCode::of} instead.
	 */
	private CondisDepthCodeGenerator() {
	}

	@Override
	protected CondisDepthCode transduceAtom(final Term term) {
		return new CondisDepthCode(Adk.ATOM, Arrays.asList(new Integer[] { 1 }));
	}

	@Override
	protected CondisDepthCode transduceConjunction(final ApplicationTerm originalTerm,
			final List<CondisDepthCode> transducedArguments) {
		List<Integer> tmp = new ArrayList<>();
		for (final CondisDepthCode input : transducedArguments) {
			if (input.getAdk() == Adk.ATOM || input.getAdk() == Adk.DISJUNCTION) {
				tmp = computeMaximum(tmp, input.getDualJuncts());
			} else {
				throw new AssertionError("expected conjunction-disjunction alternation");
			}
		}
		final List<Integer> result = new ArrayList<>();
		result.add(transducedArguments.size());
		result.addAll(tmp);
		return new CondisDepthCode(Adk.CONJUNCTION, result);
	}

	@Override
	protected CondisDepthCode transduceDisjunction(final ApplicationTerm originalTerm,
			final List<CondisDepthCode> transducedArguments) {
		List<Integer> tmp = new ArrayList<>();
		for (final CondisDepthCode input : transducedArguments) {
			if (input.getAdk() == Adk.ATOM || input.getAdk() == Adk.CONJUNCTION) {
				tmp = computeMaximum(tmp, input.getDualJuncts());
			} else {
				throw new AssertionError("expected conjunction-disjunction alternation");
			}
		}
		final List<Integer> result = new ArrayList<>();
		result.add(transducedArguments.size());
		result.addAll(tmp);
		return new CondisDepthCode(Adk.DISJUNCTION, result);
	}

	private static List<Integer> computeMaximum(final List<Integer> list1, final List<Integer> list2) {
		List<Integer> larger;
		List<Integer> smaller;
		if (list1.size() >= list2.size()) {
			larger = list1;
			smaller = list2;
		} else {
			larger = list2;
			smaller = list1;
		}
		for (int i = 0; i < smaller.size(); i++) {
			larger.set(i, Integer.max(larger.get(i), smaller.get(i)));
		}
		return larger;
	}

	public static class CondisDepthCode {
		private final Adk mAdk;
		private final List<Integer> mDualJuncts;

		public CondisDepthCode(final Adk adk, final List<Integer> dualJuncts) {
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
			return mAdk.getSymbol() + "-" + mDualJuncts.stream().map(Object::toString).collect(Collectors.joining("-"));
		}

		public static CondisDepthCode of(final Term term) {
			return new CondisDepthCodeGenerator().transduce(term);
		}
	}
}
