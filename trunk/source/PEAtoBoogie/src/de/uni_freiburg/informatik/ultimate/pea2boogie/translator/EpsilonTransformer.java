
/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.Arrays;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.RtInconcistencyConditionGenerator;

/**
 *
 * This transformer implements the following transformations for <code>Ndc(A_i,p_i)</code> (see
 * {@link RtInconcistencyConditionGenerator#generateNonDeadlockCondition(de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata[])}).
 *
 * For clock invariants of the form x<c, replace c by c - ε in clock invariants.
 *
 * For guards that contain relation over clock vars x and constants c,
 * <ol>
 * <li>Replace all relations of the form x>=c with x>c and all of the form x<c with x<=c (deprecated)
 * <li>Replace all constants c by c - ε.
 * </ol>
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class EpsilonTransformer {

	private final Rational mEpsilon;
	private final Script mScript;
	private final IReqSymbolTable mReqSymboltable;

	public EpsilonTransformer(final Script script, final Rational epsilon, final IReqSymbolTable reqSymboltable) {
		mEpsilon = epsilon;
		mScript = script;
		mReqSymboltable = reqSymboltable;
	}

	public Term transformGuard(final Term guardTerm) {
		// final Term replacedRelation =
		// new GenericTransformer(EpsilonTransformer::filterAll, this::changeRelation).transform(guardTerm);
		// return new GenericTransformer(EpsilonTransformer::filterAll,
		// this::subtractEpsilon).transform(replacedRelation);

		// TODO: check proof
		return new GenericTransformer(EpsilonTransformer::filterAll, this::subtractEpsilon).transform(guardTerm);
	}

	public Term transformClockInvariant(final Term inv) {
		return new GenericTransformer(EpsilonTransformer::filterLt, this::subtractEpsilon).transform(inv);
	}

	private Term applyTransform(final ApplicationTerm appTerm, final String func, final Term[] args,
			final IFunTransform funTransform) {
		if (args.length != 2) {
			throw new UnsupportedOperationException("not yet implemented");
		}

		assert filterAll(func);

		if (args[0] instanceof ConstantTerm && args[1] instanceof TermVariable) {
			return applyTransform(appTerm, dual(func), new Term[] { args[1], args[0] }, funTransform);
		} else if (args[1] instanceof ConstantTerm && args[0] instanceof TermVariable) {
			final TermVariable tv = (TermVariable) args[0];
			if (mReqSymboltable.getClockVars().contains(tv.getName())) {
				return funTransform.transform(appTerm, func, args);
			}
			return null;
		} else {
			if (Arrays.stream(args).anyMatch(a -> mReqSymboltable.getClockVars().contains(a.toString()))) {
				throw new UnsupportedOperationException("relation not in normal form: " + appTerm);
			}
			return null;
		}
	}

	private static boolean filterAll(final String func) {
		switch (func) {
		case "<":
		case ">=":
		case "<=":
		case ">":
			return true;
		default:
			return false;
		}
	}

	private static boolean filterLt(final String func) {
		switch (func) {
		case "<":
			return true;
		default:
			return false;
		}
	}

	private static String dual(final String func) {
		switch (func) {
		case "<":
			return ">";
		case ">=":
			return "<=";
		case "<=":
			return ">=";
		case ">":
			return "<";
		default:
			throw new AssertionError();
		}
	}

	@FunctionalInterface
	private interface IFunTransform {
		Term transform(final ApplicationTerm appTerm, final String func, final Term[] args);
	}

	private Term changeRelation(final ApplicationTerm appTerm, final String func, final Term[] args) {
		if (func.equals("<")) {
			return mScript.term("<=", args);
		}
		if (func.equals(">=")) {
			return mScript.term(">", args);
		}
		return null;
	}

	private Term subtractEpsilon(final ApplicationTerm appTerm, final String func, final Term[] args) {
		final Term[] nargs = new Term[args.length];
		nargs[0] = args[0];
		final Rational val = SmtUtils.toRational((ConstantTerm) args[1]);
		final Rational newVal = val.sub(mEpsilon);
		nargs[1] = newVal.toTerm(SmtSortUtils.getRealSort(mScript));
		return mScript.term(func, nargs);
	}

	private final class GenericTransformer extends TermTransformer {
		private final Predicate<String> mPred;
		private final IFunTransform mFun;

		public GenericTransformer(final Predicate<String> pred, final IFunTransform funTransform) {
			mPred = pred;
			mFun = funTransform;
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
			final String func = appTerm.getFunction().getName();
			if (mPred.test(func)) {
				final Term newTerm = applyTransform(appTerm, func, args, mFun);
				if (newTerm != null) {
					setResult(newTerm);
					return;
				}
			}
			super.convertApplicationTerm(appTerm, args);
		}
	}
}