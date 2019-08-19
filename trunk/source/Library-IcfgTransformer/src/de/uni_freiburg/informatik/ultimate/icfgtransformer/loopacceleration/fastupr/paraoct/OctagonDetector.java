/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class OctagonDetector extends NonRecursive {

	private final HashSet<Term> mCheckedTerms;
	private final HashSet<Term> mSubTerms;
	private final HashSet<TermVariable> mCurrentVars;
	private final boolean mOctagon;
	private boolean mIsOctTerm;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	public OctagonDetector(ILogger logger, ManagedScript managedScript, IUltimateServiceProvider services) {
		super();
		mLogger = logger;
		mCheckedTerms = new HashSet<>();
		mSubTerms = new HashSet<>();
		mCurrentVars = new HashSet<>();
		mOctagon = true;
		mManagedScript = managedScript;
		mServices = services;
	}

	private static class ConjunctionWalker implements NonRecursive.Walker {

		private final Term mTerm;

		public ConjunctionWalker(Term t) {
			mTerm = t;
		}

		@Override
		public void walk(NonRecursive engine) {
			((OctagonDetector) engine).addConjunctTerms(mTerm);
		}

	}

	private static class OctagonDetectionWalker implements NonRecursive.Walker {

		private final Term mTerm;

		OctagonDetectionWalker(Term t) {
			mTerm = t;
		}

		@Override
		public void walk(NonRecursive engine) {
			((OctagonDetector) engine).check(mTerm);

		}

	}

	/**
	 * Returns a Set of conjunct subterms.
	 *
	 * @param t
	 *            The Term to split
	 * @return Set of Subterms
	 */
	public Set<Term> getConjunctSubTerms(Term t) {
		final Term cnfRelation = SmtUtils.toCnf(mServices, mManagedScript, t,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mCheckedTerms.clear();
		run(new ConjunctionWalker(cnfRelation));
		return mSubTerms;
	}

	private void addConjunctTerms(Term t) {
		mLogger.debug("Current Term:" + t.toString());

		if (mCheckedTerms.contains(t)) {
			mLogger.debug("Already checked");
			return;
		}

		if (t instanceof ApplicationTerm) {
			mLogger.debug("ApplicationTerm");
			final ApplicationTerm aT = (ApplicationTerm) t;
			if ((aT).getFunction().getName().compareTo("and") == 0) {
				mCheckedTerms.add(t);
				mLogger.debug("> with function name = " + aT.getFunction().getName());

				for (final Term arg : (aT).getParameters()) {
					enqueueWalker(new ConjunctionWalker(arg));
				}
				return;
			}
		}

		mLogger.debug("Other Term or other Application Term");
		mSubTerms.add(t);
		mCheckedTerms.add(t);
	}

	/**
	 * Checks if a given Term t is a valid Term in the conjunction of an
	 * Octagon.
	 *
	 * @param t
	 *            The Term to check.
	 * @return TRUE if the given term is a valid OctTerm.
	 */
	public boolean isOctTerm(Term t) {
		mCheckedTerms.clear();
		mIsOctTerm = true;
		mCurrentVars.clear();
		run(new OctagonDetectionWalker(t));
		mLogger.debug(mIsOctTerm ? "Term is Oct" : "Term is NOT Oct");
		return mIsOctTerm;
	}

	private void check(Term t) {
		if (!mIsOctTerm) {
			return;
		}

		mLogger.debug("Checking Term:" + t.toString());

		if (t instanceof TermVariable) {
			mCurrentVars.add((TermVariable) t);
			if (mCurrentVars.size() > 2) {
				mIsOctTerm = false;
			}
		} else if (t instanceof ApplicationTerm) {
			final ApplicationTerm aT = (ApplicationTerm) t;
			final String functionName = aT.getFunction().getName();
			final List<String> validNames = Arrays.asList("<=", "<", ">", ">=", "=", "+");
			if (validNames.contains(functionName)) {
				for (final Term arg : aT.getParameters()) {
					enqueueWalker(new OctagonDetectionWalker(arg));
				}
			} else {
				mIsOctTerm = false;
				return;
			}
		} else if (t instanceof ConstantTerm) {
			return;
		} else if (t instanceof AnnotatedTerm) {
			enqueueWalker(new OctagonDetectionWalker(((AnnotatedTerm) t).getSubterm()));
		} else {
			mIsOctTerm = false;
			return;
		}

	}

	/**
	 * Clears the set of checked terms.
	 */
	public void clearChecked() {
		mCheckedTerms.clear();
	}

	public Set<Term> getSubTerms() {
		return mSubTerms;
	}

	public boolean isOctagon() {
		return mOctagon;
	}
}
