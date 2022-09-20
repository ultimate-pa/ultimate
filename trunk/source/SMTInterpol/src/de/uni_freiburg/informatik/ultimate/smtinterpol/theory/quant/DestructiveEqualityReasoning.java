/*
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral.NegQuantLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.SubstitutionHelper.SubstitutionResult;

/**
 * Apply destructive equality reasoning to a quantified clause.
 * <p>
 * That is, if a quantified clause contains a literal (x != t), every occurrence of x is substituted by t, and the
 * literal is dropped.
 *
 * @author Tanja Schindler
 *
 */
public class DestructiveEqualityReasoning {

	private final QuantifierTheory mQuantTheory;
	private final Clausifier mClausifier;

	private final TermVariable[] mVars;
	private final Literal[] mGroundLits;
	private final QuantLiteral[] mQuantLits;
	private final SourceAnnotation mSource;

	private final Map<TermVariable, Term> mSigma;
	private boolean mIsChanged;

	private DERResult mResult;

	DestructiveEqualityReasoning(final QuantifierTheory quantTheory, final TermVariable[] vars,
			final Literal[] groundLits, final QuantLiteral[] quantLits,
			final SourceAnnotation source) {
		mQuantTheory = quantTheory;
		mClausifier = quantTheory.getClausifier();

		mVars = vars;
		mGroundLits = groundLits;
		mQuantLits = quantLits;
		mSource = source;

		mSigma = new LinkedHashMap<>();
		mIsChanged = false;

		mResult = null;
	}

	/**
	 * Apply destructive equality reasoning.
	 * <p>
	 * If something has changed, the result can be obtained by calling getResult().
	 *
	 * @return true if DER changed something, i.e., a variable has been removed; false otherwise.
	 */
	boolean applyDestructiveEqualityReasoning() {
		collectSubstitution();
		if (!mSigma.isEmpty()) {
			final SubstitutionHelper subsHelper =
					new SubstitutionHelper(mQuantTheory, mGroundLits, mQuantLits, mSource, mSigma);
			final SubstitutionResult subsResult = subsHelper.substituteInClause();
			final Term[] subs = new Term[mVars.length];
			for (int i = 0; i < subs.length; i++) {
				subs[i] = mSigma.containsKey(mVars[i]) ? mSigma.get(mVars[i]) : mVars[i];
			}
			mResult = new DERResult(subs, subsResult);
			mIsChanged = true;
		}
		return mIsChanged;
	}

	/**
	 * Get the result from applying DER if it has changed something.
	 *
	 * @return the result from applying DER on the given clause.
	 */
	DERResult getResult() {
		assert mIsChanged : "Should only be called if DER has changed the clause.";
		return mResult;
	}

	/**
	 * Collect the substitution sigma. Step 1: Go through all literals. For variables x,y,z, and a term t (can be a
	 * variable):<br>
	 * (i) For a literal (x != t), t ground or var, add {z -> t} to sigma if sigma*(x) = z.<br>
	 * (ii) For a literal (x != y), add {z -> x} to sigma if sigma*(y) = z.<br>
	 * First check (i) and only if it does not apply, check (ii).<br>
	 * (iii) For a literal (x != f(y1,...,yn)), add f(y1,...,yn) to potential substitutions for x if sigma*(x) = z.
	 * <p>
	 * Step 2:<br>
	 * (i) Build sigma := sigma*.<br>
	 * (ii) Find a substitution for all variables without ground substitution, but don't build cycles.
	 */
	private void collectSubstitution() {
		final Map<TermVariable, Term> groundAndVarSubsForVar = new LinkedHashMap<>();
		final Map<TermVariable, List<Term>> potentialSubsForVar = new LinkedHashMap<>();
		// Step 1:
		for (final QuantLiteral qLit : mQuantLits) {
			if (qLit.mIsDERUsable) {
				assert qLit instanceof NegQuantLiteral && qLit.getAtom() instanceof QuantEquality;
				final QuantEquality varEq = (QuantEquality) qLit.mAtom;
				assert varEq.getLhs() instanceof TermVariable;
				final TermVariable var = (TermVariable) varEq.getLhs();
				final Term varRep = findRep(var);
				final Term rhs = varEq.getRhs();
				if (varRep instanceof TermVariable) {
					if (rhs.getFreeVars().length == 0 || rhs instanceof TermVariable) { // (i)
						groundAndVarSubsForVar.put((TermVariable) varRep, rhs);
					} else { // (iii)
						if (!potentialSubsForVar.containsKey(varRep)) {
							potentialSubsForVar.put(var, new ArrayList<Term>());
						}
						potentialSubsForVar.get(var).add(rhs);
					}
				} else {
					if (rhs instanceof TermVariable) {
						final Term otherVarRep = findRep((TermVariable) rhs);
						if (otherVarRep instanceof TermVariable) { // (ii)
							groundAndVarSubsForVar.put((TermVariable) otherVarRep, varRep);
						}
					}
				}
			}
		}

		// Step 2 (i):
		if (!groundAndVarSubsForVar.isEmpty()) {
			final Set<TermVariable> visited = new HashSet<>();
			for (final TermVariable var : groundAndVarSubsForVar.keySet()) {
				if (!visited.contains(var)) {
					final Set<TermVariable> varsWithSameSubs = new LinkedHashSet<>();
					Term subs = var;
					while (subs instanceof TermVariable && !visited.contains(subs)) {
						visited.add((TermVariable) subs);
						varsWithSameSubs.add((TermVariable) subs);
						if (groundAndVarSubsForVar.containsKey(subs)) {
							subs = groundAndVarSubsForVar.get(subs);
						}
					}
					for (final TermVariable equiVar : varsWithSameSubs) {
						if (equiVar != subs) { // Don't use a substitution x->x.
							mSigma.put(equiVar, subs);
							if (!(subs instanceof TermVariable)) {
								potentialSubsForVar.remove(equiVar);
							}
						}
					}
				}
			}
		}
		// Step 2 (ii):
		if (!potentialSubsForVar.isEmpty()) {
			for (final TermVariable var : potentialSubsForVar.keySet()) {
				final Term varRep = findRep(var);
				if (varRep instanceof TermVariable) {
					for (final Term potentialSubs : potentialSubsForVar.get(var)) {
						if (!hasCycle(var, potentialSubs)) {
							final FormulaUnLet unletter = new FormulaUnLet();
							unletter.addSubstitutions(mSigma);
							Term subs = unletter.unlet(potentialSubs);
							final IProofTracker tracker = mClausifier.getTracker();
							subs = tracker.getProvedTerm(mClausifier.getTermCompiler().transform(subs));
							mSigma.put((TermVariable) varRep, subs);
						}
					}
				}
			}
		}
	}

	/**
	 * For a variable x, find sigma*(x).
	 *
	 * We define sigma(x) = x if x has no substitution so far.
	 *
	 * @return The Term sigma*(x).
	 */
	private Term findRep(final TermVariable var) {
		TermVariable nextVarRep = var;
		while (true) {
			if (mSigma.containsKey(nextVarRep)) {
				final Term subs = mSigma.get(nextVarRep);
				if (subs instanceof TermVariable) {
					nextVarRep = (TermVariable) subs;
				} else {
					return subs;
				}
			} else {
				return nextVarRep;
			}
		}
	}

	/**
	 * For a variable x and a potential substitution sigma containing variables check if there is a cycle in sigma.
	 */
	private boolean hasCycle(final TermVariable var, final Term potentialSubs) {
		assert potentialSubs.getFreeVars().length > 0;
		for (final TermVariable dependentVar : potentialSubs.getFreeVars()) {
			if (Arrays.asList(findRep(dependentVar).getFreeVars()).contains(var)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * This class is used to collect the result from applying Destructive Equality Reasoning on a clause. It contains
	 * information about the substituted clause term, the simplified substituted term, and the corresponding literals,
	 * as well as the terms used for the substitution.
	 *
	 */
	public static class DERResult extends SubstitutionResult {
		private final Term[] mSubs;

		protected DERResult(final Term[] subs, final SubstitutionResult subsRes) {
			super(subsRes.mSubstituted, subsRes.mSimplified, subsRes.mGroundLits, subsRes.mQuantLits);
			mSubs = subs;
		}

		public Term[] getSubs() {
			return mSubs;
		}
	}
}
