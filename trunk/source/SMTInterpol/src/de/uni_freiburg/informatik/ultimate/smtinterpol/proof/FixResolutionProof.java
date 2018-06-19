/*
 * Copyright (C) 2009-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Fix a resolution proof. This makes sure that for every application of a resolution rule, (1) the primary clause
 * contains the negated pivot and the antecedent contains the negated pivot and (2) no clause contains a literal and its
 * negation.
 *
 * @author Jochen Hoenicke
 */
public class FixResolutionProof extends NonRecursive {

	/*
	 * This class uses a non-recursive iteration through the proof tree. The main type in a proof tree is the sort
	 * {@literal @}Proof. Each term of this sort proves a clause and the main task of this code is to compute the proven
	 * formula. The whole proof term should prove the empty clause.
	 *
	 * The main idea of this non-recursive algorithm is to push a proof walker for the {@literal @}Proof terms on the
	 * todo stack, which will push the proved term of type Bool onto the result stack mStackResults. We only handle the
	 * propositional part of the proof, so we only handle resolution steps, clause, asserted and lemmas. For each of
	 * these we call the corresponding walk function, which computes (or looks up) the clause and creates a proof info.
	 * For resolution steps it may also simplify the resolution proof and return the fixed up proof.
	 */

	/**
	 * The main proof walker that handles a term of sort {@literal @}Proof. It just calls the walk function.
	 */
	static class ProofWalker implements Walker {
		final ApplicationTerm mTerm;

		public ProofWalker(final Term term) {
			assert term.getSort().getName().equals("@Proof");
			mTerm = (ApplicationTerm) term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((FixResolutionProof) engine).walk(mTerm);
		}
	}

	/**
	 * The proof walker that handles a {@literal @}res application term after its arguments are converted. It just calls
	 * the walkResolution function.
	 */
	static class ResolutionWalker implements Walker {
		final ApplicationTerm mTerm;

		public ResolutionWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals("@res");
			mTerm = term;
		}

		public void enqueue(final FixResolutionProof engine) {
			/*
			 * The resolution rule.
			 *
			 * This function is expected to have as first argument the main clause. The other parameters are clauses
			 * annotated with a pivot literal, on which they are resolved.
			 */
			/* enqueue this object first, so it gets executed last */
			engine.enqueueWalker(this);
			/* now enqueue proof walkers for the subproofs in reverse order */
			final Term[] params = mTerm.getParameters();
			for (int i = params.length - 1; i >= 1; i--) {
				final AnnotatedTerm pivotClause = (AnnotatedTerm) params[i];
				engine.enqueueWalker(new ProofWalker(pivotClause.getSubterm()));
			}
			engine.enqueueWalker(new ProofWalker(params[0]));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FixResolutionProof checker = (FixResolutionProof) engine;

			/* pop the proof infos for the children of this node */
			final ProofInfo[] subProofs = new ProofInfo[mTerm.getParameters().length];
			for (int i = subProofs.length - 1; i >= 1; i--) {
				subProofs[i] = checker.stackPop();
			}
			subProofs[0] = checker.stackPop();
			/* walk the resolution node and push the result */
			checker.stackPush(checker.walkResolution(mTerm, subProofs), mTerm);
		}
	}

	/**
	 * The proof info computed for every node of the proof dag. This stores the clause and the simplified proof.
	 * 
	 * If the proof computes a tautology (a clause with a literal appearing both positively and negatively), this is
	 * marked by setting both fields to null.
	 */
	static class ProofInfo {
		Term mResultProof;
		Term[] mClause;

		public ProofInfo(Term result, Term[] clause) {
			mResultProof = result;
			mClause = clause;
		}

		public ProofInfo() {
			mResultProof = null;
			mClause = null;
		}

		public boolean isTrue() {
			return mResultProof == null;
		}

		public Term getResultingProof() {
			return mResultProof;
		}

		public Term[] getClause() {
			return mClause;
		}
	}

	/**
	 * The proof cache. It maps each converted proof to the boolean term it proves.
	 */
	HashMap<Term, ProofInfo> mCacheConv;

	/**
	 * The stack containing the transformed proofs.
	 */
	Stack<ProofInfo> mProofStack = new Stack<>();

	/**
	 * Create a proof checker.
	 *
	 * @param script
	 *            An SMT2 script.
	 * @param logger
	 *            The logger where errors are reported.
	 */
	public FixResolutionProof() {
	}

	/**
	 * Fix a resolution proof. This makes sure that for every application of a resolution rule, (1) the primary clause
	 * contains the negated pivot and the antecedent contains the negated pivot and (2) no clause contains a literal and
	 * its negation.
	 *
	 * @param proof
	 *            the proof to fix.
	 * @return the fixed proof.
	 */
	public Term fix(Term proof) {
		final FormulaUnLet unletter = new FormulaUnLet();

		// Initializing the proof-checker-cache
		mCacheConv = new HashMap<>();
		// Now non-recursive:
		proof = unletter.unlet(proof);
		run(new ProofWalker(proof));

		assert mProofStack.size() == 1 && mProofStack.peek().getClause().length == 0;
		return mProofStack.pop().getResultingProof();
	}

	/**
	 * The proof walker. This takes a proof term and pushes the proven formula on the result stack. It also checks the
	 * proof cache to prevent running over the same term twice.
	 *
	 * @param proofTerm
	 *            The proof term. Its sort must be {@literal @}Proof.
	 */
	void walk(final ApplicationTerm proofTerm) {
		/* Check the cache, if the unfolding step was already done */
		if (mCacheConv.containsKey(proofTerm)) {
			mProofStack.push(mCacheConv.get(proofTerm));
			return;
		}

		/* Get the function and parameters */
		final String rulename = proofTerm.getFunction().getName();

		/* Look at the rule name and treat each different */
		switch (rulename) {
		case "@res":
			new ResolutionWalker(proofTerm).enqueue(this);
			break;

		case "@lemma":
			stackPush(walkLemma(proofTerm), proofTerm);
			break;

		case "@clause":
			stackPush(walkClause(proofTerm), proofTerm);
			break;

		default:
			throw new AssertionError("Unknown proof rule " + rulename + ".");
		}
	}

	/* === Theory lemmas === */

	/**
	 * Handle a lemma rule. This doesn't simplify anything and just parses the clause and returns it together with the
	 * original proof.
	 *
	 * @param lemmaApp
	 *            The {@literal @}lemma application.
	 */
	ProofInfo walkLemma(final ApplicationTerm lemmaApp) {
		/*
		 * The argument of the @lemma application is a single clause annotated with the lemma type, which has as object
		 * all the necessary annotation. For example (@lemma (! (or (not (= a b)) (not (= b c)) (= a c)) :CC ((= a c)
		 * :path (a b c))))
		 */
		final AnnotatedTerm annTerm = (AnnotatedTerm) lemmaApp.getParameters()[0];
		final Term lemma = annTerm.getSubterm();
		ProofInfo info = new ProofInfo(lemmaApp, termToClause(lemma));
		return info;
	}

	/**
	 * Handle a clause rule. This doesn't simplify anything and just extracts the clause and returns it together with
	 * the original proof.
	 *
	 * @param lemmaApp
	 *            The {@literal @}lemma application.
	 */
	ProofInfo walkClause(final ApplicationTerm clauseApp) {
		Term provedClause = clauseApp.getParameters()[1];
		if (provedClause instanceof AnnotatedTerm) {
			final Annotation[] annot = ((AnnotatedTerm) provedClause).getAnnotations();
			if (annot.length == 1 && annot[0].getKey().equals(":input")) {
				/* newer version of proof producer adds :input annotation to @clause for interpolator */
				provedClause = ((AnnotatedTerm) provedClause).getSubterm();
			}
		}

		ProofInfo info = new ProofInfo(clauseApp, termToClause(provedClause));
		return info;
	}

	/**
	 * Handle the resolution rule.
	 *
	 * @param resApp
	 *            The <code>{@literal @}res</code> application from the original proof.
	 * @param subProofs
	 *            The proof infos for the arguments of the resolution node (in the same order).
	 */
	ProofInfo walkResolution(final ApplicationTerm resApp, final ProofInfo[] subProofs) {
		final Theory theory = resApp.getTheory();
		/*
		 * allDisjuncts is the currently computed resolution result.
		 */
		final HashSet<Term> allDisjuncts = new HashSet<Term>();
		/*
		 * newResolutionArgs are the new arguments for this resolution node.
		 */
		final ArrayList<Term> newResolutionArgs = new ArrayList<>();

		/* changed is set, if we changed something */
		boolean changed = false;

		if (subProofs[0].isTrue()) {
			changed = true;
		} else {
			/* Get the disjuncts of the first argument. */
			allDisjuncts.addAll(Arrays.asList(subProofs[0].getClause()));
			newResolutionArgs.add(subProofs[0].getResultingProof());
			changed = subProofs[0].getResultingProof() != resApp;
		}

		/* Resolve the other clauses */
		for (int i = 1; i < subProofs.length; i++) {
			if (subProofs[i].isTrue()) {
				/* the antecedent is a tautology and should be removed */
				changed = true;
				continue;
			}
			final AnnotatedTerm pivotPlusProof = (AnnotatedTerm) resApp.getParameters()[i];

			assert pivotPlusProof.getAnnotations().length == 1
					&& pivotPlusProof.getAnnotations()[0].getKey() == ":pivot";

			if (newResolutionArgs.isEmpty()) {
				/* Previous steps were tautologies and were removed. The antecedent is the new primary */
				allDisjuncts.addAll(Arrays.asList(subProofs[i].getClause()));
				newResolutionArgs.add(subProofs[i].getResultingProof());
				changed = true;
				continue;
			}

			final Term pivot = (Term) pivotPlusProof.getAnnotations()[0].getValue();
			/* Check if antecedent is necessary (negated pivot in primary) */
			if (!allDisjuncts.remove(negate(pivot))) {
				changed = true;
				continue;
			}

			/*
			 * For each clause check for the pivot and add all other literals.
			 */
			final Term[] clause = subProofs[i].getClause();
			boolean pivotFound = false;
			boolean isTautology = false;
			for (final Term t : clause) {
				if (t == pivot) {
					pivotFound = true;
				} else {
					if (allDisjuncts.contains(negate(t))) {
						/* allDisjuncts is a tautology */
						isTautology = true;
						break;
					}
					allDisjuncts.add(t);
				}
			}

			if (isTautology) {
				/* this resolution step produces a tautology.  Remove all steps so far */
				newResolutionArgs.clear();
				allDisjuncts.clear();
				changed = true;
			} else if (pivotFound) {
				/* normal resolution step; add the antecedent and check if there are changes */
				if (pivotPlusProof.getSubterm() == subProofs[i].getResultingProof()) {
					newResolutionArgs.add(pivotPlusProof);
				} else {
					newResolutionArgs.add(theory.annotatedTerm(pivotPlusProof.getAnnotations(), 
							subProofs[i].getResultingProof()));
					changed = true;
				}
			} else {
				/* primary is unnecessary (pivot not in antecedent) */
				allDisjuncts.clear();
				newResolutionArgs.clear();
				allDisjuncts.addAll(Arrays.asList(subProofs[i].getClause()));
				newResolutionArgs.add(subProofs[i].getResultingProof());
				changed = true;
			}
		}

		if (newResolutionArgs.isEmpty()) {
			/* the whole resolution node produced a tautology */
			return new ProofInfo();
		}
		/* compute the resulting clause */
		Term[] newClause = allDisjuncts.toArray(new Term[allDisjuncts.size()]);
		if (!changed) {
			/* if nothing changes, return the original proof */
			assert resApp == theory.term("@res", newResolutionArgs.toArray(new Term[newResolutionArgs.size()]));
			return new ProofInfo(resApp, newClause);
		}
		if (newResolutionArgs.size() == 1) {
			/* if only one antecedent survived, the @res node should be omitted */
			return new ProofInfo(newResolutionArgs.get(0), newClause);
		}
		/* compute the new resolution proof and return it */
		Term[] resArgs = newResolutionArgs.toArray(new Term[newResolutionArgs.size()]);
		return new ProofInfo(theory.term("@res", resArgs), newClause);
	}

	/* === Auxiliary functions === */

	void stackPush(ProofInfo info, final ApplicationTerm keyTerm) {
		mCacheConv.put(keyTerm, info);
		mProofStack.push(info);
	}

	ProofInfo stackPop() {
		return mProofStack.pop();
	}

	/**
	 * Convert a clause term into an Array of terms, one entry for each disjunct. This also handles singleton and empty
	 * clause correctly.
	 *
	 * @param clauseTerm
	 *            The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private Term[] termToClause(final Term clauseTerm) {
		assert clauseTerm != null && clauseTerm.getSort().getName() == "Bool";
		if (isApplication("or", clauseTerm)) {
			return ((ApplicationTerm) clauseTerm).getParameters();
		} else if (isApplication("false", clauseTerm)) {
			return new Term[0];
		} else {
			/* in all other cases, this is a singleton clause. */
			return new Term[] { clauseTerm };
		}
	}

	/**
	 * Negate a term, avoiding double negation. If formula is (not x) it returns x, otherwise it returns (not formula).
	 *
	 * @param formula
	 *            the formula to negate.
	 * @return the negated formula.
	 */
	public Term negate(final Term formula) {
		if (isApplication("not", formula)) {
			return ((ApplicationTerm) formula).getParameters()[0];
		}
		return formula.getTheory().term("not", formula);
	}

	/**
	 * Checks if a term is an application of an internal function symbol.
	 *
	 * @param funcSym
	 *            the expected function symbol.
	 * @param term
	 *            the term to check.
	 * @return true if term is an application of funcSym.
	 */
	boolean isApplication(final String funcSym, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (func.isIntern() && func.getName().equals(funcSym)) {
				return true;
			}
		}
		return false;
	}
}
