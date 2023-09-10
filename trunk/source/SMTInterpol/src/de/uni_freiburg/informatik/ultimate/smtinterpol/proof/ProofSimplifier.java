/*
 * Copyright (C) 2021 University of Freiburg
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

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * This class explains an SMTInterpol proof with oracles using the low-level
 * rules.
 *
 * @author Jochen Hoenicke
 */
public class ProofSimplifier extends TermTransformer {
	/**
	 * The SMT script (mainly used to create terms).
	 */
	Script mSkript;
	/**
	 * The proof rules creator
	 */
	ProofRules mProofRules;
	/**
	 * The logger where errors are reported.
	 */
	LogProxy mLogger;
	private final MinimalProofChecker mChecker;

	private HashMap<FunctionSymbol, LambdaTerm> mAuxDefs;

	private final static String ANNOT_PROVES_CLAUSE = ":proves";
	private final static String ANNOT_PROVED_EQ = ":provedEq";

	/**
	 * Create a proof checker.
	 *
	 * @param script
	 *            An SMT2 script.
	 * @param logger
	 *            The logger where errors are reported.
	 */
	public ProofSimplifier(final Script script) {
		mSkript = script;
		mProofRules = new ProofRules(script.getTheory());
		mLogger = new DefaultLogger();
		mChecker = new MinimalProofChecker(mSkript, new DefaultLogger());
	}

	private Term annotateProvedClause(final Term proof, Annotation annot, final ProofLiteral[] clause) {
		final Object[] clauseAnnot = new Object[clause.length * 2];
		for (int i = 0; i < clause.length; i++) {
			clauseAnnot[2 * i] = clause[i].getPolarity() ? "+" : "-";
			clauseAnnot[2 * i + 1] = clause[i].getAtom();
		}
		return mSkript.annotate(proof, new Annotation(ANNOT_PROVES_CLAUSE, clauseAnnot), annot);
	}

	private Term annotateProved(final Term provedTerm, final Term proof) {
		return mSkript.annotate(proof, new Annotation(ANNOT_PROVED_EQ, provedTerm));
	}

	private Term provedTerm(final AnnotatedTerm annotatedTerm) {
		assert annotatedTerm.getAnnotations()[0].getKey() == ANNOT_PROVED_EQ;
		return (Term) annotatedTerm.getAnnotations()[0].getValue();
	}

	private Term stripAnnotation(final Term term) {
		if (term instanceof AnnotatedTerm && ((AnnotatedTerm) term).getAnnotations()[0].getKey() == ANNOT_PROVED_EQ) {
			return ((AnnotatedTerm) term).getSubterm();
		}
		return term;
	}

	private Term subproof(final AnnotatedTerm annotatedTerm) {
		assert annotatedTerm.getAnnotations()[0].getKey() == ANNOT_PROVED_EQ;
		return annotatedTerm.getSubterm();
	}

	private boolean checkProof(final Term proof, final ProofLiteral[] expectedLits) {
		final ProofLiteral[] actual = mChecker.getProvedClause(mAuxDefs, proof);
		final HashSet<ProofLiteral> expectedSet = new HashSet<>();
		expectedSet.addAll(Arrays.asList(expectedLits));
		assert expectedSet.size() == actual.length;
		for (final ProofLiteral lit : actual) {
			assert expectedSet.contains(lit);
		}
		return true;
	}

	/**
	 * Extend a proof to eliminate not terms from the given candidateTerm
	 *
	 * @param proof
	 *            the current proof
	 * @param candidateTerm
	 *            the literal occurring in the proved clause
	 * @param positive
	 *            true iff the literal is expected to occur positive in the clause
	 * @return the extended proof where the literal is no longer double negated.
	 */
	private Term removeNot(Term proof, Term candidateTerm, boolean positive) {
		while (isApplication("not", candidateTerm)) {
			proof = mProofRules.resolutionRule(candidateTerm, positive ? proof : mProofRules.notIntro(candidateTerm),
					positive ? mProofRules.notElim(candidateTerm) : proof);
			candidateTerm = ((ApplicationTerm) candidateTerm).getParameters()[0];
			positive = !positive;
		}
		return proof;
	}

	private Term convertTermITE(final ProofLiteral[] clause) {
		final int lastPos = clause.length - 1;
		assert clause[lastPos].getPolarity() && isApplication("=", clause[lastPos].getAtom());
		final ApplicationTerm iteEquality = (ApplicationTerm) clause[lastPos].getAtom();
		Term iteTerm = iteEquality.getParameters()[0];
		final Term goal = iteEquality.getParameters()[1];
		final ArrayList<Term> intermediates = new ArrayList<>();
		final ArrayList<Term> proofs = new ArrayList<>();
		final HashMap<Term,ProofLiteral> conditionLits = new HashMap<>();
		for (int i = 0; i < clause.length - 1; i++) {
			conditionLits.put(clause[i].getAtom(), clause[i]);
		}
		while (iteTerm != goal) {
			assert isApplication("ite", iteTerm);
			intermediates.add(iteTerm);
			final Term[] iteParams = ((ApplicationTerm) iteTerm).getParameters();
			Term condition = iteParams[0];
			boolean conditionPositive = true;
			while (isApplication("not", condition)) {
				condition = ((ApplicationTerm) condition).getParameters()[0];
				conditionPositive = !conditionPositive;
			}
			final ProofLiteral clauseLit = conditionLits.get(condition);
			if (conditionPositive == clauseLit.getPolarity()) {
				proofs.add(removeNot(mProofRules.ite2(iteTerm), iteParams[0], true));
				iteTerm = iteParams[2];
			} else {
				proofs.add(removeNot(mProofRules.ite1(iteTerm), iteParams[0], false));
				iteTerm = iteParams[1];
			}
		}
		assert iteTerm == goal;
		if (proofs.size() > 1) {
			final Theory t = goal.getTheory();
			// build transitivity proof
			intermediates.add(goal);
			Term proof = mProofRules.trans(intermediates.toArray(new Term[intermediates.size()]));
			for (int i = 0; i < proofs.size(); i++) {
				final Term eqTerm = t.term("=", intermediates.get(i), intermediates.get(i + 1));
				proof = mProofRules.resolutionRule(eqTerm, proofs.get(i), proof);
			}
			return proof;
		} else {
			assert proofs.size() == 1;
			return proofs.get(0);
		}
	}

	/**
	 * Check if an iteTerm is the ite in the TermITEBound term. A :termITEBound
	 * axiom has the form {@pre (<= (+ iteTerm (- maxValue)) 0)} or {@pre (<= (+
	 * minValue (- iteTerm)) 0)}. The problem is that iteTerm may not be the first
	 * term in the sum and that max/minValue may itself consist of several terms
	 * that are summed, including other ite terms. Here we check that for the given
	 * possibleIteTerm and it's factor in the sum, the sum is either of the firsts
	 * or second form.
	 *
	 * @param sum             The sum, i.e. the left-hand-side of the <= term.
	 * @param possibleIteTerm the candidate ite term. We assume that it is indeed an
	 *                        ite term.
	 * @param factor          the factor of the ite term in the sum. This should be
	 *                        1 or -1.
	 * @return true if the sum is of the correct form.
	 */
	private boolean checkIteinIteBound(final SMTAffineTerm sum, final ApplicationTerm possibleIteTerm,
			final Rational factor) {
		assert isApplication(SMTLIBConstants.ITE, possibleIteTerm);
		Term[] iteArgs = possibleIteTerm.getParameters();
		boolean zeroSeen = false;
		final HashSet<Term> visited = new HashSet<>();
		final ArrayDeque<Term> toCheck = new ArrayDeque<>();
		toCheck.add(iteArgs[2]);
		toCheck.add(iteArgs[1]);
		// Now check for each ti if replacing ti with (ite c t1 t2) in sum results a
		// non-positive constant.
		while (!toCheck.isEmpty()) {
			final Term candidate = toCheck.removeLast();
			if (visited.add(candidate)) {
				if (isApplication("ite", candidate)) {
					// nested ite. push the other branches to toCheck queue
					iteArgs = ((ApplicationTerm) candidate).getParameters();
					toCheck.addLast(iteArgs[1]);
					toCheck.addLast(iteArgs[2]);
				} else {
					// replace (ite c t e) with candidate in sum, by adding
					// (- candidate (ite c t e)) * factor
					final SMTAffineTerm sumWithCandidate = new SMTAffineTerm(candidate);
					sumWithCandidate.add(Rational.MONE, possibleIteTerm);
					sumWithCandidate.mul(factor);
					sumWithCandidate.add(sum);

					// Afterwards the literal should be <= 0, to make the clause true.
					if (!sumWithCandidate.isConstant() || sumWithCandidate.getConstant().signum() > 0) {
						return false;
					}
					if (sumWithCandidate.getConstant().signum() == 0) {
						zeroSeen = true;
					}
				}
			}
		}
		// check that the bound is tight, i.e. one of the sums should be 0.
		return zeroSeen;
	}

	/**
	 * Find the ite in the TermITEBound term. A :termITEBound axiom has the form
	 * {@pre (<= (+ iteTerm (- maxValue)) 0)} or {@pre (<= (+ minValue (- iteTerm))
	 * 0)}. The problem is that iteTerm may not be the first term in the sum and
	 * that max/minValue may itself consist of several terms that are summed,
	 * including other ite terms. We find the right ite term just by trying all
	 * candidates and check if they match.
	 *
	 * @param sum The sum, i.e. the left-hand-side of the <= term.
	 * @return The iteTerm.
	 * @throws AssertionError if there is no candidate ite term.
	 */
	private ApplicationTerm findAndCheckIteinIteBound(final SMTAffineTerm sum) {
		for (final Map.Entry<Term, Rational> entry : sum.getSummands().entrySet()) {
			if (isApplication("ite", entry.getKey()) && entry.getValue().abs() == Rational.ONE) {
				final ApplicationTerm iteTerm = (ApplicationTerm) entry.getKey();
				if (checkIteinIteBound(sum, iteTerm, entry.getValue())) {
					return iteTerm;
				}
			}
		}
		throw new AssertionError();
	}

	/**
	 * Collect the leafs from the given iteTerm and build the proof for the clause
	 * {@pre (or (= iteTerm leaf1) ... (= iteTerm leafn))}
	 *
	 * @param iteTerm  the ite term.
	 * @param allLeafs a set were all leafs are added to.
	 * @return the proof for the clause.
	 */
	private Term proveIteEqualsLeafs(final ApplicationTerm iteTerm, final Set<Term> allLeafs) {
		assert isApplication(SMTLIBConstants.ITE, iteTerm);
		final Theory theory = iteTerm.getTheory();
		Term[] iteArgs = iteTerm.getParameters();
		final ArrayDeque<Term> todo = new ArrayDeque<>();
		final ArrayDeque<ApplicationTerm> subIteTerms = new ArrayDeque<>();
		final HashSet<Term> visited = new HashSet<>();
		Term proof = res(iteArgs[0], mProofRules.ite2(iteTerm), mProofRules.ite1(iteTerm));
		todo.add(iteArgs[2]);
		todo.add(iteArgs[1]);
		// find leafs and subIteTerms and bring subIteTerms in topological order.
		while (!todo.isEmpty()) {
			final Term candidate = todo.removeLast();
			if (!visited.contains(candidate)) {
				if (isApplication("ite", candidate)) {
					final ApplicationTerm subIteTerm = (ApplicationTerm) candidate;
					iteArgs = subIteTerm.getParameters();
					if (!visited.contains(iteArgs[1]) || !visited.contains(iteArgs[2])) {
						// if children have not been visited yet, visit them first, then visit ite again.
						todo.addLast(candidate);
						todo.addLast(iteArgs[1]);
						todo.addLast(iteArgs[2]);
					} else {
						// children already visited.  Add candidate to subIteTerms in reverse order and visit it.
						// this way children are guaranteed to appear after parents.
						subIteTerms.addFirst(subIteTerm);
						visited.add(candidate);
					}
				} else {
					// this is a leaf term
					allLeafs.add(candidate);
					visited.add(candidate);
				}
			}
		}
		// now proof {@pre (or ... (= iteTerm t) ...)} for all leafs.
		for (final ApplicationTerm subIteTerm : subIteTerms) {
			iteArgs = subIteTerm.getParameters();
			Term subProof = res(iteArgs[0], mProofRules.ite2(subIteTerm), mProofRules.ite1(subIteTerm));
			for (int i = 1; i < 3; i++) {
				final Term eq2 = theory.term(SMTLIBConstants.EQUALS, subIteTerm, iteArgs[i]);
				subProof = res(eq2, subProof, mProofRules.trans(iteTerm, subIteTerm, iteArgs[i]));
			}
			final Term eq1 = theory.term(SMTLIBConstants.EQUALS, iteTerm, subIteTerm);
			proof = res(eq1, proof, subProof);
		}
		return proof;
	}

	private Term convertTermITEBound(final ProofLiteral[] clause) {
		// Check for the form: (<= (+ (ite c1 t1 t2) x) 0) where (+ ti x) must be
		// constant and <= 0.
		// The ite can also be nested, i.e. (<= (+ (ite c1 (ite c2 t1 t2) (ite c3 t3
		// t4)) x) 0)
		// The ite can also be negated.
		// One of the (+ ti x) terms must be equal to 0.
		// The conditions ci can have arbitrary form.
		assert clause.length == 1 && clause[0].getPolarity() && isApplication("<=", clause[0].getAtom());
		final Theory theory = clause[0].getAtom().getTheory();
		final Term[] leqArgs = ((ApplicationTerm) clause[0].getAtom()).getParameters();
		assert leqArgs.length == 2 && isZero(leqArgs[1]);
		final SMTAffineTerm sum = new SMTAffineTerm(leqArgs[0]);

		final ApplicationTerm iteTerm = findAndCheckIteinIteBound(sum);
		final LinkedHashSet<Term> allLeafs = new LinkedHashSet<>();
		final LinkedHashSet<Term> neededRefls = new LinkedHashSet<>();
		Term proof = proveIteEqualsLeafs(iteTerm, allLeafs);

		final Sort sort = iteTerm.getSort();
		final FunctionSymbol lt = theory.getFunctionWithResult(SMTLIBConstants.LT, null, null, sort, sort);
		int itePos = -1;
		Term[] sumArgs = null;
		boolean isNegated = false;
		if (isApplication(SMTLIBConstants.PLUS, leqArgs[0])) {
			sumArgs = ((ApplicationTerm) leqArgs[0]).getParameters();
			for (int i = 0; i < sumArgs.length; i++) {
				if (sumArgs[i] == iteTerm) {
					itePos = i;
					break;
				} else if (isApplication(SMTLIBConstants.MUL, sumArgs[i])) {
					final Term[] mulArgs = ((ApplicationTerm) sumArgs[i]).getParameters();
					if (mulArgs.length == 2 && mulArgs[1] == iteTerm) {
						itePos = i;
						isNegated = true;
						break;
					}
				}
			}
			assert itePos >= 0;
		} else {
			if (leqArgs[0] != iteTerm) {
				isNegated = true;
			}
		}

		for (final Term leaf : allLeafs) {
			// replace (ite c t e) with leaf in sum by congruence
			Term eq = theory.term(SMTLIBConstants.EQUALS, iteTerm, leaf);
			Polynomial newSum = new Polynomial(leaf);
			Term newLeaf = leaf;
			if (isNegated) {
				final ApplicationTerm mulIte = (ApplicationTerm) (itePos >= 0 ? sumArgs[itePos] : leqArgs[0]);
				final Term[] mulArgs = mulIte.getParameters();
				final Term[] newMulArgs = mulArgs.clone();
				newMulArgs[1] = leaf;
				proof = res(eq, proof, mProofRules.cong(mulIte.getFunction(), mulArgs, newMulArgs));
				final Term rhs = theory.term(mulIte.getFunction(), newMulArgs);
				neededRefls.add(mulArgs[0]);
				newSum.mul(new Polynomial(newMulArgs[0]));
				newLeaf = newSum.toTerm(leaf.getSort());
				if (rhs != newLeaf) {
					proof = res(theory.term(SMTLIBConstants.EQUALS, mulIte, rhs), proof,
							res(theory.term(SMTLIBConstants.EQUALS, rhs, newLeaf),
								mProofRules.polyMul(rhs, newLeaf), mProofRules.trans(mulIte, rhs, newLeaf)));
				}
				eq = theory.term(SMTLIBConstants.EQUALS, mulIte, newLeaf);
			}
			if (itePos >= 0) {
				final FunctionSymbol plus = ((ApplicationTerm) leqArgs[0]).getFunction();
				final Term[] newSumArgs = sumArgs.clone();
				newSumArgs[itePos] = newLeaf;
				final Term rhs = theory.term(plus, newSumArgs);
				proof = res(eq, proof, mProofRules.cong(plus, sumArgs, newSumArgs));
				newSum = new Polynomial();
				for (int i = 0; i < newSumArgs.length; i++) {
					newSum.add(Rational.ONE, newSumArgs[i]);
					if (i != itePos) {
						neededRefls.add(newSumArgs[i]);
					}
				}
				newLeaf = newSum.toTerm(leaf.getSort());
				if (rhs != newLeaf) {
					proof = res(theory.term(SMTLIBConstants.EQUALS, leqArgs[0], rhs), proof,
							res(theory.term(SMTLIBConstants.EQUALS, rhs, newLeaf),
									mProofRules.polyAdd(rhs, newLeaf), mProofRules.trans(leqArgs[0], rhs, newLeaf)));
				}
				eq = theory.term(SMTLIBConstants.EQUALS, leqArgs[0], newLeaf);
			}
			// Now show ~(< 0 leqArgs[0]) from ~(< 0 newLeaf)
			final Term[] oldArgs = new Term[] { leqArgs[1], leqArgs[0] };
			final Term[] newArgs = new Term[] { leqArgs[1], newLeaf };
			proof = res(eq, proof, mProofRules.cong(lt, oldArgs, newArgs));
			neededRefls.add(leqArgs[1]);
			final Term oldLt = theory.term(lt, oldArgs);
			final Term newLt = theory.term(lt, newArgs);
			final Term ltEqual = theory.term(SMTLIBConstants.EQUALS, oldLt, newLt);
			proof = res(ltEqual, proof, mProofRules.iffElim2(ltEqual));
			proof = res(newLt, proof, mProofRules.farkas(new Term[] { newLt }, new BigInteger[] { BigInteger.ONE }));
		}

		// Now we have a proof for ~(< 0 leqArgs[0]); finish using total and reflexivity.
		proof = res(theory.term(lt, leqArgs[1], leqArgs[0]), mProofRules.total(leqArgs[0], leqArgs[1]), proof);
		for (final Term t : neededRefls) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, t, t), mProofRules.refl(t), proof);
		}
		return proof;
	}

	/**
	 * Convert the tautology that introduces a forall or eliminates an exists. These
	 * are the rules that introduce Skolem variables.
	 *
	 * @param clause     the clause to check
	 * @param skolemFuns the Skolemization used in the tautology. These are
	 *                   functions whose expansion is the correct choose term for
	 *                   the quantifier.
	 * @return the proof of the tautology.
	 */
	private Term convertTautQuantSkolemize(final ProofLiteral[] clause, final Term[] skolemFuns,
			final boolean isForall) {
		// isForall case:
		// clause[0]: (forall ((x...)) F)
		// clause[1]: (not (let ((x skolem...)) F))
		// !isForall case:
		// clause[0]: not (exists ((x...)) F
		// clause[1]: (let ((x skolem...)) F)
		assert clause.length == 2;
		final QuantifiedFormula qf = (QuantifiedFormula) clause[0].getAtom();
		assert isForall == clause[0].getPolarity();
		assert qf.getQuantifier() == (isForall ? QuantifiedFormula.FORALL : QuantifiedFormula.EXISTS);
		final Theory theory = qf.getTheory();
		final TermVariable[] vars = qf.getVariables();
		final Sort[] varSorts = new Sort[vars.length];
		for (int i = 0; i < vars.length; i++) {
			varSorts[i] = vars[i].getSort();
		}
		theory.push();
		final FunctionSymbol qFunc = theory.declareInternalFunction("@quantbody", varSorts, qf.getFreeVars(),
				qf.getSubformula(), FunctionSymbol.UNINTERPRETEDINTERNAL);
		final Term[] chooseTerms = mProofRules.getSkolemVars(vars, qf.getSubformula(), isForall);
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term subChoose = unletter.unlet(mSkript.let(vars, chooseTerms, qf.getSubformula()));
		final Term quantChoose = theory.term(qFunc, chooseTerms);
		final Term quantSkolem = theory.term(qFunc, skolemFuns);
		final Term subSkolem = unletter.unlet(mSkript.let(vars, skolemFuns, qf.getSubformula()));
		Term transProof = res(
				theory.term(SMTLIBConstants.EQUALS, quantSkolem, subSkolem),
				mProofRules.expand(quantSkolem),
				res(theory.term(SMTLIBConstants.EQUALS, subSkolem, quantSkolem),
						mProofRules.symm(subSkolem, quantSkolem),
						res(theory.term(SMTLIBConstants.EQUALS, quantSkolem, quantChoose),
								mProofRules.cong(qFunc, skolemFuns, chooseTerms),
								res(theory.term(SMTLIBConstants.EQUALS, quantChoose, subChoose),
										mProofRules.expand(quantChoose),
										mProofRules.trans(subSkolem, quantSkolem, quantChoose, subChoose)))));
		for (int i = 0; i < chooseTerms.length; i++) {
			transProof = res(theory.term(SMTLIBConstants.EQUALS, skolemFuns[i], chooseTerms[i]),
					mProofRules.expand(skolemFuns[i]), transProof);
		}
		final Term skolemEquivalence = theory.term(SMTLIBConstants.EQUALS, subSkolem, subChoose);
		Term proof;
		if (isForall) {
			proof = res(subChoose, mProofRules.iffElim2(skolemEquivalence), mProofRules.forallIntro(qf));
		} else {
			proof = res(subChoose, mProofRules.existsElim(qf), mProofRules.iffElim1(skolemEquivalence));
		}
		proof = res(skolemEquivalence, transProof, proof);
		proof = mProofRules.defineFun(qFunc, theory.lambda(vars, qf.getSubformula()), proof);
		theory.pop();
		return removeNot(proof, subSkolem, !isForall);
	}

	/**
	 * Convert the tautology that introduces an exists.
	 *
	 * @param clause the clause to check
	 * @param subst  the substitution used in the tautology; these are currently
	 *               fresh variables.
	 * @return the proof of the tautology.
	 */
	private Term convertTautForallElim(final ProofLiteral[] clause, final Term[] subst) {
		// clause[0] is (not (forall ((x1...)) F )).
		// subst is (y1, ..., yn).
		// clause[1] is F [y1/x1]...[yn/xn].
		assert clause.length == 2 && !clause[0].getPolarity();
		final Term forall = clause[0].getAtom();
		final QuantifiedFormula qf = (QuantifiedFormula) forall;
		assert qf.getQuantifier() == QuantifiedFormula.FORALL;
		final TermVariable[] universalVars = qf.getVariables();

		// subst must contain one substitution for each variable
		assert universalVars.length == subst.length;

		Term proof = mProofRules.forallElim(subst, qf);
		// remove negations
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term result = unletter.unlet(mSkript.let(universalVars, subst, qf.getSubformula()));
		proof = removeNot(proof, result, true);
		return proof;
	}

	/**
	 * Convert the tautology that introduces an exists.
	 *
	 * @param clause the clause to check
	 * @param subst  the substitution used in the tautology; these are currently
	 *               fresh variables.
	 * @return the proof of the tautology.
	 */
	private Term convertTautExistsIntro(final ProofLiteral[] clause, final Term[] subst) {
		// clause[0] is (exists ((x1...)) F ).
		// subst is (y1, ..., yn).
		// clause[1] is (not F [y1/x1]...[yn/xn]).
		assert clause.length == 2 && clause[0].getPolarity();
		final QuantifiedFormula qf = (QuantifiedFormula) clause[0].getAtom();
		assert qf.getQuantifier() == QuantifiedFormula.EXISTS;
		final TermVariable[] universalVars = qf.getVariables();
		assert universalVars.length == subst.length;

		Term proof = mProofRules.existsIntro(subst, qf);
		// remove negations
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term result = unletter.unlet(mSkript.let(universalVars, subst, qf.getSubformula()));
		proof = removeNot(proof, result, false);
		return proof;
	}

	private Term convertTautIte1Helper(final Term iteAtom, final Term iteTrueCase, final boolean polarity) {
		final Term iteTrueCaseEq = iteAtom.getTheory().term("=", iteAtom, iteTrueCase);
		final Term proof = mProofRules.resolutionRule(iteTrueCaseEq, mProofRules.ite1(iteAtom),
				polarity ? mProofRules.iffElim1(iteTrueCaseEq) : mProofRules.iffElim2(iteTrueCaseEq));
		return removeNot(proof, iteTrueCase, !polarity);
	}

	private Term convertTautIte2Helper(final Term iteAtom, final Term iteFalseCase, final boolean polarity) {
		final Term iteFalseCaseEq = iteAtom.getTheory().term("=", iteAtom, iteFalseCase);
		final Term proof = mProofRules.resolutionRule(iteFalseCaseEq, mProofRules.ite2(iteAtom),
				polarity ? mProofRules.iffElim1(iteFalseCaseEq) : mProofRules.iffElim2(iteFalseCaseEq));
		return removeNot(proof, iteFalseCase, !polarity);
	}

	private Term convertTautExcludedMiddle(final String name, final ProofLiteral[] clause) {
		assert clause.length == 2;
		final boolean isEqTrue = name == ":excludedMiddle1";

		// Check for the form: (+ (= p true) - p) :excludedMiddle1
		// or (+ (= p false) + p) :excludedMiddle2
		final Term equality = clause[0].getAtom();
		assert clause[0].getPolarity() && isApplication("=", equality);
		final Term[] eqArgs = ((ApplicationTerm) equality).getParameters();
		final boolean isAuxLiteral = isAuxApplication(eqArgs[0]);
		final Term atomTerm = isAuxLiteral ? expandAux((ApplicationTerm) eqArgs[0]) : eqArgs[0];
		assert eqArgs.length == 2 && isApplication(isEqTrue ? "true" : "false", eqArgs[1]);

		// now proof equality, lit
		Term proof = isEqTrue
				? mProofRules.resolutionRule(eqArgs[1], mProofRules.trueIntro(), mProofRules.iffIntro2(equality))
				: mProofRules.resolutionRule(eqArgs[1], mProofRules.iffIntro1(equality), mProofRules.falseElim());

		if (isAuxLiteral) {
			final Term expandAuxEq = mSkript.term(SMTLIBConstants.EQUALS, eqArgs[0], atomTerm);
			final Term expandAuxProof = mProofRules.expand(eqArgs[0]);
			if (isEqTrue) {
				proof = res(eqArgs[0], res(expandAuxEq, expandAuxProof, mProofRules.iffElim1(expandAuxEq)), proof);
			} else {
				proof = res(eqArgs[0], proof, res(expandAuxEq, expandAuxProof, mProofRules.iffElim2(expandAuxEq)));
			}
		}
		proof = removeNot(proof, atomTerm, !isEqTrue);
		return proof;
	}

	private boolean isSkolem(Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol func = ((ApplicationTerm) term).getFunction();
			return func.isIntern() && func.getName().startsWith("@skolem");
		}
		return false;
	}

	private boolean isAuxApplication(Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol func = ((ApplicationTerm) term).getFunction();
			return func.isIntern() && func.getName().startsWith("@AUX");
		}
		return false;
	}

	private int findArgPosition(final ProofLiteral searchTerm, final Term[] mainParams, boolean forImplication) {
		for (int i = 0; i < mainParams.length; i++) {
			Term mainParam = mainParams[i];
			boolean positive = true;
			while (isApplication(SMTLIBConstants.NOT, mainParam)) {
				mainParam = ((ApplicationTerm) mainParam).getParameters()[0];
				positive = !positive;
			}
			if (forImplication && i == mainParams.length - 1) {
				positive = !positive;
			}
			if (mainParam == searchTerm.getAtom() && positive == searchTerm.getPolarity()) {
				return i;
			}
		}
		throw new AssertionError();
	}

	private Term convertTautElimIntro(final String ruleName, final ProofLiteral[] clause) {
		final boolean isElim = ruleName.contains("-");

		ApplicationTerm mainAtom;
		final ApplicationTerm firstAtom = (ApplicationTerm) clause[0].getAtom();
		final boolean isAuxDefEq = clause[0].getPolarity() && isApplication(SMTLIBConstants.EQUALS, firstAtom);
		if (isAuxDefEq) {
			assert isApplication(isElim ? SMTLIBConstants.FALSE : SMTLIBConstants.TRUE, firstAtom.getParameters()[1]);
			mainAtom = (ApplicationTerm) expandAuxDef(firstAtom);
		} else {
			assert isElim != clause[0].getPolarity();
			mainAtom = firstAtom;
		}
		assert ruleName.startsWith(":" + mainAtom.getFunction().getName());
		final Term[] mainParams = mainAtom.getParameters();

		Term proof;
		switch (ruleName) {
		case ":or+": {
			assert clause.length == 2;
			final int pos = findArgPosition(clause[1].negate(), mainParams, false);
			proof = mProofRules.orIntro(pos, mainAtom);
			proof = removeNot(proof, mainParams[pos], false);
			break;
		}
		case ":or-": {
			proof = mProofRules.orElim(mainAtom);
			for (int i = 0; i < mainParams.length; i++) {
				proof = removeNot(proof, mainParams[i], true);
			}
			break;
		}
		case ":and+":
			proof = mProofRules.andIntro(mainAtom);
			for (int i = 0; i < mainParams.length; i++) {
				proof = removeNot(proof, mainParams[i], false);
			}
			break;
		case ":and-": {
			assert clause.length == 2;
			final int pos = findArgPosition(clause[1], mainParams, false);
			proof = mProofRules.andElim(pos, mainAtom);
			proof = removeNot(proof, mainParams[pos], true);
			break;
		}
		case ":=>+": {
			assert clause.length == 2;
			final int lastPos = mainParams.length - 1;
			final int pos = findArgPosition(clause[1], mainParams, true);
			proof = mProofRules.impIntro(pos, mainAtom);
			proof = removeNot(proof, mainParams[pos], pos != lastPos);
			break;
		}
		case ":=>-": {
			proof = mProofRules.impElim(mainAtom);
			for (int i = 0; i < mainParams.length; i++) {
				proof = removeNot(proof, mainParams[i], i == mainParams.length - 1);
			}
			break;
		}
		case ":xor+1": {
			proof = mProofRules.xorIntro(mainParams, new Term[] { mainParams[0] }, new Term[] { mainParams[1] });
			proof = removeNot(proof, mainParams[0], true);
			proof = removeNot(proof, mainParams[1], false);
			break;
		}
		case ":xor+2": {
			proof = mProofRules.xorIntro(mainParams, new Term[] { mainParams[1] }, new Term[] { mainParams[0] });
			proof = removeNot(proof, mainParams[0], false);
			proof = removeNot(proof, mainParams[1], true);
			break;
		}
		case ":xor-1": {
			proof = mProofRules.xorIntro(new Term[] { mainParams[0] }, new Term[] { mainParams[1] }, mainParams);
			proof = removeNot(proof, mainParams[0], true);
			proof = removeNot(proof, mainParams[1], true);
			break;
		}
		case ":xor-2": {
			proof = mProofRules.xorElim(mainParams, new Term[] { mainParams[0] }, new Term[] { mainParams[1] });
			proof = removeNot(proof, mainParams[0], false);
			proof = removeNot(proof, mainParams[1], false);
			break;
		}
		case ":ite+1":
			// iteAtom, ~cond, ~then
			proof = removeNot(convertTautIte1Helper(mainAtom, mainParams[1], true), mainParams[0], false);
			break;
		case ":ite+2":
			// iteAtom, cond, ~else
			proof = removeNot(convertTautIte2Helper(mainAtom, mainParams[2], true), mainParams[0], true);
			break;
		case ":ite+red":
			// iteAtom, ~then, ~else
			proof = mProofRules.resolutionRule(mainParams[0], convertTautIte2Helper(mainAtom, mainParams[2], true),
					convertTautIte1Helper(mainAtom, mainParams[1], true));
			break;
		case ":ite-1":
			// ~iteAtom, ~cond, then
			proof = removeNot(convertTautIte1Helper(mainAtom, mainParams[1], false), mainParams[0], false);
			break;
		case ":ite-2":
			// ~iteAtom, cond, else
			proof = removeNot(convertTautIte2Helper(mainAtom, mainParams[2], false), mainParams[0], true);
			break;
		case ":ite-red":
			// ~iteAtom, then, else
			proof = mProofRules.resolutionRule(mainParams[0], convertTautIte2Helper(mainAtom, mainParams[2], false),
					convertTautIte1Helper(mainAtom, mainParams[1], false));
			break;
		default:
			throw new AssertionError();
		}
		if (isAuxDefEq) {
			final Term expandEq = mSkript.term(SMTLIBConstants.EQUALS, firstAtom, mainAtom);
			if (isElim) {
				proof = mProofRules.resolutionRule(mainAtom, proveAuxElim(firstAtom, mainAtom), proof);
			} else {
				proof = mProofRules.resolutionRule(mainAtom, proof, mProofRules.iffElim1(expandEq));
				proof = mProofRules.resolutionRule(expandEq, proveAuxExpand(firstAtom, mainAtom), proof);
			}
		}
		return proof;
	}

	/**
	 * Check an select over store lemma for correctness. If a problem is found, an
	 * error is reported.
	 *
	 * @param clause the clause to check.
	 */
	private Term convertTautStore(final ProofLiteral[] clause) {
		// Store tautology have the form
		// (@tautology (! (= (select (store a i v) i) v) :store))
		assert clause.length == 1 && clause[0].getPolarity();
		final Term eqlit = clause[0].getAtom();
		assert isApplication("=", eqlit);
		final Term[] sides = ((ApplicationTerm) eqlit).getParameters();
		assert isApplication("select", sides[0]);
		final ApplicationTerm select = (ApplicationTerm) sides[0];
		final Term store = select.getParameters()[0];
		assert isApplication("store", store);
		final Term[] storeArgs = ((ApplicationTerm) store).getParameters();
		assert storeArgs[1] == select.getParameters()[1] && storeArgs[2] == sides[1];

		return mProofRules.selectStore1(storeArgs[0], storeArgs[1], storeArgs[2]);
	}

	private Term convertTautDiff(final ProofLiteral[] clause) {
		// lit0: (= a b)
		// lit1: ~(= (select a (diff a b)) (select b (diff a b)))
		assert clause.length == 2 && clause[0].getPolarity();
		final Term arrEq = clause[0].getAtom();
		assert isApplication("=", arrEq);
		final Term[] arrays = ((ApplicationTerm) arrEq).getParameters();
		// we could check the second equality, but the proof check in tautology will catch any problems
		return mProofRules.extDiff(arrays[0], arrays[1]);
	}

	private Term convertTautLowHigh(final String ruleName, final ProofLiteral[] clause) {
		final Term atom = clause[0].getAtom();
		final Theory theory = atom.getTheory();
		final boolean isToInt = ruleName.startsWith(":toInt");
		final boolean isHigh = ruleName.endsWith("High");
		// isLow: (<= (+ (- arg0) (* d candidate) ) 0)
		// aka. (>= (- arg0 (* d candidate)) 0)
		// isHigh: (not (<= (+ (- arg0) (* d candidate) |d|) 0)
		// aka. (< (- arg0 (* d candidate)) |d|)
		// where candidate is (div arg0 d) or (to_int arg0) and d is 1 for toInt.

		assert clause[0].getPolarity() != isHigh;
		assert isApplication("<=", atom);
		final Term[] leArgs = ((ApplicationTerm) atom).getParameters();
		final SMTAffineTerm lhs = new SMTAffineTerm(leArgs[0]);
		assert isZero(leArgs[1]);
		assert leArgs[0].getSort().getName() == (isToInt ? "Real" : "Int");

		final String func = isToInt ? "to_int" : "div";
		// search for the toInt or div term; note that there can be several div terms in case of a nested div.
		for (final Term candidate : lhs.getSummands().keySet()) {
			if (isApplication(func, candidate)) {
				final Term[] args = ((ApplicationTerm) candidate).getParameters();
				// compute d
				final Rational d;
				SMTAffineTerm summand;
				if (isToInt) {
					d = Rational.ONE;
					summand = new SMTAffineTerm(candidate);
				} else {
					final SMTAffineTerm arg1 = new SMTAffineTerm(args[1]);
					assert arg1.isConstant();
					d = arg1.getConstant();
					assert !d.equals(Rational.ZERO);
					summand = new SMTAffineTerm(candidate);
					summand.mul(d);
				}
				// compute expected term and check that lhs equals it.
				final SMTAffineTerm expected = new SMTAffineTerm(args[0]);
				expected.negate();
				expected.add(summand);
				if (isHigh) {
					expected.add(d.abs());
				}
				if (lhs.equals(expected)) {
					Term axiomTerm;
					Term proof;
					switch (ruleName) {
					case ":toIntLow": {
						axiomTerm = theory.term(SMTLIBConstants.LEQ,
								theory.term(SMTLIBConstants.TO_REAL, candidate), args[0]);
						proof = mProofRules.toIntLow(args[0]);
						break;
					}
					case ":toIntHigh": {
						axiomTerm = theory.term(SMTLIBConstants.LT, args[0],
								theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.TO_REAL, candidate),
										Rational.ONE.toTerm(args[0].getSort())));
						proof = mProofRules.toIntHigh(args[0]);
						break;
					}
					case ":divLow": {
						axiomTerm = theory.term(SMTLIBConstants.LEQ,
								theory.term(SMTLIBConstants.MUL, args[1], candidate), args[0]);
						proof = mProofRules.divLow(args[0], args[1]);
						final Term zero = Rational.ZERO.toTerm(args[1].getSort());
						proof = res(theory.term(SMTLIBConstants.EQUALS, args[1], zero),
								proof, proveTrivialDisequality(args[1], zero));
						break;
					}
					case ":divHigh": {
						axiomTerm = theory.term(SMTLIBConstants.LT, args[0],
								theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.MUL, args[1], candidate),
										theory.term(SMTLIBConstants.ABS, args[1])));
						proof = mProofRules.divHigh(args[0], args[1]);
						final Term zero = Rational.ZERO.toTerm(args[1].getSort());
						proof = res(theory.term(SMTLIBConstants.EQUALS, args[1], zero),
								proof, proveTrivialDisequality(args[1], zero));
						break;
					}
					default:
						throw new AssertionError();
					}
					final Term realAtom = isHigh ? atom : theory.term(SMTLIBConstants.LT, leArgs[1], leArgs[0]);
					if (ruleName.equals(":divHigh")) {
						final Term realAbsD = theory.term(SMTLIBConstants.ABS, args[1]);
						final Term absD = d.abs().toTerm(args[1].getSort());
						final Term absDivisor = theory.term(SMTLIBConstants.EQUALS, realAbsD, absD);
						proof = res(axiomTerm, proof, mProofRules.farkas(new Term[] {realAtom, axiomTerm, absDivisor},
								new BigInteger[] { BigInteger.ONE, BigInteger.ONE, BigInteger.ONE }));
						proof = res(theory.term(SMTLIBConstants.EQUALS, realAbsD, absD),
								proveAbsConstant(d, args[0].getSort()), proof);
					} else {
						proof = res(axiomTerm, proof, mProofRules.farkas(new Term[] {realAtom, axiomTerm},
								new BigInteger[] { BigInteger.ONE, BigInteger.ONE }));
					}
					if (!isHigh) {
						proof = res(realAtom, mProofRules.total(leArgs[0], leArgs[1]), proof);
					}
					return proof;
				}
			}
		}
		throw new AssertionError();
	}

	private Term convertTautDtMatch(final String rule, final ProofLiteral[] clause) {
		// there are two different matchCase tautologies:
		// boolean case: +/~(match ...), ~(is_cons c), ~/+(case ...)
		// term case: ~(is_cons c), (= (match ...) (case ...))
		// similarly, there are two different matchDefault tautologies:
		// boolean case: +/~(match ...), (is_cons c1), ..., (is_cons cn) ~/+(case ...)
		// term case: (is_cons c1), ..., (is_cons cn), (= (match ...) (case ...))
		boolean negated;
		// check for matchCase or matchDefault.
		final boolean isMatchCase = rule.equals(":matchCase");
		// use the first literal to distinguish between boolean and term case.
		final boolean boolCase = clause[0].getAtom() instanceof MatchTerm;
		MatchTerm matchTerm;
		ApplicationTerm isTerm = null;
		if (boolCase) {
			// boolean case
			assert clause.length >= 2;
			negated = !clause[0].getPolarity();
			matchTerm = (MatchTerm) clause[0].getAtom();
			if (isMatchCase) {
				assert !clause[1].getPolarity();
				final Term tester = clause[1].getAtom();
				assert isApplication(SMTLIBConstants.IS, tester);
				isTerm = (ApplicationTerm) tester;
			}
		} else {
			// term case
			assert clause.length >= 1;
			negated = false;
			if (isMatchCase) {
				assert !clause[0].getPolarity();
				final Term tester = clause[0].getAtom();
				assert isApplication(SMTLIBConstants.IS, tester);
				isTerm = (ApplicationTerm) tester;
			}
			assert clause[clause.length - 1].getPolarity();
			assert isApplication(SMTLIBConstants.EQUALS, clause[clause.length - 1].getAtom());
			final ApplicationTerm eqTerm = (ApplicationTerm) clause[clause.length - 1].getAtom();
			assert eqTerm.getParameters().length == 2;
			matchTerm = (MatchTerm) eqTerm.getParameters()[0];
		}

		final Constructor[] constrs = matchTerm.getConstructors();
		int caseNr;
		for (caseNr = 0; caseNr < constrs.length; caseNr++) {
			if (isMatchCase ? constrs[caseNr].getName().equals(isTerm.getFunction().getIndices()[0])
					: constrs[caseNr] == null) {
					break;
			}
		}
		final Theory theory = matchTerm.getTheory();
		final Term dataTerm = matchTerm.getDataTerm();
		Term iteTerm = MinimalProofChecker.buildIteForMatch(matchTerm);

		final ArrayList<Term> eqSequence = new ArrayList<>();
		eqSequence.add(matchTerm);
		for (int i = 0; i < caseNr; i++) {
			assert isApplication(SMTLIBConstants.ITE, iteTerm);
			eqSequence.add(iteTerm);
			iteTerm = ((ApplicationTerm) iteTerm).getParameters()[2];
		}
		if (isMatchCase && caseNr < constrs.length - 1) {
			assert isApplication(SMTLIBConstants.ITE, iteTerm);
			eqSequence.add(iteTerm);
			iteTerm = ((ApplicationTerm) iteTerm).getParameters()[1];
		}
		eqSequence.add(iteTerm);
		Term proof = mProofRules.trans(eqSequence.toArray(new Term[eqSequence.size()]));
		proof = res(theory.term(SMTLIBConstants.EQUALS, matchTerm, eqSequence.get(1)), mProofRules.dtMatch(matchTerm),
				proof);
		final Constructor cons = constrs[caseNr];
		Term consTerm = null;
		if (isMatchCase) {
			final Term[] selectTerms = new Term[cons.getSelectors().length];
			for (int i = 0; i < selectTerms.length; i++) {
				selectTerms[i] = theory.term(cons.getSelectors()[i], dataTerm);
			}
			consTerm = theory.term(cons.getName(), null, (cons.needsReturnOverload() ? dataTerm.getSort() : null),
					selectTerms);
		}
		for (int i = 0; i < caseNr; i++) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, eqSequence.get(i + 1), eqSequence.get(i + 2)),
					mProofRules.ite2(eqSequence.get(i + 1)), proof);
			if (isMatchCase) {
				final String[] index = new String[] { constrs[i].getName() };
				final Term isConsData = theory.term(SMTLIBConstants.IS, index, null, dataTerm);
				final Term isConsCons = theory.term(SMTLIBConstants.IS, index, null, consTerm);
				final Term isConsEq = theory.term(SMTLIBConstants.EQUALS, isConsCons, isConsData);
				proof = res(isConsData, proof, mProofRules.iffElim1(isConsEq));
				proof = res(isConsEq, mProofRules.cong(isConsCons, isConsData), proof);
				proof = res(isConsCons, proof, mProofRules.dtTestE(constrs[i].getName(), consTerm));
			}
		}
		if (isMatchCase && caseNr > 0) {
			final Term isConsCons = theory.term(SMTLIBConstants.IS, new String[] { cons.getName() }, null, dataTerm);
			proof = res(theory.term(SMTLIBConstants.EQUALS, consTerm, dataTerm), mProofRules.dtCons(isConsCons), proof);
		}
		if (isMatchCase && caseNr < constrs.length - 1) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, eqSequence.get(caseNr + 1), eqSequence.get(caseNr + 2)),
					mProofRules.ite1(eqSequence.get(caseNr + 1)), proof);
		}
		if (boolCase) {
			final Term matchEq = theory.term(SMTLIBConstants.EQUALS, matchTerm, iteTerm);
			proof = res(matchEq, proof, (negated ? mProofRules.iffElim2(matchEq) : mProofRules.iffElim1(matchEq)));
			proof = removeNot(proof, iteTerm, negated);
		}
		return proof;
	}

	private Term convertTautology(final ProofLiteral[] clause, Annotation annot) {
		final String ruleName = annot.getKey();
		Term proof = null;
		switch (ruleName) {
		case ":true+":
			assert clause.length == 1 && clause[0].getPolarity()
					&& isApplication(SMTLIBConstants.TRUE, clause[0].getAtom());
			proof = mProofRules.trueIntro();
			break;
		case ":false-":
			assert clause.length == 1 && !clause[0].getPolarity()
					&& isApplication(SMTLIBConstants.FALSE, clause[0].getAtom());
			proof = mProofRules.falseElim();
			break;
		case ":or+":
		case ":or-":
		case ":and+":
		case ":and-":
		case ":=>+":
		case ":=>-":
		case ":xor+1":
		case ":xor+2":
		case ":xor-1":
		case ":xor-2":
		case ":ite+1":
		case ":ite+2":
		case ":ite+red":
		case ":ite-1":
		case ":ite-2":
		case ":ite-red": {
			proof = convertTautElimIntro(ruleName, clause);
			break;
		}
		case ":=+1": {
			assert clause.length == 3;
			final Term eqTerm = clause[0].getAtom();
			assert clause[0].getPolarity() && isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			proof = mProofRules.iffIntro1(eqTerm);
			assert clause[1].getPolarity() && eqParams[0] == clause[1].getAtom();
			proof = removeNot(proof, eqParams[0], true);
			assert clause[2].getPolarity() && eqParams[1] == clause[2].getAtom();
			proof = removeNot(proof, eqParams[1], true);
			break;
		}
		case ":=+2": {
			assert clause.length == 3;
			final Term eqTerm = clause[0].getAtom();
			assert clause[0].getPolarity() && isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			proof = mProofRules.iffIntro2(eqTerm);
			assert !clause[1].getPolarity() && eqParams[0] == clause[1].getAtom();
			proof = removeNot(proof, eqParams[0], false);
			assert !clause[2].getPolarity() && eqParams[1] == clause[2].getAtom();
			proof = removeNot(proof, eqParams[0], false);
			break;
		}
		case ":=-1": {
			assert clause.length == 3;
			final Term eqTerm = clause[0].getAtom();
			assert !clause[0].getPolarity() && isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			proof = mProofRules.iffElim1(eqTerm);
			assert clause[1].getPolarity() && eqParams[0] == clause[1].getAtom();
			proof = removeNot(proof, eqParams[0], true);
			assert !clause[2].getPolarity() && eqParams[1] == clause[2].getAtom();
			proof = removeNot(proof, eqParams[1], false);
			break;
		}
		case ":=-2": {
			assert clause.length == 3;
			final Term eqTerm = clause[0].getAtom();
			assert !clause[0].getPolarity() && isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			proof = mProofRules.iffElim2(eqTerm);
			assert !clause[1].getPolarity() && eqParams[0] == clause[1].getAtom();
			proof = removeNot(proof, eqParams[0], false);
			assert clause[2].getPolarity() && eqParams[1] == clause[2].getAtom();
			proof = removeNot(proof, eqParams[1], true);
			break;
		}
		case ":exists-":
		case ":forall+": {
			proof = convertTautQuantSkolemize(clause, (Term[]) annot.getValue(), ruleName.equals(":forall+"));
			break;
		}
		case ":exists+": {
			proof = convertTautExistsIntro(clause, (Term[]) annot.getValue());
			break;
		}
		case ":forall-": {
			proof = convertTautForallElim(clause, (Term[]) annot.getValue());
			break;
		}
		case ":termITE": {
			proof = convertTermITE(clause);
			break;
		}
		case ":termITEBound": {
			proof = convertTermITEBound(clause);
			break;
		}
		case ":trueNotFalse": {
			final Theory t = clause[0].getAtom().getTheory();
			proof = mProofRules.resolutionRule(t.mTrue, mProofRules.trueIntro(), mProofRules.resolutionRule(t.mFalse,
					mProofRules.iffElim2(t.term("=", t.mTrue, t.mFalse)), mProofRules.falseElim()));
			break;
		}
		case ":excludedMiddle1":
		case ":excludedMiddle2":
			proof = convertTautExcludedMiddle(ruleName, clause);
			break;
		case ":divHigh":
		case ":divLow":
		case ":toIntHigh":
		case ":toIntLow":
			proof = convertTautLowHigh(ruleName, clause);
			break;
		case ":store":
			proof = convertTautStore(clause);
			break;
		case ":diff":
			proof = convertTautDiff(clause);
			break;
		case ":matchCase":
		case ":matchDefault":
			proof = convertTautDtMatch(ruleName, clause);
			break;
		default:
			throw new IllegalArgumentException("Unknown Tautology");
		}
		assert checkProof(proof, clause);
		return proof;
	}

	private Term convertTrans(final Term[] newParams) {
		final Term[] intermediateTerms = new Term[newParams.length + 1];
		Term lastTerm = null;
		for (int i = 0; i < newParams.length; i++) {
			final ApplicationTerm provedEq = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[i]);
			assert isApplication(SMTLIBConstants.EQUALS, provedEq);
			assert provedEq.getParameters().length == 2;
			assert i == 0 || lastTerm == provedEq.getParameters()[0];
			intermediateTerms[i] = provedEq.getParameters()[0];
			lastTerm = provedEq.getParameters()[1];
		}
		intermediateTerms[newParams.length] = lastTerm;
		Term clause = mProofRules.trans(intermediateTerms);
		for (int i = 0; i < newParams.length; i++) {
			final ApplicationTerm provedEq = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[i]);
			final Term subproof = subproof((AnnotatedTerm) newParams[i]);
			clause = mProofRules.resolutionRule(provedEq, subproof, clause);
		}
		final Term provedTerm = clause.getTheory().term(SMTLIBConstants.EQUALS, intermediateTerms[0],
				intermediateTerms[newParams.length]);
		return annotateProved(provedTerm, clause);
	}

	private Term convertCong(final FunctionSymbol congSymb, final Term[] newParams) {
		final Sort resultSort = congSymb.isReturnOverload() ? congSymb.getReturnSort() : null;
		final FunctionSymbol func = CongRewriteFunctionFactory.getFunctionFromIndex(congSymb.getIndices(),
				congSymb.getParameterSorts(), resultSort);

		final ApplicationTerm leftEquality = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[0]);
		final Theory t = newParams[0].getTheory();
		assert isApplication(SMTLIBConstants.EQUALS, leftEquality);
		final Term[] oldFuncParams = new Term[newParams.length];
		final Term[] newFuncParams = new Term[newParams.length];
		final Term[] newLit = new Term[newParams.length];
		final Term[] newLitProof = new Term[newParams.length];
		for (int i = 0; i < newFuncParams.length; i++) {
			final ApplicationTerm provedEquality = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[i]);
			newLit[i] = provedEquality;
			newLitProof[i] = subproof((AnnotatedTerm) newParams[i]);
			oldFuncParams[i] = provedEquality.getParameters()[0];
			newFuncParams[i] = provedEquality.getParameters()[1];
		}

		final Term oldFunc = t.term(func, oldFuncParams);
		final Term newFunc = t.term(func, newFuncParams);
		final Term congEquality = t.term(SMTLIBConstants.EQUALS, oldFunc, newFunc);
		Term proof = mProofRules.cong(func, oldFuncParams, newFuncParams);
		final HashSet<Term> eliminated = new HashSet<>();
		for (int i = 0; i < newFuncParams.length; i++) {
			if (!eliminated.contains(newLit[i])) {
				proof = mProofRules.resolutionRule(newLit[i], newLitProof[i], proof);
				eliminated.add(newLit[i]);
			}
		}
		return annotateProved(congEquality, proof);
	}

	private Term convertMatch(final Term[] newParams) {
		final AnnotatedTerm dataRewrite = (AnnotatedTerm) newParams[0];
		final Theory theory = dataRewrite.getTheory();
		final ApplicationTerm dataEquality = (ApplicationTerm) provedTerm(dataRewrite);
		assert dataEquality.getFunction().getName().equals(SMTLIBConstants.EQUALS);
		final Term oldData = dataEquality.getParameters()[0];
		final Term newData = dataEquality.getParameters()[1];

		final DataType dataType = (DataType) oldData.getSort().getSortSymbol();
		final Term[] oldMatchCases = new Term[newParams.length - 1];
		final Term[] newMatchCases = new Term[newParams.length - 1];
		final TermVariable[][] caseVars = new TermVariable[newParams.length - 1][];
		final Constructor[] constructors = new Constructor[newParams.length - 1];
		final Term[] rewriteProofs = new Term[newParams.length - 1];
		for  (int i = 1; i < newParams.length; i++) {
			final AnnotatedTerm caseRewrite = (AnnotatedTerm) newParams[i];
			final AnnotatedTerm rewrite = (AnnotatedTerm) caseRewrite.getSubterm();
			final ApplicationTerm caseEquality = (ApplicationTerm) provedTerm(rewrite);
			assert caseRewrite.getAnnotations()[0].getKey() == ProofConstants.ANNOTKEY_VARS;
			caseVars[i-1] = (TermVariable[]) caseRewrite.getAnnotations()[0].getValue();
			assert caseRewrite.getAnnotations()[1].getKey() == ProofConstants.ANNOTKEY_CONSTRUCTOR;
			final String constructorName = (String) caseRewrite.getAnnotations()[1].getValue();
			oldMatchCases[i - 1] = caseEquality.getParameters()[0];
			newMatchCases[i - 1] = caseEquality.getParameters()[1];
			constructors[i - 1] = constructorName == null ? null : dataType.findConstructor(constructorName);
			rewriteProofs[i - 1] = subproof(rewrite);
		}
		final MatchTerm oldOldMatch = (MatchTerm) theory.match(oldData, caseVars, oldMatchCases, constructors);
		final MatchTerm oldMatch = (MatchTerm) theory.match(newData, caseVars, oldMatchCases, constructors);
		final MatchTerm newMatch = (MatchTerm) theory.match(newData, caseVars, newMatchCases, constructors);
		Term oldMatchEqualityProof = null;
		if (oldData != newData) {
			theory.push();
			final TermVariable dataVar = theory.createFreshTermVariable("match", oldData.getSort());
			final TermVariable[] bodyVars = new TermVariable[] { dataVar };
			final Term bodyDef = theory.match(dataVar, caseVars, oldMatchCases, constructors);
			final FunctionSymbol bodyFunc = theory.declareInternalFunction("@matchbody",
					new Sort[] { oldData.getSort() }, bodyVars, bodyDef, FunctionSymbol.UNINTERPRETEDINTERNAL);
			final Term oldBody = theory.term(bodyFunc, oldData);
			final Term newBody = theory.term(bodyFunc, newData);
			final Term oldOldMatchBodyEq = res(theory.term(SMTLIBConstants.EQUALS, oldBody, oldOldMatch),
					mProofRules.expand(oldBody), mProofRules.symm(oldOldMatch, oldBody));
			final Term oldNewBodyEq = res(theory.term(SMTLIBConstants.EQUALS, oldData, newData),
					subproof(dataRewrite), mProofRules.cong(oldBody, newBody));
			oldMatchEqualityProof = res(theory.term(SMTLIBConstants.EQUALS, oldOldMatch, oldBody), oldOldMatchBodyEq,
					res(theory.term(SMTLIBConstants.EQUALS, oldBody, newBody), oldNewBodyEq,
							res(theory.term(SMTLIBConstants.EQUALS, newBody, oldMatch),
									mProofRules.expand(newBody),
									mProofRules.trans(oldOldMatch, oldBody, newBody, oldMatch))));
			oldMatchEqualityProof = mProofRules.defineFun(bodyFunc, theory.lambda(bodyVars, bodyDef),
					oldMatchEqualityProof);
			theory.pop();
		}

		final Term oldIte = MinimalProofChecker.buildIteForMatch(oldMatch);
		final Term newIte = MinimalProofChecker.buildIteForMatch(newMatch);
		Term iteEqualsProof = null;
		boolean needReflData = false;
		Term oldSub = oldIte;
		Term newSub = newIte;
		for (int i = 0; i < constructors.length; i++) {
			Term oldCase, newCase;
			if (constructors[i] == null || i == newParams.length - 1) {
				oldCase = oldSub;
				newCase = newSub;
			} else {
				assert ((ApplicationTerm) oldSub).getFunction().getName().equals("ite");
				assert ((ApplicationTerm) newSub).getFunction().getName().equals("ite");
				oldCase = ((ApplicationTerm) oldSub).getParameters()[1];
				newCase = ((ApplicationTerm) newSub).getParameters()[1];
				iteEqualsProof = res(theory.term(SMTLIBConstants.EQUALS, oldSub, newSub),
						mProofRules.cong(oldSub, newSub), iteEqualsProof);

				final Term oldCond = ((ApplicationTerm) oldSub).getParameters()[0];
				final Term newCond = ((ApplicationTerm) newSub).getParameters()[0];
				iteEqualsProof = res(theory.term(SMTLIBConstants.EQUALS, oldCond, newCond),
						mProofRules.cong(oldCond, newCond), iteEqualsProof);
				needReflData = true;
			}
			Term[] selectors;
			if (constructors[i] == null) {
				selectors = new Term[] { newData };
			} else {
				selectors = new Term[constructors[i].getSelectors().length];
				for (int j = 0; j < selectors.length; j++) {
					selectors[j] = theory.term(constructors[i].getSelectors()[j], newData);
				}
			}
			iteEqualsProof = res(theory.term(SMTLIBConstants.EQUALS, oldCase, newCase),
					theory.let(caseVars[i], selectors, rewriteProofs[i]), iteEqualsProof);
			if (constructors[i] == null) {
				break;
			} else if (i < newParams.length - 1) {
				oldSub = ((ApplicationTerm) oldSub).getParameters()[2];
				newSub = ((ApplicationTerm) newSub).getParameters()[2];
			}
		}
		iteEqualsProof = new FormulaUnLet().unlet(iteEqualsProof);
		if (needReflData) {
			iteEqualsProof = res(theory.term(SMTLIBConstants.EQUALS, newData, newData),
					mProofRules.refl(newData), iteEqualsProof);
		}
		final Term iteEquality = theory.term(SMTLIBConstants.EQUALS, oldIte, newIte);
		Term proof = res(iteEquality, iteEqualsProof, mProofRules.trans(oldMatch, oldIte, newIte, newMatch));
		proof = res(theory.term(SMTLIBConstants.EQUALS, oldMatch, oldIte), mProofRules.dtMatch(oldMatch), proof);
		proof = res(theory.term(SMTLIBConstants.EQUALS, newMatch, newIte), mProofRules.dtMatch(newMatch),
				res(theory.term(SMTLIBConstants.EQUALS, newIte, newMatch), mProofRules.symm(newIte, newMatch), proof));
		if (oldData != newData) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, oldOldMatch, oldMatch), oldMatchEqualityProof,
					res(theory.term(SMTLIBConstants.EQUALS, oldMatch, newMatch), proof,
							mProofRules.trans(oldOldMatch, oldMatch, newMatch)));
		}

		return annotateProved(theory.term(SMTLIBConstants.EQUALS, oldOldMatch, newMatch), proof);
	}

	private Term convertRewriteIntern(final Term lhs, final Term rhs) {
		final Theory theory = lhs.getTheory();
		// simple case first
		if (rhs == lhs) {
			return mProofRules.refl(lhs);
		}

		// term x can be rewritten to (not (= x false))) for EPR reasoning
		if (isApplication("not", rhs)) {
			final Term atom = ((ApplicationTerm) rhs).getParameters()[0];
			if (isApplication("=", atom)) {
				final ApplicationTerm rhsApp = (ApplicationTerm) atom;
				if (isApplication("false", rhsApp.getParameters()[1]) && lhs == rhsApp.getParameters()[0]) {
					final Term rhsLit = theory.term("not", rhsApp);
					final Term lhsEqRhsLit = theory.term("=", lhs, rhsLit);
					Term proofLhsEqRhsLit;
					final Term falseTerm = rhsApp.getParameters()[1];
					proofLhsEqRhsLit = proveIff(lhsEqRhsLit,
							mProofRules.resolutionRule(rhsApp, mProofRules.notIntro(rhsLit),
									mProofRules.iffElim2(rhsApp)),
							mProofRules.resolutionRule(rhsApp, mProofRules.iffIntro1(rhsApp),
									mProofRules.notElim(rhsLit)));
					proofLhsEqRhsLit = mProofRules.resolutionRule(falseTerm, proofLhsEqRhsLit, mProofRules.falseElim());
					return proofLhsEqRhsLit;
				}
			}
		}

		/* second case: boolean functions are created as equality with true */
		if (isApplication("=", rhs)) {
			final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
			if (rhsArgs.length == 2 && isApplication("true", rhsArgs[1])) {
				/* check if we need to expand an @aux application */
				if (lhs == rhsArgs[0] || isAuxApplication(rhsArgs[0])) {

					final Term equality1 = theory.term("=", rhsArgs[0], rhs);
					Term proof = res(rhsArgs[1], mProofRules.trueIntro(),
							proveIff(equality1, mProofRules.iffIntro2(rhs), mProofRules.iffElim1(rhs)));
					if (lhs != rhsArgs[0]) {
						final Term transitivity = mProofRules.trans(lhs, rhsArgs[0], rhs);
						proof = mProofRules.resolutionRule(equality1, proof, transitivity);
						proof = res(theory.term("=", lhs, rhsArgs[0]), res(theory.term("=", rhsArgs[0], lhs),
												mProofRules.expand(rhsArgs[0]), mProofRules.symm(lhs, rhsArgs[0])),
										proof);
					}
					return proof;
				}
			}
		}

		if (isApplication("<=", lhs)) {
			final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
			assert isZero(lhsParams[1]);
			return proveRewriteWithLeq(lhs, rhs, true);
		}

		// eq is normalized in CC (sides may be swapped)
		if (isApplication("=", lhs)) {
			/* compute affine term for lhs */
			final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
			assert lhsParams.length == 2;

			// check rewrites for trivial disequality / equality.
			if (isApplication("false", rhs)) {
				final Term proofNotLhs = proveTrivialDisequality(lhsParams[0], lhsParams[1]);
				return proveIffFalse(theory.term("=", lhs, rhs), proofNotLhs);
			} else if (isApplication("true", rhs)) {
				// since we canonicalize SMTAffineTerms, they can only be equal if they are
				// identical.
				assert lhsParams[0] == lhsParams[1];
				return proveIffTrue(theory.term("=", lhs, rhs), mProofRules.refl(lhsParams[0]));
			}

			assert isApplication("=", rhs);
			final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
			assert rhsParams.length == 2;

			final Term equality = theory.term("=", lhs, rhs);
			if (lhsParams[1] == rhsParams[0] && lhsParams[0] == rhsParams[1]) {
				// lhs and rhs are only swapped
				return proveIff(equality, mProofRules.symm(rhsParams[0], rhsParams[1]),
						mProofRules.symm(lhsParams[0], lhsParams[1]));
			} else {
				// Now it must be an LA equality that got normalized in a different way.
				assert lhsParams[0].getSort().isNumericSort();
				return proveRewriteWithLinEq(lhs, rhs);
			}
		}
		throw new AssertionError();
	}

	private Term convertRewriteLeq(final String rewriteRule, final Term rewrite, final Term lhs, final Term rhs) {
		// (<= c 0) --> true/false if c is constant.
		assert isApplication("<=", lhs);
		final Term[] params = ((ApplicationTerm) lhs).getParameters();
		assert params.length == 2 && isZero(params[1]);
		final Rational param0 = parseConstant(params[0]);
		final boolean isTrue = rewriteRule == ":leqTrue";
		if (isTrue) {
			assert param0.signum() <= 0 && isApplication("true", rhs);
			final Term falseLhs = lhs.getTheory().term("<", params[1], params[0]);
			return proveIffTrue(rewrite,
					mProofRules.resolutionRule(falseLhs, mProofRules.total(params[0], params[1]),
							mProofRules.farkas(new Term[] { falseLhs }, new BigInteger[] { BigInteger.ONE })));
		} else {
			assert param0.signum() > 0 && isApplication("false", rhs);
			return proveIffFalse(rewrite, mProofRules.farkas(new Term[] { lhs }, new BigInteger[] { BigInteger.ONE }));
		}
	}

	private Term convertRewriteNot(final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (not lhsAtom)
		assert isApplication("not", lhs);
		final Term lhsAtom = ((ApplicationTerm) lhs).getParameters()[0];
		if (isApplication("false", lhsAtom)) {
			// not false = true
			assert isApplication("true", rhs);
			return proveIffTrue(rewrite,
					mProofRules.resolutionRule(lhsAtom, mProofRules.notIntro(lhs), mProofRules.falseElim()));
		}
		if (isApplication("true", lhsAtom)) {
			// not true = false
			assert isApplication("false", rhs);
			return proveIffFalse(rewrite,
					mProofRules.resolutionRule(lhsAtom, mProofRules.trueIntro(), mProofRules.notElim(lhs)));
		}
		if (isApplication("not", lhsAtom)) {
			// not (not x) = x
			assert rhs == ((ApplicationTerm) lhsAtom).getParameters()[0];
			return proveIff(rewrite,
					mProofRules.resolutionRule(lhsAtom, mProofRules.notIntro(lhsAtom), mProofRules.notElim(lhs)),
					mProofRules.resolutionRule(lhsAtom, mProofRules.notIntro(lhs), mProofRules.notElim(lhsAtom)));
		}
		throw new AssertionError();
	}

	private Term convertRewriteTrueNotFalse(final Term lhs, final Term rhs) {
		// expect lhs: (= ... true ... false ...)), rhs: false
		final Theory t = lhs.getTheory();
		assert isApplication("=", lhs) && isApplication("false", rhs);
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		int trueIdx = -1, falseIdx = -1;
		for (int i = 0; i < lhsParams.length; i++) {
			final Term term = lhsParams[i];
			if (isApplication("true", term)) {
				trueIdx = i;
			}
			if (isApplication("false", term)) {
				falseIdx = i;
			}
		}
		assert trueIdx >= 0 && falseIdx >= 0;
		Term clause;
		final Term trueEqFalse = t.term(SMTLIBConstants.EQUALS, lhsParams[trueIdx], lhsParams[falseIdx]);
		clause = mProofRules.resolutionRule(trueEqFalse, mProofRules.equalsElim(trueIdx, falseIdx, lhs),
				mProofRules.iffElim2(trueEqFalse));
		clause = mProofRules.resolutionRule(lhs, mProofRules.iffIntro1(t.term(SMTLIBConstants.EQUALS, lhs, rhs)),
				clause);
		clause = mProofRules.resolutionRule(lhsParams[falseIdx],
				mProofRules.resolutionRule(lhsParams[trueIdx], mProofRules.trueIntro(), clause),
				mProofRules.falseElim());
		return clause;
	}

	private Term convertRewriteEqTrueFalse(final String rewriteRule, final Term lhs, final Term rhs) {
		// lhs: (= l1 true ln), rhs: (not (or (not l1) ... (not ln)))
		// lhs: (= l1 false ln), rhs: (not (or l1 ... ln))
		// duplicated entries in lhs should be removed in rhs.
		final boolean trueCase = rewriteRule.equals(":eqTrue");
		assert isApplication("=", lhs);
		int trueFalseIdx = -1;
		final Term[] params = ((ApplicationTerm) lhs).getParameters();
		final LinkedHashMap<Term, Integer> args = new LinkedHashMap<>();
		for (int i = 0; i < params.length; i++) {
			final Term t = params[i];
			if (isApplication(trueCase ? "true" : "false", t)) {
				trueFalseIdx = i;
			} else if (!args.containsKey(t)) {
				args.put(t, i);
			}
		}
		assert trueFalseIdx >= 0;
		final Theory theo = lhs.getTheory();

		final Term rewrite = theo.term(SMTLIBConstants.EQUALS, lhs, rhs);
		Term proofRhs = null;
		Term rhsAtom = null;
		if (args.size() > 1 || !trueCase) {
			assert isApplication(SMTLIBConstants.NOT, rhs);
			rhsAtom = ((ApplicationTerm) rhs).getParameters()[0];
			proofRhs = mProofRules.notIntro(rhs);
			if (args.size() > 1) {
				assert isApplication(SMTLIBConstants.OR, rhsAtom);
				proofRhs = res(rhsAtom, proofRhs, mProofRules.orElim(rhsAtom));
			}
		}
		Term proofLhs = params.length > 2 ? mProofRules.equalsIntro(lhs) : null;
		for (int i = 0; i < params.length - 1; i++) {
			final Term equality = theo.term(SMTLIBConstants.EQUALS, params[i], params[i+1]);
			final Term iffIntro = trueCase ? mProofRules.iffIntro2(equality) : mProofRules.iffIntro1(equality);
			proofLhs = res(equality, iffIntro, proofLhs);
		}
		// proofRhs: (not? l1), ..., (not? ln), rhs.
		// proofLhs: ~true/false, ~? l1,...,~? ln, lhs.
		// introduce all distinct arguments
		int orPos = 0;
		for (final int pos : args.values()) {
			final Term arg = params[pos];
			final Term notArg = theo.term(SMTLIBConstants.NOT, arg);
			final Term orArg = trueCase ? notArg : arg;
			if (args.size() > 1) {
				if (trueCase) {
					proofRhs = res(notArg, proofRhs, mProofRules.notElim(notArg));
					proofLhs = res(arg, mProofRules.notIntro(notArg), proofLhs);
				}
				proofLhs = res(orArg, proofLhs, mProofRules.orIntro(orPos++, rhsAtom));
			}
			final Term argTrueFalse = theo.term(SMTLIBConstants.EQUALS, arg, params[trueFalseIdx]);
			proofRhs = trueCase ? res(arg, mProofRules.iffElim1(argTrueFalse), proofRhs)
					: res(arg, proofRhs, mProofRules.iffElim2(argTrueFalse));
			final Term equalsElim = params.length > 2 ? mProofRules.equalsElim(pos, trueFalseIdx, lhs)
					: trueFalseIdx == 1 ? null : mProofRules.symm(params[1], params[0]);
			proofRhs = res(argTrueFalse, equalsElim, proofRhs);
		}
		if (args.size() > 1 || !trueCase) {
			proofLhs = res(rhsAtom, proofLhs, mProofRules.notElim(rhs));
		}
		// proofLhs: ~true/false, ~rhs, lhs.
		// proofRhs: ~true/false, ~lhs, rhs.
		final Term proof = proveIff(rewrite, proofRhs, proofLhs);
		return trueCase ? res(params[trueFalseIdx], mProofRules.trueIntro(), proof)
				: res(params[trueFalseIdx], proof, mProofRules.falseElim());
	}

	private Term convertRewriteToXor(final String rule, final Term rewrite, final Term lhs, final Term rhs) {
		// expect lhs: (=/distinct a b), rhs: (not? (xor a b))
		assert isApplication(rule == ":eqToXor" ? "=" : "distinct", lhs);
		Term xorTerm = rhs;
		if (rule == ":eqToXor") {
			xorTerm = negate(xorTerm);
		}
		assert isApplication("xor", xorTerm);
		final Term[] eqParams = ((ApplicationTerm) lhs).getParameters();
		final Term[] xorParams = ((ApplicationTerm) xorTerm).getParameters();
		assert xorParams.length == 2 && eqParams.length == 2;
		assert xorParams[0] == eqParams[0] && xorParams[1] == eqParams[1];
		final Term eqLhs = rewrite.getTheory().term("=", eqParams[0], eqParams[1]);
		final Term proofEqToNotXor = mProofRules.resolutionRule(eqParams[0],
				mProofRules.resolutionRule(eqParams[1],
						mProofRules.xorIntro(new Term[] { xorParams[0] }, new Term[] { xorParams[1] }, xorParams),
						mProofRules.iffElim1(eqLhs)),
				mProofRules.resolutionRule(eqParams[1], mProofRules.iffElim2(eqLhs),
						mProofRules.xorElim(new Term[] { xorParams[0] }, new Term[] { xorParams[1] }, xorParams)));
		final Term proofNotXorToEq = mProofRules.resolutionRule(eqParams[0],
				mProofRules.resolutionRule(eqParams[1], mProofRules.iffIntro1(eqLhs),
						mProofRules.xorIntro(xorParams, new Term[] { xorParams[0] }, new Term[] { xorParams[1] })),
				mProofRules.resolutionRule(eqParams[1],
						mProofRules.xorIntro(xorParams, new Term[] { xorParams[1] }, new Term[] { xorParams[0] }),
						mProofRules.iffIntro2(eqLhs)));
		final Term iffIntro1, iffIntro2;
		if (rule == ":eqToXor") {
			iffIntro1 = mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite), mProofRules.notElim(rhs));
			iffIntro2 = mProofRules.resolutionRule(rhs, mProofRules.notIntro(rhs), mProofRules.iffIntro2(rewrite));
		} else {
			iffIntro1 = mProofRules.resolutionRule(lhs, mProofRules.distinctIntro(lhs),
					mProofRules.iffIntro2(rewrite));
			iffIntro2 = mProofRules.resolutionRule(lhs, mProofRules.iffIntro1(rewrite),
					mProofRules.distinctElim(0, 1, lhs));
		}
		return mProofRules.resolutionRule(eqLhs, mProofRules.resolutionRule(xorTerm, proofNotXorToEq, iffIntro1),
				mProofRules.resolutionRule(xorTerm, iffIntro2, proofEqToNotXor));
	}

	private Term convertRewriteXorNot(final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (xor (not* arg0) (not* arg1)), rhs: (not? (xor arg0 arg1))
		final Theory theory = rewrite.getTheory();
		boolean rhsNegated = false;
		Term rhsAtom = rhs;
		if (isApplication(SMTLIBConstants.NOT, rhs)) {
			rhsNegated = !rhsNegated;
			rhsAtom = ((ApplicationTerm) rhs).getParameters()[0];
		}
		assert isApplication(SMTLIBConstants.XOR, lhs) && isApplication(SMTLIBConstants.XOR, rhsAtom);
		final Term[] lhsArgs = ((ApplicationTerm) lhs).getParameters();
		final Term[] rhsArgs = ((ApplicationTerm) rhsAtom).getParameters();
		final ArrayList<Term> pairs = new ArrayList<>();
		assert lhsArgs.length == rhsArgs.length;

		Term[] xorAllArgs = null;
		Term xorAll = null;
		Term proofXorAll = null;
		boolean xorAllNegated = false;
		// Build xorAll = xor(~p1, p1,...) for all literals negatedin lhs.
		// Build proof for polarity * xorAll.
		for (int i = 0; i < lhsArgs.length; i++) {
			// While lhsArg contains not, remove it, and switch polarity.
			// Then check it equals the corresponding rhsArg
			final Term lhsArg = lhsArgs[i];
			final Term rhsArg = rhsArgs[i];
			if (isApplication(SMTLIBConstants.NOT, lhsArg)) {
				Term arg = lhsArg;
				int numNegations = 0;
				while (isApplication(SMTLIBConstants.NOT, arg)) {
					arg = ((ApplicationTerm) arg).getParameters()[0];
					numNegations++;
				}
				assert arg == rhsArg;
				// prove -rhsArg, +/-lhsArg and +rhsArg, -/+lhsArg
				Term proofLhsNeg = null;
				Term proofLhsPos = null;
				arg = rhsArg;
				for (int ctr = 0; ctr < numNegations; ctr++) {
					final Term notArg = mSkript.term(SMTLIBConstants.NOT, arg);
					final Term nextProofLhsPos = res(arg, mProofRules.notIntro(notArg), proofLhsNeg);
					proofLhsNeg = res(arg, proofLhsPos, mProofRules.notElim(notArg));
					proofLhsPos = nextProofLhsPos;
					arg = notArg;
				}
				// prove +/-(xor lhsArgs[i] rhsArgs[i])
				final Term[] xorArgs = new Term[] { lhsArg, rhsArg };
				final Term xorTerm = theory.term(SMTLIBConstants.XOR, xorArgs);

				// and then prove (xor lhsArgs[0] rhsArgs[0]...lhsArgs[i] rhsArgs[i])
				pairs.add(lhsArg);
				pairs.add(rhsArg);
				final Term[] xorAllNextArgs = pairs.toArray(new Term[pairs.size()]);
				final Term xorAllNext = theory.term(SMTLIBConstants.XOR, xorAllNextArgs);
				boolean xorAllNextNegated;
				Term proofStep;
				if (numNegations % 2 == 0) {
					// prove - xor(lhsArg, rhsArg)
					final Term proofXor = mProofRules.resolutionRule(rhsArg,
							mProofRules.resolutionRule(lhsArg,
									mProofRules.xorIntro(new Term[] { lhsArg }, new Term[] { rhsArg }, xorArgs),
									proofLhsNeg),
							mProofRules.resolutionRule(lhsArg, proofLhsPos,
									mProofRules.xorElim(new Term[] { lhsArg }, new Term[] { rhsArg }, xorArgs)));
					if (xorAll == null) {
						proofStep = proofXor;
					} else {
						proofStep = xorAllNegated ? mProofRules.xorIntro(xorArgs, xorAllNextArgs, xorAllArgs)
								: mProofRules.xorIntro(xorArgs, xorAllArgs, xorAllNextArgs);
						proofStep = mProofRules.resolutionRule(xorTerm, proofStep, proofXor);
					}
					xorAllNextNegated = xorAllNegated;
				} else {
					final Term proofXor = mProofRules.resolutionRule(rhsArg,
							mProofRules.resolutionRule(lhsArg, proofLhsPos,
									mProofRules.xorIntro(xorArgs, new Term[] { rhsArg }, new Term[] { lhsArg })),
						mProofRules.resolutionRule(lhsArg,
									mProofRules.xorIntro(xorArgs, new Term[] { lhsArg }, new Term[] { rhsArg }),
									proofLhsNeg));
					// Now compute the proof for !polarity * xorAllNext
					if (xorAll == null) {
						proofStep = proofXor;
					} else {
						proofStep = xorAllNegated ? mProofRules.xorElim(xorAllNextArgs, xorAllArgs, xorArgs)
								: mProofRules.xorIntro(xorAllNextArgs, xorAllArgs, xorArgs);
						proofStep = mProofRules.resolutionRule(xorTerm, proofXor, proofStep);
					}
					xorAllNextNegated = !xorAllNegated;
				}
				proofXorAll = res(xorAll, xorAllNegated ? proofXorAll : proofStep,
						xorAllNegated ? proofStep : proofXorAll);
				xorAllArgs = xorAllNextArgs;
				xorAll = xorAllNext;
				xorAllNegated = xorAllNextNegated;
			} else {
				assert lhsArg == rhsArg;
			}
		}
		assert pairs.size() > 0;
		// The lemma is well-formed if all nots cancel out.
		assert rhsNegated == xorAllNegated;

		Term proof1, proof2;
		proof1 = mProofRules.xorIntro(lhsArgs, rhsNegated ? rhsArgs : xorAllArgs, rhsNegated ? xorAllArgs : rhsArgs);
		proof2 = rhsNegated ? mProofRules.xorElim(rhsArgs, xorAllArgs, lhsArgs)
				: mProofRules.xorIntro(rhsArgs, xorAllArgs, lhsArgs);
		if (rhsNegated) {
			proof1 = mProofRules.resolutionRule(rhsAtom, proof1, mProofRules.notElim(rhs));
			proof2 = mProofRules.resolutionRule(rhsAtom, mProofRules.notIntro(rhs), proof2);
		}

		final Term proof = mProofRules.resolutionRule(lhs,
				mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite),
						proof1),
				mProofRules.resolutionRule(rhs, proof2, mProofRules.iffIntro2(rewrite)));
		return mProofRules.resolutionRule(xorAll, xorAllNegated ? proofXorAll : proof, xorAllNegated ? proof : proofXorAll);
	}

	private Term convertRewriteXorConst(final String rewriteRule, final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (xor true/false arg1) or (xor arg0 true/false)
		assert isApplication("xor", lhs);
		final boolean isTrue = rewriteRule == ":xorTrue";
		final Term[] xorArgs = ((ApplicationTerm) lhs).getParameters();
		final int constIdx = isApplication(isTrue ? "true" : "false", xorArgs[0]) ? 0 : 1;
		final Term[] constArg = new Term[] { xorArgs[constIdx] };
		final Term[] otherArg = new Term[] { xorArgs[1 - constIdx] };
		if (isTrue) {
			assert isApplication("true", xorArgs[constIdx]) && rhs == mSkript.term("not", xorArgs[1 - constIdx]);
			final Term proof = proveIff(rewrite,
					mProofRules.resolutionRule(xorArgs[1 - constIdx], mProofRules.notIntro(rhs),
							mProofRules.xorElim(otherArg, xorArgs, constArg)),
					mProofRules.resolutionRule(xorArgs[1 - constIdx],
							mProofRules.xorIntro(otherArg, xorArgs, constArg), mProofRules.notElim(rhs)));
			return mProofRules.resolutionRule(xorArgs[constIdx], mProofRules.trueIntro(), proof);
		} else {
			assert isApplication("false", xorArgs[constIdx]) && rhs == xorArgs[1 - constIdx];
			final Term proof = proveIff(rewrite,
					mProofRules.xorIntro(otherArg, constArg, xorArgs),
					mProofRules.xorIntro(xorArgs, constArg, otherArg));
			return mProofRules.resolutionRule(xorArgs[constIdx], proof, mProofRules.falseElim());
		}
	}

	private Term convertRewriteXorSame(final Term rewrite, final Term lhs, final Term rhs) {
		assert isApplication("xor", lhs);
		final Term[] lhsArgs = ((ApplicationTerm) lhs).getParameters();
		assert lhsArgs.length == 2 && lhsArgs[0] == lhsArgs[1] && isApplication("false", rhs);
		return proveIffFalse(rewrite, mProofRules.xorElim(lhsArgs, lhsArgs, lhsArgs));
	}

	private Term convertRewriteEqSimp(final String rewriteRule, final Term lhs, final Term rhs) {
		// lhs: (= ...), rhs: (= ...) or true, if all entries in rhs are the same.
		// duplicated entries in lhs should be removed in rhs.
		assert isApplication("=", lhs);
		final Theory theory = lhs.getTheory();
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		final LinkedHashMap<Term, Integer> lhsTerms = new LinkedHashMap<>();
		for (int i = 0; i < lhsParams.length; i++) {
			lhsTerms.put(lhsParams[i], i);
		}
		if (lhsTerms.size() == 1) {
			assert rewriteRule.equals(":eqSame") && isApplication("true", rhs);
			Term proof = mProofRules.refl(lhsParams[0]);
			if (lhsParams.length > 2) {
				proof = res(theory.term("=", lhsParams[0], lhsParams[0]), proof, mProofRules.equalsIntro(lhs));
			}
			return proveIffTrue(theory.term("=", lhs, rhs), proof);
		} else {
			assert rewriteRule.equals(":eqSimp");
			assert isApplication("=", rhs);
			final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
			assert rhsParams.length == lhsTerms.size();

			final LinkedHashMap<Term, Integer> rhsTerms = new LinkedHashMap<>();
			for (int i = 0; i < rhsParams.length; i++) {
				rhsTerms.put(rhsParams[i], i);
			}

			Term proofLhsToRhs = mProofRules.equalsIntro(rhs);
			final HashSet<Term> seen = new HashSet<>();
			for (int i = 0; i < rhsParams.length - 1; i++) {
				final Term eq = theory.term("=", rhsParams[i], rhsParams[i + 1]);
				if (seen.add(eq)) {
					proofLhsToRhs = mProofRules.resolutionRule(eq,
							mProofRules.equalsElim(lhsTerms.get(rhsParams[i]), lhsTerms.get(rhsParams[i + 1]), lhs),
							proofLhsToRhs);
				}
			}
			seen.clear();
			Term proofRhsToLhs = mProofRules.equalsIntro(lhs);
			for (int i = 0; i < lhsParams.length - 1; i++) {
				final Term eq = theory.term("=", lhsParams[i], lhsParams[i + 1]);
				if (seen.add(eq)) {
					proofRhsToLhs = mProofRules.resolutionRule(eq,
							mProofRules.equalsElim(rhsTerms.get(lhsParams[i]), rhsTerms.get(lhsParams[i + 1]), rhs),
						proofRhsToLhs);
				}
			}
			return proveIff(theory.term("=", lhs, rhs), proofLhsToRhs, proofRhsToLhs);
		}
	}

	private Term convertRewriteEqBinary(final Term rewrite, final Term lhs, final Term rhs) {
		// eqBinary is like expand (chainable) combined with andToOr
		final Theory theory = lhs.getTheory();
		assert isApplication("=", lhs);
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		assert lhsParams.length >= 3;
		assert isApplication("not", rhs);
		final Term rhsAtom = ((ApplicationTerm) rhs).getParameters()[0];
		assert isApplication("or", rhsAtom);
		final Term[] rhsParams = ((ApplicationTerm) rhsAtom).getParameters();
		assert lhsParams.length == rhsParams.length + 1;

		final Term proof1 = mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite),
				mProofRules.notElim(rhs));
		Term proof2 = mProofRules.resolutionRule(rhs, mProofRules.notIntro(rhs), mProofRules.iffIntro2(rewrite));
		proof2 = mProofRules.resolutionRule(rhsAtom, proof2, mProofRules.orElim(rhsAtom));
		proof2 = mProofRules.resolutionRule(lhs, mProofRules.equalsIntro(lhs), proof2);
		// proof1: (= lhs rhs), lhs, ~rhsAtom
		// proof2: (= lhs rhs), ~(= lhs0 lhs1), ..., ~(= lhsn lhsn+1), rhsParam[0],...rhsParam[n]
		for (int i = 0; i < rhsParams.length; i++) {
			final Term eqi = theory.term("=", lhsParams[i], lhsParams[i + 1]);
			assert rhsParams[i] == theory.term("not", eqi);
			proof2 = mProofRules.resolutionRule(rhsParams[i], proof2, mProofRules.notElim(rhsParams[i]));
			proof2 = mProofRules.resolutionRule(eqi,
					mProofRules.resolutionRule(rhsParams[i], mProofRules.notIntro(rhsParams[i]),
					mProofRules.resolutionRule(rhsAtom, mProofRules.orIntro(i, rhsAtom),
									mProofRules.resolutionRule(lhs, proof1, mProofRules.equalsElim(i, i + 1, lhs)))),
					proof2);
			// proof2: (= lhs rhs), ~(= lhsi+1 lhsi+2), ..., ~(= lhsn lhsn+1), rhsParam[i+1],...rhsParam[n]
		}
		return proof2;
	}

	private Term convertRewriteDistinct(final String rewriteRule, final Term rewrite, final Term lhs, final Term rhs) {
		final Theory theory = lhs.getTheory();
		assert isApplication("distinct", lhs);
		final Term[] args = ((ApplicationTerm) lhs).getParameters();
		switch (rewriteRule) {
		case ":distinctBool":
			assert args.length > 2 && args[0].getSort().getName() == "Bool" && isApplication("false", rhs);
			final Term eq01 = theory.term("=", args[0], args[1]);
			final Term eq02 = theory.term("=", args[0], args[2]);
			final Term eq12 = theory.term("=", args[1], args[2]);
			final Term proof01 = mProofRules.distinctElim(0, 1, lhs);
			final Term proof02 = mProofRules.distinctElim(0, 2, lhs);
			final Term proof12 = mProofRules.distinctElim(1, 2, lhs);
			// Prove contradiction using the three equalities eq01, eq02, eq12.
			// Do case distinction over three boolean values and show that in each case one
			// equality needs to hold.
			Term proof =
					mProofRules.resolutionRule(args[0],
							mProofRules.resolutionRule(args[1], mProofRules.iffIntro1(eq01),
									mProofRules.resolutionRule(args[2], mProofRules.iffIntro1(eq02),
											mProofRules.iffIntro2(eq12))),
							mProofRules.resolutionRule(args[1], mProofRules.resolutionRule(args[2],
									mProofRules.iffIntro1(eq12), mProofRules.iffIntro2(eq02)),
									mProofRules.iffIntro2(eq01)));
			// Now use the fact that one of the equalities is false, to prove that distinct
			// is false.
			proof = mProofRules.resolutionRule(eq01,
					mProofRules.resolutionRule(eq02, mProofRules.resolutionRule(eq12, proof, proof12), proof02),
					proof01);
			proof = proveIffFalse(rewrite, proof);
			return proof;

		case ":distinctSame": {
			// (distinct ... x ... x ...) = false
			assert isApplication("false", rhs);
			final HashMap<Term,Integer> seen = new HashMap<>();
			for (int i = 0; i < args.length; i++) {
				final Integer otherIdx = seen.put(args[i], i);
				if (otherIdx != null) {
					final Term eq = theory.term("=", args[i], args[i]);
					return proveIffFalse(rewrite,
							res(eq, mProofRules.refl(args[i]),
									mProofRules.distinctElim(otherIdx, i, lhs)));
				}
			}
			throw new AssertionError();
		}
		case ":distinctBinary": {
			// (distinct x1 ... xn) = (not (or (= x1 x2) ... (= x1 xn) ... (= xn-1 xn)))
			final Term rhsAtom = negate(rhs);
			if (args.length == 2) {
				assert rhsAtom == mSkript.term("=", args[0], args[1]);
				final Term proof1 = mProofRules.resolutionRule(rhsAtom, mProofRules.distinctIntro(lhs),
						mProofRules.notElim(rhs));
				final Term proof2 = mProofRules.resolutionRule(rhsAtom, mProofRules.notIntro(rhs),
						mProofRules.distinctElim(0, 1, lhs));
				return mProofRules.resolutionRule(lhs,
						mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite), proof1),
						mProofRules.resolutionRule(rhs, proof2, mProofRules.iffIntro2(rewrite)));
			}
			assert isApplication("or", rhsAtom);
			final Term[] rhsArgs = ((ApplicationTerm) rhsAtom).getParameters();
			Term proof1 = mProofRules.distinctIntro(lhs);
			Term proof2 = mProofRules.resolutionRule(rhsAtom, mProofRules.notIntro(rhs),
					mProofRules.orElim(rhsAtom));
			int offset = 0;
			for (int i = 0; i < args.length - 1; i++) {
				for (int j = i + 1; j < args.length; j++) {
					assert offset < rhsArgs.length && rhsArgs[offset] == mSkript.term("=", args[i], args[j]);
					proof1 = mProofRules.resolutionRule(rhsArgs[offset], proof1,
							mProofRules.orIntro(offset, rhsAtom));
					proof2 = mProofRules.resolutionRule(rhsArgs[offset], proof2, mProofRules.distinctElim(i, j, lhs));
					offset++;
				}
			}
			proof1 = mProofRules.resolutionRule(rhsAtom, proof1, mProofRules.notElim(rhs));
			assert offset == rhsArgs.length;
			return proveIff(rewrite, proof2, proof1);
		}
		}
		throw new AssertionError();
	}

	private Term convertRewriteOrSimp(final Term rewriteStmt, final Term lhs, final Term rhs) {
		// lhs: (or ...), rhs: (or ...)
		// duplicated entries in lhs and false should be removed in rhs.
		// if only one entry remains, or is omitted, if no entry remains, false is
		// returned.
		assert isApplication("or", lhs);
		final LinkedHashMap<Term, Integer> args = new LinkedHashMap<>();
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		Term falseTerm = null;
		for (int i = 0; i < lhsParams.length; i++) {
			if (isApplication("false", lhsParams[i])) {
				falseTerm = lhsParams[i];
			} else {
				args.put(lhsParams[i], i);
			}
		}
		Term proofRhs = mProofRules.orElim(lhs);
		if (falseTerm != null && rhs != falseTerm) {
			proofRhs = mProofRules.resolutionRule(falseTerm, proofRhs, mProofRules.falseElim());
		}
		Term proofLhs = null;
		if (isApplication("false", rhs)) {
			proofLhs = mProofRules.falseElim();
		} else if (args.size() > 1) {
			assert isApplication("or", rhs);
			final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
			for (int i = 0; i < rhsParams.length; i++) {
				proofRhs = mProofRules.resolutionRule(rhsParams[i], proofRhs, mProofRules.orIntro(i, rhs));
			}
			proofLhs = mProofRules.orElim(rhs);
		}
		for (final int i : args.values()) {
			if (proofLhs == null) {
				proofLhs = mProofRules.orIntro(i, lhs);
			} else {
				proofLhs = mProofRules.resolutionRule(lhsParams[i], proofLhs, mProofRules.orIntro(i, lhs));
			}
		}
		return proveIff(rewriteStmt, proofRhs, proofLhs);
	}

	private Term convertRewriteOrTaut(final Term rewrite, final Term lhs, final Term rhs) {
		assert isApplication("or", lhs) && isApplication("true", rhs);
		// case 1
		// lhs: (or ... true ...), rhs: true
		// case 2
		// lhs: (or ... p ... (not p) ...), rhs: true
		Term proof = mProofRules.iffIntro2(rewrite);
		final HashMap<Term,Integer> seen = new HashMap<>();
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		for (int i = 0; i < lhsParams.length; i++) {
			if (isApplication("true", lhsParams[i])) {
				proof = mProofRules.resolutionRule(lhs, mProofRules.orIntro(i, lhs), proof);
				break;
			}
			final Integer otherIdx = seen.get(negate(lhsParams[i]));
			if (otherIdx != null) {
				int posIdx, negIdx;
				if (isApplication("not", lhsParams[i])) {
					negIdx = i;
					posIdx = otherIdx;
				} else {
					negIdx = otherIdx;
					posIdx = i;
				}
				final Term orProof = mProofRules.resolutionRule(
						lhsParams[posIdx], mProofRules.resolutionRule(lhsParams[negIdx],
								mProofRules.notIntro(lhsParams[negIdx]), mProofRules.orIntro(negIdx, lhs)),
						mProofRules.orIntro(posIdx, lhs));
				proof = mProofRules.resolutionRule(lhs, orProof, proof);
				break;
			}
			seen.put(lhsParams[i], i);
		}
		return mProofRules.resolutionRule(rhs, mProofRules.trueIntro(), proof);
	}

	private Term convertRewriteCanonicalSum(final Term lhs, final Term rhs) {
		final Theory theory = lhs.getTheory();
		if (lhs instanceof ConstantTerm) {
			return proveTrivialEquality(lhs, rhs);
		}

		final ApplicationTerm lhsApp = (ApplicationTerm) lhs;
		final Term[] lhsArgs = lhsApp.getParameters();
		switch (lhsApp.getFunction().getName()) {
		case "+":
			return mProofRules.polyAdd(lhs, rhs);
		case "*":
			return mProofRules.polyMul(lhs, rhs);
		case "to_real": {
			final Term expected = ProofRules.computePolyToReal(lhsArgs[0]);
			if (rhs == expected) {
				return mProofRules.toRealDef(lhs);
			} else {
				// difference can only be order of +
				return res(theory.term(SMTLIBConstants.EQUALS, lhs, expected),
						mProofRules.toRealDef(lhs),
						res(theory.term(SMTLIBConstants.EQUALS, expected, rhs),
								 mProofRules.polyAdd(expected, rhs),
								 mProofRules.trans(lhs, expected, rhs)));
			}
		}
		case "-": {
			final Term minusToPlus = ProofRules.computePolyMinus(lhs);
			if (minusToPlus == rhs) {
				return mProofRules.minusDef(lhs);
			}
			if (lhsArgs.length == 1) {
				final Term proof = res(theory.term(SMTLIBConstants.EQUALS, lhs, minusToPlus),
						mProofRules.minusDef(lhs), mProofRules.trans(lhs, minusToPlus, rhs));
				return res(theory.term(SMTLIBConstants.EQUALS, minusToPlus, rhs),
						mProofRules.polyMul(minusToPlus, rhs), proof);
			} else {
				final Term[] expectedArgs = new Term[lhsArgs.length];
				expectedArgs[0] = lhsArgs[0];
				for (int i = 1; i < lhsArgs.length; i++) {
					final SMTAffineTerm affineTerm = new SMTAffineTerm();
					affineTerm.add(Rational.MONE, lhsArgs[i]);
					expectedArgs[i] = affineTerm.toTerm(lhsArgs[i].getSort());
				}
				final Term expectedPlus = theory.term(SMTLIBConstants.PLUS, expectedArgs);
				Term proof;
				if (expectedPlus != rhs) {
					proof = res(theory.term(SMTLIBConstants.EQUALS, expectedPlus, rhs),
							mProofRules.polyAdd(expectedPlus, rhs),
							mProofRules.trans(lhs, minusToPlus, expectedPlus, rhs));
				} else {
					proof = mProofRules.trans(lhs, minusToPlus, expectedPlus);
				}
				proof = res(theory.term(SMTLIBConstants.EQUALS, lhs, minusToPlus), mProofRules.minusDef(lhs), proof);
				proof = res(theory.term(SMTLIBConstants.EQUALS, minusToPlus, expectedPlus),
						mProofRules.cong(minusToPlus, expectedPlus), proof);
				final HashSet<Term> seenEqs = new HashSet<>();
				final Term[] minusToPlusArgs = ((ApplicationTerm) minusToPlus).getParameters();
 				for (int i = 0; i < minusToPlusArgs.length; i++) {
					final Term eq = theory.term(SMTLIBConstants.EQUALS, minusToPlusArgs[i], expectedArgs[i]);
					if (seenEqs.add(eq)) {
						final Term proofEq = minusToPlusArgs[i] == expectedArgs[i]
								? mProofRules.refl(minusToPlusArgs[i])
										: mProofRules.polyMul(minusToPlusArgs[i], expectedArgs[i]);
						proof = res(eq, proofEq, proof);
					}
 				}
				return proof;
			}
		}
		case "/": {
			Term proofDivDef = mProofRules.divideDef(lhs);
			final Sort sort = lhs.getSort();
			final Term zero = Rational.ZERO.toTerm(sort);
			final Term[] mulTermArgs = new Term[lhsArgs.length];
			Rational multiplier = Rational.ONE;
			for (int i = 1; i < lhsArgs.length; i++) {
				final Term eqZero = theory.term(SMTLIBConstants.EQUALS, lhsArgs[i], zero);
				proofDivDef = res(eqZero, proofDivDef, proveTrivialDisequality(lhsArgs[i], zero));
				multiplier = multiplier.mul(parseConstant(lhsArgs[i]));
				mulTermArgs[i - 1] = lhsArgs[i];
			}
			mulTermArgs[mulTermArgs.length - 1] = lhs;
			Term mulTerm = theory.term("*", mulTermArgs);
			if (mulTermArgs.length > 2) {
				final Term mulShortTerm = theory.term("*", multiplier.toTerm(sort), lhs);
				proofDivDef = res(theory.term(SMTLIBConstants.EQUALS, mulShortTerm, mulTerm),
						res(theory.term(SMTLIBConstants.EQUALS, mulTerm, mulShortTerm),
								mProofRules.polyMul(mulTerm, mulShortTerm),
								mProofRules.symm(mulShortTerm, mulTerm)),
						mProofRules.trans(mulShortTerm, mulTerm, lhsArgs[0]));
				mulTerm = mulShortTerm;
			}
			// now mulTerm is (* multiplier lhs)
			// and proofDivDef is a proof for (= mulTerm lhsArgs[0])
			return res(theory.term(SMTLIBConstants.EQUALS, mulTerm, lhsArgs[0]), proofDivDef,
					proveEqWithMultiplier(new Term[] { mulTerm, lhsArgs[0] }, new Term[] { lhs, rhs },
							multiplier.inverse()));
		}
		default:
			throw new AssertionError();
		}
	}

	private Term convertRewriteToInt(final Term lhs, final Term rhs) {
		// (to_int constant) --> floor(constant)
		assert isApplication("to_int", lhs);
		final Term arg = ((ApplicationTerm) lhs).getParameters()[0];
		final Rational argConst = parseConstant(arg);
		final Rational rhsConst = parseConstant(rhs);
		assert argConst != null && rhsConst != null && rhsConst.equals(argConst.floor());

		// use trichotomy and toIntHigh/toIntLow and total-int
		final Theory theory = lhs.getTheory();
		final Term diffLhsRhs = theory.term(SMTLIBConstants.PLUS, lhs, rhsConst.negate().toTerm(rhs.getSort()));
		final Term lt = theory.term(SMTLIBConstants.LT, lhs, rhs);
		final Term gt = theory.term(SMTLIBConstants.LT, rhs, lhs);
		final Term leqDiffm1 = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, Rational.MONE.toTerm(rhs.getSort()));
		final Term geqDiff0 = theory.term(SMTLIBConstants.LEQ, Rational.ZERO.toTerm(rhs.getSort()), diffLhsRhs);
		final Term leqDiff0 = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, Rational.ZERO.toTerm(rhs.getSort()));
		final Term geqDiff1 = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(rhs.getSort()), diffLhsRhs);
		Term proof = mProofRules.trichotomy(lhs, rhs);
		final Term one = Rational.ONE.toTerm(arg.getSort());
		final Term toIntLowLeq = theory.term(SMTLIBConstants.LEQ, theory.term(SMTLIBConstants.TO_REAL, lhs), arg);
		final Term toIntHighLt = theory.term(SMTLIBConstants.LT, arg,
				theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.TO_REAL, lhs), one));
		final BigInteger[] coeffs = new BigInteger[] { BigInteger.ONE, BigInteger.ONE };
		proof = res(gt, proof, mProofRules.farkas(new Term[] { gt, leqDiff0 }, coeffs));
		proof = res(leqDiff0, mProofRules.totalInt(diffLhsRhs, BigInteger.ZERO), proof);
		proof = res(geqDiff1, proof, mProofRules.farkas(new Term[] { toIntLowLeq, geqDiff1 }, coeffs));
		proof = res(lt, proof, mProofRules.farkas(new Term[] { lt, geqDiff0 }, coeffs));
		proof = res(geqDiff0, mProofRules.totalInt(diffLhsRhs, BigInteger.ONE.negate()), proof);
		proof = res(leqDiffm1, proof, mProofRules.farkas(new Term[] { toIntHighLt, leqDiffm1 }, coeffs));
		proof = res(toIntLowLeq, mProofRules.toIntLow(arg), proof);
		proof = res(toIntHighLt, mProofRules.toIntHigh(arg), proof);
		return proof;
	}

	private Term convertRewriteStoreOverStore(final Term lhs, final Term rhs) {
		// lhs: (store (store a i v) i w)
		// rhs: (store a i w)
		assert isApplication("store", lhs);
		final Term[] outerArgs = ((ApplicationTerm) lhs).getParameters();
		final Term innerStore = outerArgs[0];
		final Term index = outerArgs[1];
		final Term valueW = outerArgs[2];
		assert isApplication("store", innerStore);
		final Term[] innerArgs = ((ApplicationTerm) innerStore).getParameters();
		final Term array = innerArgs[0];
		final Term innerIndex = innerArgs[1];
		final Term proofEq = proveTrivialEquality(index, innerIndex);
		assert proofEq != null;
		assert rhs == mSkript.term("store", array, index, valueW);

		final Theory theory = lhs.getTheory();
		final Term diff = theory.term("@diff", lhs, rhs);
		final Term selectLhsDiff = theory.term(SMTLIBConstants.SELECT, lhs, diff);
		final Term selectInnerDiff = theory.term(SMTLIBConstants.SELECT, innerStore, diff);
		final Term selectArrayDiff = theory.term(SMTLIBConstants.SELECT, array, diff);
		final Term selectRhsDiff = theory.term(SMTLIBConstants.SELECT, rhs, diff);
		final Term selectLhsI = theory.term(SMTLIBConstants.SELECT, lhs, index);
		final Term selectRhsI = theory.term(SMTLIBConstants.SELECT, rhs, index);


		// show (select lhs diff) = (select rhs diff) lhs if (= i diff)
		Term proof1 = mProofRules.trans(selectLhsDiff, selectLhsI, valueW, selectRhsI, selectRhsDiff);
		proof1 = res(theory.term("=", selectLhsDiff, selectLhsI), mProofRules.cong(selectLhsDiff, selectLhsI), proof1);
		proof1 = res(theory.term("=", lhs, lhs), mProofRules.refl(lhs), proof1);
		proof1 = res(theory.term("=", diff, index), mProofRules.symm(diff, index), proof1);
		proof1 = res(theory.term("=", selectLhsI, valueW), mProofRules.selectStore1(innerStore, index, valueW), proof1);
		proof1 = res(theory.term("=", valueW, selectRhsI), mProofRules.symm(valueW, selectRhsI), proof1);
		proof1 = res(theory.term("=", selectRhsI, valueW), mProofRules.selectStore1(array, index, valueW), proof1);
		proof1 = res(theory.term("=", selectRhsI, selectRhsDiff), mProofRules.cong(selectRhsI, selectRhsDiff), proof1);
		proof1 = res(theory.term("=", rhs, rhs), mProofRules.refl(rhs), proof1);

		// now the case ~(= i diff)
		Term proof2 = mProofRules.trans(selectLhsDiff, selectInnerDiff, selectArrayDiff, selectRhsDiff);
		proof2 = res(theory.term("=", selectLhsDiff, selectInnerDiff),
				mProofRules.selectStore2(innerStore, index, valueW, diff), proof2);
		proof2 = res(theory.term("=", selectInnerDiff, selectArrayDiff),
				mProofRules.selectStore2(array, innerIndex, innerArgs[2], diff), proof2);
		if (innerIndex != index) {
			proof2 = res(theory.term("=", innerIndex, diff), proof2, mProofRules.trans(index, innerIndex, diff));
			proof2 = res(theory.term("=", index, innerIndex), proofEq, proof2);
		}
		proof2 = res(theory.term("=", selectArrayDiff, selectRhsDiff),
				mProofRules.symm(selectArrayDiff, selectRhsDiff), proof2);
		proof2 = res(theory.term("=", selectRhsDiff, selectArrayDiff),
				mProofRules.selectStore2(array, index, valueW, diff), proof2);

		Term proof = res(theory.term("=", index, diff), proof2, proof1);
		proof = res(theory.term("=", selectLhsDiff, selectRhsDiff), proof, mProofRules.extDiff(lhs, rhs));
		return proof;
	}

	private Term convertRewriteSelectOverStore(final Term lhs, final Term rhs) {
		// lhs: (select (store a i v) j) i-j is a constant
		// rhs: (select a j) if i-j !=0. v if i-j = 0
		final Theory theory = lhs.getTheory();
		assert isApplication("select", lhs);
		final Term[] selectArgs = ((ApplicationTerm) lhs).getParameters();
		final Term store = selectArgs[0];
		assert isApplication("store", store);
		final Term[] storeArgs = ((ApplicationTerm) store).getParameters();
		final Term array = storeArgs[0];
		final Term indexI = storeArgs[1];
		final Term value = storeArgs[2];
		final Term indexJ = selectArgs[1];
		final Term proofEqualJI = proveTrivialEquality(indexJ, indexI);
		if (proofEqualJI != null) {
			assert rhs == storeArgs[2];
			final Term selectStoreI = theory.term("select", store, indexI);
			Term proof = mProofRules.trans(lhs, selectStoreI, value);
			proof = res(theory.term("=", lhs, selectStoreI), mProofRules.cong(lhs,  selectStoreI), proof);
			proof = res(theory.term("=", store, store), mProofRules.refl(store), proof);
			proof = res(theory.term("=", indexJ, indexI), proofEqualJI, proof);
			proof = res(theory.term("=", selectStoreI, value), mProofRules.selectStore1(array, indexI, value), proof);
			return proof;
		} else {
			final Term proofNotEqual = proveTrivialDisequality(indexI, indexJ);
			assert proofNotEqual != null;
			return res(theory.term("=", indexI, indexJ), mProofRules.selectStore2(array, indexI, value, indexJ),
					proofNotEqual);
		}
	}

	/**
	 * Explain an auxIntro rewrite rules of the form {@code (= def (@AUX x y))},
	 * where def is the definition of the {@code @AUX} application.
	 *
	 * @param lhs the definition.
	 * @param rhs the AUX application.
	 * @return the low-level proof for that statement.
	 */
	private Term convertRewriteAuxIntro(final Term rewrite, final Term lhs, final Term rhs) {
		final Term symmEq = mSkript.term(SMTLIBConstants.EQUALS, rhs, lhs);
		return res(symmEq, mProofRules.expand(rhs), mProofRules.symm(lhs, rhs));
	}

	private Term convertRewriteStore(final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (= (store a i v) a) (or symmetric)
		// rhs: (= (select a i) v)
		final Theory theory = lhs.getTheory();
		assert isApplication("=", lhs);
		final Term[] lhsArgs = ((ApplicationTerm) lhs).getParameters();
		final int storeIdx = isApplication("store", lhsArgs[0])
				&& ((ApplicationTerm) lhsArgs[0]).getParameters()[0] == lhsArgs[1] ? 0 : 1;
		final Term store = lhsArgs[storeIdx];
		final Term[] storeArgs = ((ApplicationTerm) store).getParameters();
		final Term array = storeArgs[0];
		final Term index = storeArgs[1];
		final Term value = storeArgs[2];
		assert isApplication("store", store) && array == lhsArgs[1 - storeIdx];

		final Term diff = theory.term("@diff", store, array);
		final Term selectArrayDiff = theory.term(SMTLIBConstants.SELECT, array, diff);
		final Term selectStoreDiff = theory.term(SMTLIBConstants.SELECT, store, diff);
		final Term selectArrayI = theory.term(SMTLIBConstants.SELECT, array, index);
		final Term selectStoreI = theory.term(SMTLIBConstants.SELECT, store, index);


		// show (select a i) = v if array = store
		Term proofRhs = res(theory.term("=", selectArrayI, selectStoreI),
				res(theory.term("=", index, index), mProofRules.refl(index),
						mProofRules.cong(selectArrayI, selectStoreI)),
						mProofRules.trans(selectArrayI, selectStoreI, value));

		// show (select store diff) = (select array diff) lhs if (= i diff)
		Term proofLhs = mProofRules.trans(selectStoreDiff, selectStoreI, value, selectArrayI, selectArrayDiff);
		proofLhs = res(theory.term("=", selectStoreDiff, selectStoreI),
				mProofRules.cong(selectStoreDiff, selectStoreI), proofLhs);
		proofLhs = res(theory.term("=", diff, index), mProofRules.symm(diff, index), proofLhs);
		proofLhs = res(theory.term("=", store, store), mProofRules.refl(store), proofLhs);
		proofLhs = res(theory.term("=", value, selectArrayI), mProofRules.symm(value, selectArrayI), proofLhs);
		proofLhs = res(theory.term("=", selectArrayI, selectArrayDiff),
				mProofRules.cong(selectArrayI, selectArrayDiff), proofLhs);
		proofLhs = res(theory.term("=", array, array), mProofRules.refl(array), proofLhs);

		// show (select store diff) = (select array diff) lhs also if ~(= i diff)
		proofLhs = res(theory.term("=", index, diff), mProofRules.selectStore2(array, index, value, diff), proofLhs);

		// hence store = array.
		proofLhs = res(theory.term("=", selectStoreDiff, selectArrayDiff),
				proofLhs, mProofRules.extDiff(store, array));

		// swap store and array according to lhs.
		if (storeIdx == 0) {
			proofRhs = res(theory.term("=", array, store), mProofRules.symm(array, store), proofRhs);
		} else {
			proofLhs = res(theory.term("=", store, array), proofLhs, mProofRules.symm(array, store));
		}
		Term proof = proveIff(rewrite, proofRhs, proofLhs);
		proof = res(theory.term("=", selectStoreI, value), mProofRules.selectStore1(array, index, value), proof);
		return proof;
	}

	private Term convertRewriteToLeq0(final String rewriteRule, final Term lhs, final Term rhs) {
		boolean isNegated;
		switch (rewriteRule) {
		case ":leqToLeq0":
			assert isApplication("<=", lhs);
			isNegated = false;
			break;
		case ":ltToLeq0":
			assert isApplication("<", lhs);
			isNegated = true;
			break;
		case ":geqToLeq0":
			assert isApplication(">=", lhs);
			isNegated = false;
			break;
		case ":gtToLeq0":
			assert isApplication(">", lhs);
			isNegated = true;
			break;
		default:
			throw new AssertionError();
		}
		final Term rhsAtom = isNegated ? negate(rhs) : rhs;
		assert isApplication("<=", rhsAtom);

		return proveRewriteWithLeq(lhs, rhs, false);
	}

	private Term convertRewriteIte(final String rewriteRule, final Term rewriteStmt, final Term ite, final Term rhs) {
		// lhs: (ite cond then else)
		assert isApplication("ite", ite);
		final Term[] args = ((ApplicationTerm) ite).getParameters();
		final Term cond = args[0];
		final Term t1 = args[1];
		final Term t2 = args[2];
		switch (rewriteRule) {
		case ":iteTrue":
			// (= (ite true t1 t2) t1)
			return mProofRules.resolutionRule(cond, mProofRules.trueIntro(), mProofRules.ite1(ite));
		case ":iteFalse":
			// (= (ite false t1 t2) t2)
			return mProofRules.resolutionRule(cond, mProofRules.ite2(ite), mProofRules.falseElim());
		case ":iteSame":
			// (= (ite cond t1 t1) t1)
			return mProofRules.resolutionRule(cond, mProofRules.ite2(ite), mProofRules.ite1(ite));
		case ":iteBool1": {
			// (= (ite cond true false) cond)
			assert isApplication("true", t1) && isApplication("false", t2) && rhs == cond;
			// show ~ite, cond by observing that ite2 is cond, (= ite false).
			final Term iteFalse = mSkript.term("=", ite, t2);
			Term proofRhs = mProofRules.resolutionRule(iteFalse, mProofRules.ite2(ite), mProofRules.iffElim2(iteFalse));
			proofRhs = mProofRules.resolutionRule(t2, proofRhs, mProofRules.falseElim());
			// show ite, ~cond by observing that ite1 is ~cond, (= ite true).
			final Term iteTrue = mSkript.term("=", ite, t1);
			Term proofLhs = mProofRules.resolutionRule(iteTrue, mProofRules.ite1(ite), mProofRules.iffElim1(iteTrue));
			proofLhs = mProofRules.resolutionRule(t1, mProofRules.trueIntro(), proofLhs);
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool2": {
			// (= (ite cond false true) (not cond))
			assert isApplication("false", t1) && isApplication("true", t2) && rhs == mSkript.term("not", cond);
			// show ~ite, not cond by observing that ite1 is ~cond, (= ite false).
			final Term iteFalse = mSkript.term("=", ite, t1);
			Term proofRhs = mProofRules.resolutionRule(iteFalse, mProofRules.ite1(ite), mProofRules.iffElim2(iteFalse));
			proofRhs = mProofRules.resolutionRule(t1, proofRhs, mProofRules.falseElim());
			proofRhs = mProofRules.resolutionRule(cond, mProofRules.notIntro(rhs), proofRhs);
			// show ite, ~not cond by observing that ite2 is cond, (= ite true).
			final Term iteTrue = mSkript.term("=", ite, t2);
			Term proofLhs = mProofRules.resolutionRule(iteTrue, mProofRules.ite2(ite), mProofRules.iffElim1(iteTrue));
			proofLhs = mProofRules.resolutionRule(t2, mProofRules.trueIntro(), proofLhs);
			proofLhs = mProofRules.resolutionRule(cond, proofLhs, mProofRules.notElim(rhs));
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool3": {
			// (= (ite cond true t2) (or cond t2))
			assert isApplication("true", t1) && rhs == mSkript.term("or", cond, t2);
			final Term iteTrue = mSkript.term("=", ite, t1);
			final Term iteT2 = mSkript.term("=", ite, t2);
			// show ~ite, (or cond t2) by case distinction over cond, t2
			final Term proofRhs = mProofRules
					.resolutionRule(cond,
							mProofRules.resolutionRule(t2,
									mProofRules.resolutionRule(iteT2, mProofRules.ite2(ite),
											mProofRules.iffElim2(iteT2)),
									mProofRules.orIntro(1, rhs)),
							mProofRules.orIntro(0, rhs));
			// show ite, ~(or cond t2) by case distinction over cond, t2
			Term proofLhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(t2, mProofRules.orElim(rhs),
							mProofRules.resolutionRule(iteT2, mProofRules.ite2(ite), mProofRules.iffElim1(iteT2))),
					mProofRules.resolutionRule(iteTrue, mProofRules.ite1(ite), mProofRules.iffElim1(iteTrue)));
			proofLhs = mProofRules.resolutionRule(t1, mProofRules.trueIntro(), proofLhs);
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool4": {
			// (= (ite cond false t2) (not (or cond (not t2))))
			assert isApplication("false", t1)
					&& rhs == mSkript.term("not", mSkript.term("or", cond, mSkript.term("not", t2)));
			final Term notRhs = ((ApplicationTerm) rhs).getParameters()[0];
			final Term notT2 = ((ApplicationTerm) notRhs).getParameters()[1];
			final Term iteFalse = mSkript.term("=", ite, t1);
			final Term iteT2 = mSkript.term("=", ite, t2);
			// show ~ite, (not (or cond (not t2))) by case distinction over cond, t2
			Term proofRhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(notT2, mProofRules.orElim(notRhs),
							mProofRules.resolutionRule(t2,
									mProofRules.resolutionRule(iteT2, mProofRules.ite2(ite),
											mProofRules.iffElim2(iteT2)),
									mProofRules.notElim(notT2))),
					mProofRules.resolutionRule(iteFalse, mProofRules.ite1(ite), mProofRules.iffElim2(iteFalse)));
			proofRhs = mProofRules.resolutionRule(t1, proofRhs, mProofRules.falseElim());
			proofRhs = mProofRules.resolutionRule(notRhs, mProofRules.notIntro(rhs), proofRhs);
			// show ite, ~(not (or cond (not t2)))) by case distinction over cond, t2
			Term proofLhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(t2,
							mProofRules.resolutionRule(notT2, mProofRules.notIntro(notT2),
									mProofRules.orIntro(1, notRhs)),
							mProofRules.resolutionRule(iteT2, mProofRules.ite2(ite), mProofRules.iffElim1(iteT2))),
					mProofRules.orIntro(0, notRhs));
			proofLhs = mProofRules.resolutionRule(notRhs, proofLhs, mProofRules.notElim(rhs));
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool5": {
			// (= (ite cond t1 true) (or (not cond) t1))
			final Term notCond = mSkript.term("not", cond);
			assert isApplication("true", t2) && rhs == mSkript.term("or", notCond, t1);
			final Term iteT1 = mSkript.term("=", ite, t1);
			final Term iteTrue = mSkript.term("=", ite, t2);
			// show ~ite, (or (not cond) t1) by case distinction over cond, t1
			final Term proofRhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(notCond, mProofRules.notIntro(notCond), mProofRules.orIntro(0, rhs)),
					mProofRules.resolutionRule(t1,
							mProofRules.resolutionRule(iteT1, mProofRules.ite1(ite), mProofRules.iffElim2(iteT1)),
							mProofRules.orIntro(1, rhs)));
			// show ite, ~(or (not cond) t1) by case distinction over cond, t1
			Term proofLhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(iteTrue, mProofRules.ite2(ite), mProofRules.iffElim1(iteTrue)),
					mProofRules.resolutionRule(t1,
							mProofRules.resolutionRule(notCond, mProofRules.orElim(rhs),
									mProofRules.notElim(notCond)),
							mProofRules.resolutionRule(iteT1, mProofRules.ite1(ite), mProofRules.iffElim1(iteT1))));
			proofLhs = mProofRules.resolutionRule(t2, mProofRules.trueIntro(), proofLhs);
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool6":
			// (= (ite cond t1 false) (not (or (not cond) (not t1))))
			assert isApplication("false", t2) && rhs == mSkript.term("not",
					mSkript.term("or", mSkript.term("not", cond), mSkript.term("not", t1)));
			final Term notRhs = ((ApplicationTerm) rhs).getParameters()[0];
			final Term notT1 = ((ApplicationTerm) notRhs).getParameters()[1];
			final Term notCond = ((ApplicationTerm) notRhs).getParameters()[0];
			final Term iteT1 = mSkript.term("=", ite, t1);
			final Term iteFalse = mSkript.term("=", ite, t2);
			// show ~ite, (not (or (not cond) (not t1))) by case distinction over cond, t1
			Term proofRhs =
					mProofRules.resolutionRule(cond, mProofRules.resolutionRule(iteFalse, mProofRules.ite2(ite), mProofRules.iffElim2(iteFalse)),
					mProofRules.resolutionRule(notCond,
									mProofRules.resolutionRule(notT1, mProofRules.orElim(notRhs),
							mProofRules.resolutionRule(t1,
									mProofRules.resolutionRule(iteT1, mProofRules.ite1(ite),
											mProofRules.iffElim2(iteT1)),
									mProofRules.notElim(notT1))),
									mProofRules.notElim(notCond)));
			proofRhs = mProofRules.resolutionRule(t2, proofRhs, mProofRules.falseElim());
			proofRhs = mProofRules.resolutionRule(notRhs, mProofRules.notIntro(rhs), proofRhs);
			// show ite, ~(not (or (not cond) (not t1)))) by case distinction over cond, t1
			Term proofLhs = mProofRules.resolutionRule(notCond,
					mProofRules.resolutionRule(cond, mProofRules.notIntro(notCond),
							mProofRules.resolutionRule(t1,
									mProofRules.resolutionRule(notT1, mProofRules.notIntro(notT1),
											mProofRules.orIntro(1, notRhs)),
									mProofRules.resolutionRule(iteT1, mProofRules.ite1(ite),
											mProofRules.iffElim1(iteT1)))),
					mProofRules.orIntro(0, notRhs));
			proofLhs = mProofRules.resolutionRule(notRhs, proofLhs, mProofRules.notElim(rhs));
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		throw new AssertionError();
	}

	private Term convertRewriteConstDiff(final Term rewriteStmt, final Term lhs, final Term rhs) {
		// lhs: (= ... 5 ... 7 ...), rhs: false
		assert isApplication("=", lhs) && isApplication("false", rhs);
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		assert lhsParams[0].getSort().isNumericSort();
		int lastConstantIdx = -1;
		Rational lastConstant = null;
		for (int i = 0; i < lhsParams.length; i++) {
			final Rational value = parseConstant(lhsParams[i]);
			if (value != null) {
				if (lastConstantIdx < 0) {
					lastConstantIdx = i;
					lastConstant = value;
				} else if (!lastConstant.equals(value)) {
					Term proof = proveTrivialDisequality(lhsParams[lastConstantIdx], lhsParams[i]);
					if (lhsParams.length > 2) {
						proof = mProofRules.resolutionRule(
								lhs.getTheory().term("=", lhsParams[lastConstantIdx], lhsParams[i]),
								mProofRules.equalsElim(lastConstantIdx, i, lhs), proof);
					}
					proof = proveIffFalse(rewriteStmt, proof);
					return proof;
				}
			}
		}
		throw new AssertionError();
	}

	private Term proveDivWithFarkas(final Term divTerm, final Term divResult) {
		final Theory theory = divTerm.getTheory();
		final Sort sort = divTerm.getSort();

		assert isApplication("div", divTerm);
		final Term[] divArgs = ((ApplicationTerm) divTerm).getParameters();
		assert divArgs.length == 2;
		final Rational divisor = parseConstant(divArgs[1]);
		assert divisor != null && divisor.isIntegral();

		// check that divResult is really syntactically the result of the division.
		// For (div x c) we compute (1/c * x - divResult), check that it is a constant
		// whose absolute value is less than one and that has the same sign as c.
		final Polynomial poly = new Polynomial();
		poly.add(Rational.MONE, divResult);
		poly.add(divisor.inverse(), divArgs[0]);
		assert poly.isConstant();
		final Rational remainder = poly.getConstant();
		assert remainder.abs().compareTo(Rational.ONE) < 0;
		assert remainder.signum() * divisor.signum() != -1;

		final Term zero = Rational.ZERO.toTerm(sort);
		final Term absDivArg = theory.term(SMTLIBConstants.ABS, divArgs[1]);
		final Term absDivisor = divisor.abs().toTerm(sort);
		final Term origDivLow = theory.term(SMTLIBConstants.LEQ, theory.term(SMTLIBConstants.MUL, divArgs[1], divTerm),
				divArgs[0]);
		final Term origDivHigh = theory.term(SMTLIBConstants.LT, divArgs[0],
				theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.MUL, divArgs[1], divTerm), absDivArg));
		final SMTAffineTerm diffAffine = new SMTAffineTerm(divTerm);
		diffAffine.add(Rational.MONE, divResult);
		final Term diffLhsRhs = diffAffine.toTerm(sort);
		Term proof = mProofRules.trichotomy(divTerm, divResult);
		Term ltLhsRhs = theory.term(SMTLIBConstants.LT, divTerm, divResult);
		Term gtLhsRhs = theory.term(SMTLIBConstants.LT, divResult, divTerm);
		final BigInteger[] oneone = new BigInteger[] { BigInteger.ONE, BigInteger.ONE };
		if (divisor.signum() < 0 || remainder.signum() != 0) {
			// we need total-int in the proof
			final Term leqLhsRhs = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, zero);
			final Term geqLhsRhsOne = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(sort), diffLhsRhs);
			proof = res(gtLhsRhs, proof, mProofRules.farkas(new Term[] { gtLhsRhs, leqLhsRhs }, oneone));
			proof = res(leqLhsRhs, mProofRules.totalInt(diffLhsRhs, BigInteger.ZERO), proof);
			gtLhsRhs = geqLhsRhsOne;
		}
		if (divisor.signum() > 0 || remainder.signum() != 0) {
			// we need total-int in the proof
			final Term geqLhsRhs = theory.term(SMTLIBConstants.LEQ, zero, diffLhsRhs);
			final Term leqLhsRhsOne = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, Rational.MONE.toTerm(sort));
			proof = res(ltLhsRhs, proof, mProofRules.farkas(new Term[] { ltLhsRhs, geqLhsRhs }, oneone));
			proof = res(geqLhsRhs, mProofRules.totalInt(diffLhsRhs, BigInteger.ONE.negate()), proof);
			ltLhsRhs = leqLhsRhsOne;
		}
		final Term lhsRhsLow = divisor.signum() > 0 ? gtLhsRhs : ltLhsRhs;
		final Term lhsRhsHigh = divisor.signum() > 0 ? ltLhsRhs : gtLhsRhs;
		final BigInteger[] coeffs = new BigInteger[] { BigInteger.ONE, divisor.abs().numerator() };
		final BigInteger[] coeffs3 = new BigInteger[] { BigInteger.ONE, divisor.abs().numerator(), BigInteger.ONE };
		final Term eqAbs = theory.term(SMTLIBConstants.EQUALS, absDivArg, absDivisor);
		proof = res(lhsRhsLow, proof, mProofRules.farkas(new Term[] { origDivLow, lhsRhsLow }, coeffs));
		proof = res(lhsRhsHigh, proof,
				mProofRules.farkas(new Term[] { origDivHigh, lhsRhsHigh, eqAbs }, coeffs3));
		proof = res(eqAbs, proveAbsConstant(divisor, sort), proof);
		proof = res(origDivHigh, mProofRules.divHigh(divArgs[0], divArgs[1]), proof);
		proof = res(origDivLow, mProofRules.divLow(divArgs[0], divArgs[1]), proof);
		return proof;
	}

	private Term convertRewriteDiv(final String ruleName, final Term lhs, final Term rhs) {
		// div1: (div x 1) -> x
		// div-1: (div x (- 1)) -> (- x)
		// divConst: (div c1 c2) -> c where c1,c2 are constants, c = (div c1 c2)
		assert isApplication("div", lhs);
		final Term[] divArgs = ((ApplicationTerm) lhs).getParameters();
		assert divArgs.length == 2;
		final Rational divisor = parseConstant(divArgs[1]);
		assert divisor != null && divisor.isIntegral();

		final Theory theory = lhs.getTheory();
		final Term zero = Rational.ZERO.toTerm(lhs.getSort());
		return res(theory.term(SMTLIBConstants.EQUALS, divArgs[1], zero), proveDivWithFarkas(lhs, rhs),
				proveTrivialDisequality(divArgs[1], zero));
	}

	private Term convertRewriteModulo(final String ruleName, final Term lhs, final Term rhs) {
		// mod1: (div x 1) -> 0
		// mod-1: (div x (- 1)) -> 0
		// moduloConst: (mod c1 c2) -> c where c1,c2 are constants, c = (mod c1 c2)
		// modulo: (mod x c) -> (- x (* c (div x c)))
		assert isApplication("mod", lhs);
		final Term[] modArgs = ((ApplicationTerm) lhs).getParameters();
		assert modArgs.length == 2;
		final Term divTerm = lhs.getTheory().term("div", modArgs);
		final Rational divisor = parseConstant(modArgs[1]);
		assert divisor != null && divisor != Rational.ZERO;
		final Theory theory = lhs.getTheory();
		final Sort sort = lhs.getSort();
		Term proof = mProofRules.modDef(modArgs[0], modArgs[1]);
		final Term zero = Rational.ZERO.toTerm(sort);
		// proof shows (+ (* c (div x c)) (mod x c)) = x
		final Term divPlusMod = theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.MUL, modArgs[1], divTerm), lhs);
		final Term modDefEq = theory.term(SMTLIBConstants.EQUALS, divPlusMod, modArgs[0]);
		final SMTAffineTerm affine = new SMTAffineTerm(modArgs[0]);
		affine.add(divisor.negate(), divTerm);
		Term divResult;
		switch (ruleName) {
		case ":modulo1": {
			assert divisor.equals(Rational.ONE) && isZero(rhs);
			divResult = modArgs[0];
			break;
		}
		case ":modulo-1": {
			assert divisor.equals(Rational.MONE) && isZero(rhs);
			final SMTAffineTerm negX = new SMTAffineTerm(modArgs[0]);
			negX.negate();
			divResult = negX.toTerm(sort);
			break;
		}
		case ":moduloConst": {
			final Rational dividend = parseConstant(modArgs[0]);
			Rational quotient = dividend.div(divisor.abs()).floor();
			if (divisor.signum() < 0) {
				quotient = quotient.negate();
			}
			divResult = quotient.toTerm(sort);
			break;
		}
		case ":modulo":
			assert new SMTAffineTerm(rhs).equals(affine);
			divResult = divTerm;
			break;
		default:
			throw new AssertionError();
		}
		final Term middle = divResult == divTerm ? rhs : affine.toTerm(sort);
		proof = res(modDefEq, proof,
				proveEqWithMultiplier(new Term[] { divPlusMod, modArgs[0] }, new Term[] { lhs, middle }, Rational.ONE));
		if (divResult != divTerm) {
			final Term proof2 = res(theory.term(SMTLIBConstants.EQUALS, divTerm, divResult),
					proveDivWithFarkas(divTerm, divResult),
					proveEqWithMultiplier(new Term[] { divTerm, divResult }, new Term[] { middle, rhs },
							divisor.negate()));
			proof = res(theory.term(SMTLIBConstants.EQUALS, lhs, middle), proof,
					res(theory.term(SMTLIBConstants.EQUALS, middle, rhs), proof2,
							mProofRules.trans(lhs, middle, rhs)));
		}
		proof = res(theory.term(SMTLIBConstants.EQUALS, modArgs[1], zero), proof,
				proveTrivialDisequality(modArgs[1], zero));
		return proof;
	}

	private Term convertRewriteDivisible(final String ruleName, final Term lhs, final Term rhs) {
		// ((_ divisible n) x) --> (= x (* n (div x n)))
		assert isApplication("divisible", lhs);
		final BigInteger divisor = new BigInteger(((ApplicationTerm) lhs).getFunction().getIndices()[0]);
		final Term arg = ((ApplicationTerm) lhs).getParameters()[0];
		final Term proof = mProofRules.divisible(divisor, arg);

		if (isApplication(SMTLIBConstants.EQUALS, rhs)) {
			// assume that the proof is done.
			return proof;
		}

		final Theory theory = lhs.getTheory();
		final Rational divisorRat = Rational.valueOf(divisor, BigInteger.ONE);
		final Term divisorTerm = divisorRat.toTerm(arg.getSort());
		final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisorTerm);
		final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisorTerm, divTerm);
		final Term equalTerm = theory.term(SMTLIBConstants.EQUALS, arg, mulDivTerm);
		final Term eqRhs = theory.term(SMTLIBConstants.EQUALS, equalTerm, rhs);

		final Term proof2;
		if (isApplication(SMTLIBConstants.FALSE, rhs)) {
			/* divisible is rewritten to false */
			// show ~(= x (* n (div x n)))
			assert isApplication(SMTLIBConstants.FALSE, rhs);
			proof2 = res(rhs,
					res(equalTerm, mProofRules.iffIntro1(eqRhs), proveTrivialDisequality(arg, mulDivTerm)),
					mProofRules.falseElim());
		} else {
			/* divisible is rewritten to true */
			assert isApplication(SMTLIBConstants.TRUE, rhs);
			final Term trueTerm = rhs;

			final Polynomial divResultPoly = new Polynomial(arg);
			divResultPoly.mul(divisorRat.inverse());
			assert divResultPoly.getGcd().isIntegral() && divResultPoly.getConstant().isIntegral();
			final Term divResult = divResultPoly.toTerm(arg.getSort());
			final Term zero = Rational.ZERO.toTerm(arg.getSort());

			// show (= x (* n (div x n)))
			Term proofEquality = res(theory.term(SMTLIBConstants.EQUALS, divTerm, divResult),
					proveDivWithFarkas(divTerm, divResult), proveEqWithMultiplier(new Term[] { divTerm, divResult },
							new Term[] { arg, mulDivTerm }, divisorRat.negate()));
			proofEquality = res(theory.term(SMTLIBConstants.EQUALS, divisorTerm, zero), proofEquality,
					proveTrivialDisequality(divisorTerm, zero));
			proof2 = res(trueTerm, mProofRules.trueIntro(),
					res(equalTerm, proofEquality, mProofRules.iffIntro2(eqRhs)));
		}
		return res(eqRhs, proof2, res(theory.term(SMTLIBConstants.EQUALS, lhs, equalTerm), proof,
				mProofRules.trans(lhs, equalTerm, rhs)));
	}

	private Term convertRewrite(final Term lhs, Term rhs, Annotation annot) {
		final Term rewriteStmt = lhs.getTheory().term("=", lhs, rhs);
		final String rewriteRule = annot.getKey();
		assert isApplication(SMTLIBConstants.EQUALS, rewriteStmt);
		Term subProof;

		switch (rewriteRule) {
		case ":expand":
		case ":expandDef":
			subProof = mProofRules.expand(lhs);
			break;
		case ":intern":
			subProof = convertRewriteIntern(lhs, rhs);
			break;
		case ":notSimp":
			subProof = convertRewriteNot(rewriteStmt, lhs, rhs);
			break;
		case ":trueNotFalse":
			subProof = convertRewriteTrueNotFalse(lhs, rhs);
			break;
		case ":eqTrue":
		case ":eqFalse":
			subProof = convertRewriteEqTrueFalse(rewriteRule, lhs, rhs);
			break;
		case ":eqSimp":
		case ":eqSame":
			subProof = convertRewriteEqSimp(rewriteRule, lhs, rhs);
			break;
		case ":eqBinary":
			subProof = convertRewriteEqBinary(rewriteStmt, lhs, rhs);
			break;
		case ":eqToXor":
		case ":distinctToXor":
			subProof = convertRewriteToXor(rewriteRule, rewriteStmt, lhs, rhs);
			break;
		case ":xorTrue":
		case ":xorFalse":
			subProof = convertRewriteXorConst(rewriteRule, rewriteStmt, lhs, rhs);
			break;
		case ":xorNot":
			subProof = convertRewriteXorNot(rewriteStmt, lhs, rhs);
			break;
		case ":xorSame":
			subProof = convertRewriteXorSame(rewriteStmt, lhs, rhs);
			break;
		case ":orSimp":
			subProof = convertRewriteOrSimp(rewriteStmt, lhs, rhs);
			break;
		case ":orTaut":
			subProof = convertRewriteOrTaut(rewriteStmt, lhs, rhs);
			break;
		case ":distinctBool":
		case ":distinctSame":
		case ":distinctBinary":
			subProof = convertRewriteDistinct(rewriteRule, rewriteStmt, lhs, rhs);
			break;
		case ":leqTrue":
		case ":leqFalse":
			subProof = convertRewriteLeq(rewriteRule, rewriteStmt, lhs, rhs);
			break;
		case ":leqToLeq0":
		case ":ltToLeq0":
		case ":geqToLeq0":
		case ":gtToLeq0":
			subProof = convertRewriteToLeq0(rewriteRule, lhs, rhs);
			break;
		case ":iteTrue":
		case ":iteFalse":
		case ":iteSame":
		case ":iteBool1":
		case ":iteBool2":
		case ":iteBool3":
		case ":iteBool4":
		case ":iteBool5":
		case ":iteBool6":
			subProof = convertRewriteIte(rewriteRule, rewriteStmt, lhs, rhs);
			break;
		case ":constDiff":
			subProof = convertRewriteConstDiff(rewriteStmt, lhs, rhs);
			break;
		case ":strip":
			subProof = mProofRules.delAnnot(lhs);
			break;
		case ":canonicalSum":
			subProof = convertRewriteCanonicalSum(lhs, rhs);
			break;
		case ":toInt":
			subProof = convertRewriteToInt(lhs, rhs);
			break;
		case ":div1":
		case ":div-1":
		case ":divConst":
			subProof = convertRewriteDiv(rewriteRule, lhs, rhs);
			break;
		case ":modulo1":
		case ":modulo-1":
		case ":moduloConst":
		case ":modulo":
			subProof = convertRewriteModulo(rewriteRule, lhs, rhs);
			break;
		case ":divisible":
			subProof = convertRewriteDivisible(rewriteRule, lhs, rhs);
			break;
		case ":storeOverStore":
			subProof = convertRewriteStoreOverStore(lhs, rhs);
			break;
		case ":selectOverStore":
			subProof = convertRewriteSelectOverStore(lhs, rhs);
			break;
		case ":storeRewrite":
			subProof = convertRewriteStore(rewriteStmt, lhs, rhs);
			break;
		case ":auxIntro":
			subProof = convertRewriteAuxIntro(rewriteStmt, lhs, rhs);
			break;
		default:
			subProof = mProofRules.oracle(termToProofLiterals(rewriteStmt), new Annotation[] { annot });
		}
		assert checkProof(subProof, termToProofLiterals(rewriteStmt));
		return annotateProved(rewriteStmt, subProof);
	}

	/**
	 * Convert a Farkas lemma.
	 *
	 * @param clause       the clause to convert
	 * @param coefficients the argument of the :LA annotation, which is the list of
	 *                     Farkas coefficients.
	 */
	private Term convertLALemma(final ProofLiteral[] clause, final Term[] coefficients) {
		assert clause.length == coefficients.length;
		final Theory theory = mSkript.getTheory();
		final BigInteger[] coeffs = new BigInteger[coefficients.length];
		final Term[] atoms = new Term[clause.length];
		final Term[] realAtoms = new Term[clause.length];
		final Term[] realAtomProofs = new Term[clause.length];

		for (int i = 0; i < clause.length; i++) {
			final Rational coeff = parseConstant(coefficients[i]);
			assert coeff.isIntegral() && coeff != Rational.ZERO;
			coeffs[i] = coeff.numerator().abs();

			final boolean isNegated = !clause[i].getPolarity();
			final Term atom = clause[i].getAtom();
			final Term[] atomParams = ((ApplicationTerm) atom).getParameters();
			Term realAtom;
			Term realAtomProof;

			if (isApplication("=", atom)) {
				assert isNegated;
				if (coeff.signum() > 0) {
					realAtom = theory.term(SMTLIBConstants.EQUALS, atomParams[0], atomParams[1]);
					realAtomProof = null;
				} else {
					realAtom = theory.term(SMTLIBConstants.EQUALS, atomParams[1], atomParams[0]);
					realAtomProof = mProofRules.symm(atomParams[1], atomParams[0]);
				}
			} else if (isNegated) {
				assert coeff.signum() > 0;
				realAtom = atom;
				realAtomProof = null;
			} else {
				assert coeff.signum() < 0;
				if (isApplication("<=", atom)) {
					final Sort sort = atomParams[0].getSort();
					if (sort.getName().equals(SMTLIBConstants.INT)) {
						assert isZero(atomParams[1]);
						realAtom = theory.term("<=", Rational.ONE.toTerm(sort), atomParams[0]);
						realAtomProof = mProofRules.totalInt(atomParams[0], BigInteger.ZERO);
					} else {
						realAtom = theory.term("<", atomParams[1], atomParams[0]);
						realAtomProof = mProofRules.total(atomParams[0],  atomParams[1]);
					}
				} else {
					realAtom = theory.term("<=", atomParams[1], atomParams[0]);
					realAtomProof = mProofRules.total(atomParams[1],  atomParams[0]);
				}
			}
			realAtoms[i] = realAtom;
			realAtomProofs[i] = realAtomProof;
			atoms[i] = atom;
		}
		Term proof = mProofRules.farkas(realAtoms, coeffs);
		for (int i = 0; i < atoms.length; i++) {
			proof = res(realAtoms[i], realAtomProofs[i], proof);
		}
		return proof;
	}

	/**
	 * Convert a trichotomy lemma to a proof.
	 *
	 * @param clause
	 *            the clause to check.
	 */
	private Term convertTrichotomy(final ProofLiteral[] clause) {
		assert clause.length == 3;
		final Theory theory = clause[0].getAtom().getTheory();
		Term eq = null;
		Term lt = null;
		Term gt = null;
		for (final ProofLiteral lit : clause) {
			final boolean isPositive = lit.getPolarity();
			final Term atom = lit.getAtom();
			assert isZero(((ApplicationTerm) atom).getParameters()[1]);

			if (isApplication("=", atom)) {
				assert isPositive && eq == null;
				eq = atom;
			} else if (isApplication("<=", atom) || isApplication("<", atom)) {
				if (isPositive) {
					assert lt == null;
					lt = atom;
				} else {
					assert gt == null;
					gt = atom;
				}
			} else {
				throw new AssertionError();
			}
		}
		final Term[] sides = ((ApplicationTerm) eq).getParameters();
		Term proof = mProofRules.trichotomy(sides[0], sides[1]);
		// gt term needs to be negated
		final Term realGt = theory.term("<", sides[1], sides[0]);
		proof = mProofRules.resolutionRule(realGt, proof,
				mProofRules.farkas(new Term[] { realGt, gt }, new BigInteger[] { BigInteger.ONE, BigInteger.ONE }));
		// lt may need to be converted to <=
		if (isApplication("<=", lt)) {
			final Term[] ltSides = ((ApplicationTerm) lt).getParameters();
			assert isZero(ltSides[1]);
			final Term one = Rational.ONE.toTerm(ltSides[0].getSort());
			// the literal in the new trichotomoy clause
			final Term realLt = theory.term("<", sides[0], sides[1]);
			// the other literal in the ltInt clause that we need to show with farkas.
			final Term realLeq = theory.term("<=", one, ltSides[0]);
			proof = mProofRules.resolutionRule(realLt, proof,
					mProofRules.resolutionRule(realLeq, mProofRules.totalInt(ltSides[0], BigInteger.ZERO),
							mProofRules.farkas(new Term[] { realLeq, realLt },
									new BigInteger[] { BigInteger.ONE, BigInteger.ONE })));
		}
		return proof;
	}

	/**
	 * Convert a trivial EQ lemma to minimal proof. A trivial EQ lemma is an EQ
	 * lemma where the LA part is missing, since it normalizes to an obvious
	 * inconsistency (integer variable equals proper fraction).
	 *
	 * @param clause the clause to check
	 * @return the proof.
	 */
	private Term convertEQTrivialLemma(final ProofLiteral[] clause) {
		assert clause.length == 1;
		assert !clause[0].getPolarity();
		assert isApplication("=", clause[0].getAtom());
		final ApplicationTerm eqTerm = (ApplicationTerm) clause[0].getAtom();
		return proveTrivialDisequality(eqTerm.getParameters()[0], eqTerm.getParameters()[1]);
	}

	/**
	 * Convert an EQ lemma to minimal proof.
	 *
	 * @param clause the clause to check
	 * @return the proof.
	 */
	private Term convertEQLemma(final ProofLiteral[] clause) {
		if (clause.length == 1) {
			return convertEQTrivialLemma(clause);
		}
		assert clause.length == 2;
		final int posNr = clause[0].getPolarity() ? 0 : 1;
		final int negNr = 1 - posNr;
		assert clause[1].getPolarity() == (posNr == 1);
		assert isApplication("=", clause[0].getAtom()) && isApplication("=", clause[1].getAtom());

		final Term[] negAtomArgs = ((ApplicationTerm) clause[negNr].getAtom()).getParameters();
		final Term[] posAtomArgs = ((ApplicationTerm) clause[posNr].getAtom()).getParameters();
		final SMTAffineTerm negDiff = new SMTAffineTerm(negAtomArgs[0]);
		negDiff.add(Rational.MONE, negAtomArgs[1]);
		final SMTAffineTerm posDiff = new SMTAffineTerm(posAtomArgs[0]);
		posDiff.add(Rational.MONE, posAtomArgs[1]);
		Rational multiplier = posDiff.getGcd().div(negDiff.getGcd());
		negDiff.mul(multiplier);
		if (!negDiff.equals(posDiff)) {
			negDiff.negate();
			multiplier = multiplier.negate();
		}
		assert negDiff.equals(posDiff);
		final Term proof = proveEqWithMultiplier(negAtomArgs, posAtomArgs, multiplier);
		return proof;
	}

	/**
	 *  Collect literals in a CC or array lemma clause
	 *
	 *  @param clause the clause.
	 *  @param equalities  HashMap to store equalities (negated in the clause).
	 *  @param disequalities HashMap to store disequalities (positive in the clause).
	 */
	private void collectEqualities(final ProofLiteral[] clause, final HashMap<SymmetricPair<Term>, Term> equalities,
			final HashMap<SymmetricPair<Term>, Term> disequalities) {
		for (final ProofLiteral literal : clause) {
			final Term atom = literal.getAtom();
			assert isApplication("=", atom);
			final Term[] sides = ((ApplicationTerm) atom).getParameters();
			assert sides.length == 2;
			if (literal.getPolarity()) {
				// positive in clause -> disequality in conflict
				disequalities.put(new SymmetricPair<>(sides[0], sides[1]), atom);
			} else {
				// negated atom in clause -> equality in conflict
				equalities.put(new SymmetricPair<>(sides[0], sides[1]), atom);
			}
		}
	}

	/**
	 * Convert a CC lemma to a minimal proof.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :CC annotation.
	 */
	private Term convertCCLemma(final ProofLiteral[] clause, String lemmaType, final Term[] mainPath) {
		assert mainPath.length >= 2 : "Main path too short in CC lemma";

		// The goal equality
		final Theory theory = mainPath[0].getTheory();

		/* collect literals and search for the disequality */
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);
		assert allDisequalities.size() <= 1;


		Term proof;
		final HashSet<Term> neededEqualities = new HashSet<>();
		if (mainPath.length == 2) {
			assert lemmaType == ":cong" : "Transitivity lemma must have at least three steps";
			// This must be a congruence lemma
			assert mainPath[0] instanceof ApplicationTerm && mainPath[1] instanceof ApplicationTerm;
			final ApplicationTerm lhs = (ApplicationTerm) mainPath[0];
			final ApplicationTerm rhs = (ApplicationTerm) mainPath[1];
			proof = mProofRules.cong(lhs, rhs);

			// check that functions are the same and have the same number of parameters
			assert lhs.getFunction() == rhs.getFunction() && lhs.getParameters().length == rhs.getParameters().length;
			// check if each parameter is identical or equal
			final Term[] lhsParams = lhs.getParameters();
			final Term[] rhsParams = rhs.getParameters();
			assert lhsParams.length == rhsParams.length;
			for (int i = 0; i < lhsParams.length; i++) {
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, lhsParams[i], rhsParams[i]));
			}
		} else {
			assert lemmaType == ":trans" : "Congruence lemma must have a main path of length 2";
			// This is a transitivity lemma
			proof = mProofRules.trans(mainPath);
			for (int i = 0; i < mainPath.length - 1; i++) {
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, mainPath[i], mainPath[i + 1]));
			}
		}
		final Term mainPathEquality = theory.term("=", mainPath[0], mainPath[mainPath.length - 1]);
		final Set<Term> neededDisequalities = Collections.singleton(mainPathEquality);
		proof = resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
		return proof;
	}

	/**
	 * Check if array[weakIdx] is value, either because value is a congruent select
	 * term, or array is a constant array on value. Prove the equality
	 * {@code array[weakIdx] = value}.
	 *
	 * @param value            the value that should be equal to array[weakIdx].
	 * @param array            the array.
	 * @param weakIdx          the index of the array select.
	 * @param allEqualities    the known equalities from the lemma.
	 * @param neededEqualities the needed equalities that the proof depends on.
	 *
	 * @return the proof for {@code array[weakIdx] = value}, or null if no such
	 *         proof exists. The proof may use some equalities that are added to
	 *         neededEqualities.
	 */
	private Term proveSelectConst(final Term value, final Term array, final Term weakIdx,
			final Set<SymmetricPair<Term>> allEqualities, final Set<Term> neededEqualities) {
		final Theory theory = value.getTheory();
		// Check if value is (select array idx2) with (weakIdx = idx2) in equalities or
		// syntactically equal.
		if (isApplication("select", value)) {
			final Term[] args = ((ApplicationTerm) value).getParameters();
			if (args[0] == array) {
				if (args[1] == weakIdx) {
					return mProofRules.refl(value);
				}
				if (allEqualities.contains(new SymmetricPair<>(weakIdx, args[1]))) {
					neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, array, array));
					neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, weakIdx, args[1]));
					return mProofRules.cong(theory.term(SMTLIBConstants.SELECT, array, weakIdx), value);
				}
			}
		}
		// Check if array is (const value)
		if (isApplication(SMTLIBConstants.CONST, array) && ((ApplicationTerm) array).getParameters()[0] == value) {
			return mProofRules.constArray(value, weakIdx);
		}
		return null;
	}

	/**
	 * Prove {@code (select arrayLeft weakIdx) = (select arrayRight weakIdx)}, using
	 * transitivity and some symmetry rules. It assumes that value1 = value2 is a
	 * equality that can just be added to neededEqualities.
	 *
	 * @param arrayLeft        the left array of the step.
	 * @param value1           the side of the select equality that matches the left
	 *                         select.
	 * @param value2           the side of the select equality that matches the
	 *                         right select.
	 * @param arrayRight       the right array of the step.
	 * @param weakIdx          the weak path index.
	 * @param proofLeft        proof for {@pre (select arrayLeft weakIdx) = value1}.
	 * @param proofRight       proof for {@pre (select arrayRight weakIdx) =
	 *                         value2}.
	 * @param neededEqualities a set into which needed equalities are added.
	 * @return the proof for the equality between the two selects. The proof uses
	 *         the equality between value1 and value2, which it adds to
	 *         neededEqualities.
	 */
	private Term proveSelectPathTrans(final Term arrayLeft, final Term value1, final Term value2, final Term arrayRight,
			final Term weakIdx, final Term proofLeft, final Term proofRight,
			final Set<Term> neededEqualities) {
		final Theory theory = arrayLeft.getTheory();
		final Term selectLeft = theory.term(SMTLIBConstants.SELECT, arrayLeft, weakIdx);
		final Term selectRight = theory.term(SMTLIBConstants.SELECT, arrayRight, weakIdx);
		final LinkedHashSet<Term> transChain = new LinkedHashSet<>();
		transChain.add(selectLeft);
		transChain.add(value1);
		transChain.add(value2);
		transChain.add(selectRight);
		Term proof = null;
		if (transChain.size() > 2) {
			proof = mProofRules.trans(transChain.toArray(new Term[transChain.size()]));
		}
		if (selectLeft != value1) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, selectLeft, value1), proofLeft, proof);
		}
		if (value1 != value2) {
			neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, value1, value2));
		}
		if (selectRight != value2) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, value2, selectRight),
					mProofRules.symm(value2, selectRight), proof);
			proof = res(theory.term(SMTLIBConstants.EQUALS, selectRight, value2), proofRight, proof);
		}
		return proof;
	}

	/**
	 * Prove for a step in a weak array path that
	 * {@code (select arrayLeft weakIdx) = (select arrayRight weakIdx)}, for the
	 * case that there is an explicit select equality (or the edge-case where this
	 * explicit select equality would be trivial. A select equality is an equality
	 * of the form {@code (select arrayLeft idx1) = (select arrayRight idx2)}, where
	 * an equality between weakIdx and idx1 resp. idx2 is either trivial or in the
	 * equalities set. In case arrayLeft is the term {@pre (const v)} the left-hand
	 * side of the equality can be simply {@pre v}, similarly for arrayRight.
	 *
	 * @param arrayLeft        the left array of the step.
	 * @param arrayRight       the right array of the step.
	 * @param weakIdx          the weak path index.
	 * @param equalities       the equality literals from the clause.
	 * @param neededEqualities a set into which needed equalities are added.
	 * @return the proof for the equality between the two selects. The proof uses
	 *         the equality between the select index in the equality and weakIndex,
	 *         which it adds to neededEqualities. It returns null if this is not a
	 *         store step.
	 */
	private Term proveSelectPath(final Term arrayLeft, final Term arrayRight, final Term weakIdx,
			final Set<SymmetricPair<Term>> allEqualities, final Set<Term> neededEqualities) {
		for (final SymmetricPair<Term> candidateEquality : allEqualities) {
			// Check for each candidate equality if it explains a select edge for a
			// weakeq-ext lemma.
			// We check if termPair.first[weakIdx]] equals one side of the equality and
			// termPair.second[weakIdx]
			// equals the other side.
			final Term first = candidateEquality.getFirst();
			final Term second = candidateEquality.getSecond();
			Term eq1 = proveSelectConst(first, arrayLeft, weakIdx, allEqualities, neededEqualities);
			Term eq2 = proveSelectConst(second, arrayRight, weakIdx, allEqualities, neededEqualities);
			if (eq1 != null && eq2 != null) {
				return proveSelectPathTrans(arrayLeft, first, second, arrayRight, weakIdx, eq1, eq2,
						neededEqualities);
			}
			eq1 = proveSelectConst(second, arrayLeft, weakIdx, allEqualities, neededEqualities);
			eq2 = proveSelectConst(first, arrayRight, weakIdx, allEqualities, neededEqualities);
			if (eq1 != null && eq2 != null) {
				return proveSelectPathTrans(arrayLeft, second, first, arrayRight, weakIdx, eq1, eq2,
						neededEqualities);
			}
		}
		// No candidate equality was found but it could also be a select-const edge
		// where a[i] and v are
		// syntactically equal, in which case there is no equality.
		if (isApplication(SMTLIBConstants.CONST, arrayLeft)) {
			final Term value = ((ApplicationTerm) arrayLeft).getParameters()[0];
			final Term eq2 = proveSelectConst(value, arrayRight, weakIdx, allEqualities, neededEqualities);
			if (eq2 != null) {
				return proveSelectPathTrans(arrayLeft, value, value, arrayRight, weakIdx,
						mProofRules.constArray(value, weakIdx), eq2, neededEqualities);
			}
		}
		if (isApplication(SMTLIBConstants.CONST, arrayRight)) {
			final Term value = ((ApplicationTerm) arrayRight).getParameters()[0];
			final Term eq1 = proveSelectConst(value, arrayLeft, weakIdx, allEqualities, neededEqualities);
			if (eq1 != null) {
				return proveSelectPathTrans(arrayLeft, value, value, arrayRight, weakIdx, eq1,
						mProofRules.constArray(value, weakIdx), neededEqualities);
			}
		}
		return null;
	}

	/**
	 * Try to prove for a step in a weak array path that
	 * {@code (select arrayLeft weakIdx) = (select arrayRight weakIdx)}, for the
	 * case that the left array is a store of the right array and the disequality
	 * between the store index and weakIdx is given. This returns null if this is
	 * not the case.
	 *
	 * @param arrayLeft           the left array of the step.
	 * @param arrayRight          the right array of the step.
	 * @param weakIdx             the weak path index.
	 * @param disequalities       the index disequality literals from the clause.
	 * @param neededDisequalities a set into which needed disequalities are added.
	 * @return the proof for the equality between the two selects. The proof uses
	 *         the disequality between the store index and weakIndex, which it adds
	 *         to neededDisequalities. It returns null if this is not a store step.
	 */
	private Term proveStoreStep(final Term arrayLeft, final Term arrayRight, final Term weakIdx,
			final Set<SymmetricPair<Term>> disequalities, final Set<Term> neededDisequalities) {
		if (isApplication("store", arrayLeft)) {
			final Term[] storeArgs = ((ApplicationTerm) arrayLeft).getParameters();
			if (storeArgs[0] == arrayRight) {
				// this is a step from a to (store a storeIndex v). Check if storeIndex is okay.
				final Term storeIdx = ((ApplicationTerm) arrayLeft).getParameters()[1];
				if (disequalities.contains(new SymmetricPair<>(weakIdx, storeIdx))) {
					final Term storeVal = ((ApplicationTerm) arrayLeft).getParameters()[2];
					final Theory theory = arrayLeft.getTheory();
					neededDisequalities.add(theory.term(SMTLIBConstants.EQUALS, storeIdx, weakIdx));
					return mProofRules.selectStore2(arrayRight, storeIdx, storeVal, weakIdx);
				}
			}
		}
		return null;
	}

	/**
	 * Prove for a step in a weak array path that
	 * {@code (select arrayLeft weakIdx) = (select arrayRight weakIdx)}. In a valid
	 * lemma for each pair of consecutive terms, either there is a strong equality
	 * between the arrays, or it is a weak store step, or (for weakeq-ext) there
	 * exists a select equality at indices equal to the weak path index (or one of
	 * the arrays is constant and the equality goes to this constant value).
	 *
	 * @param arrayLeft           the left array of the step.
	 * @param arrayRight          the right array of the step.
	 * @param weakIdx             the weak path index.
	 * @param selectLeft          the term {@code (select arrayLeft weakIdx)}.
	 * @param selectRight         the term {@code (select arrayRight weakIdx)}.
	 * @param equalities          the equality literals from the clause.
	 * @param disequalities       the index disequality literals from the clause.
	 * @param neededEqualities    a set into which needed equalities are added.
	 * @param neededDisequalities a set into which needed disequalities are added.
	 * @return the proof for the equality between the two selects. The proof may use
	 *         some trivial (dis)equalities or some from (dis)equalities set, in
	 *         which case they are added to the needed(Dis)Equalities set.
	 */
	private Term proveSelectOverPathStep(final Term arrayLeft, final Term arrayRight, final Term weakIdx,
			final Term selectLeft, final Term selectRight,
			final Set<SymmetricPair<Term>> equalities, final Set<SymmetricPair<Term>> disequalities,
			final Set<Term> neededEqualities, final Set<Term> neededDisequalities) {
		final Theory theory = arrayLeft.getTheory();
		/* check for strong path first */
		if (equalities.contains(new SymmetricPair<>(arrayLeft, arrayRight))) {
			neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, arrayLeft, arrayRight));
			neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, weakIdx, weakIdx));
			return mProofRules.cong(selectLeft, selectRight);
		}
		/* check for weak store step */
		Term proof = proveStoreStep(arrayLeft, arrayRight, weakIdx, disequalities, neededDisequalities);
		if (proof != null) {
			return proof;
		}
		proof = proveStoreStep(arrayRight, arrayLeft, weakIdx, disequalities, neededDisequalities);
		if (proof != null) {
			return res(theory.term(SMTLIBConstants.EQUALS, selectRight, selectLeft),
					proof, mProofRules.symm(selectLeft, selectRight));
		}
		/*
		 * check for select path with select indices equal to weakIdx, both trivially
		 * equal and proven equal by a strong path
		 */
		return proveSelectPath(arrayLeft, arrayRight, weakIdx, equalities, neededEqualities);
	}

	/**
	 * Prove for a weak array path that
	 * {@code (select path[0] weakIdx) = (select path[last] weakIdx)}. In a valid
	 * lemma for each pair of consecutive terms, either there is a strong equality
	 * between the arrays, or it is a weak store step, or (for weakeq-ext) there
	 * exists a select equality at indices equal to the weak path index (or one of
	 * the arrays is constant and the equality goes to this constant value).
	 *
	 * @param weakIdx             the weak path index.
	 * @param path                the path to prove.
	 * @param equalities          the equality literals from the clause.
	 * @param disequalities       the index disequality literals from the clause.
	 * @param neededEqualities    a set into which needed equalities are added.
	 * @param neededDisequalities a set into which needed disequalities are added.
	 * @return the proof for the equality between the selects. The proof may use
	 *         some trivial (dis)equalities or some from (dis)equalities set, in
	 *         which case they are added to the needed(Dis)Equalities set.
	 */
	private Term proveSelectOverPath(final Term weakIdx, final Term[] path,
			final Set<SymmetricPair<Term>> equalities, final Set<SymmetricPair<Term>> disequalities,
			final Set<Term> neededEqualities, final Set<Term> neededDisequalities) {
		// note that a read-const-weakeq path can have length 1
		assert path.length >= 1;
		final Theory theory = path[0].getTheory();
		final Term[] selectChain = new Term[path.length];
		for (int i = 0; i < path.length; i++) {
			selectChain[i] = theory.term(SMTLIBConstants.SELECT, path[i], weakIdx);
		}
		if (selectChain.length == 1) {
			return mProofRules.refl(selectChain[0]);
		}
		Term proof = selectChain.length > 2 ? mProofRules.trans(selectChain) : null;
		for (int i = 0; i < path.length - 1; i++) {
			final Term subproof = proveSelectOverPathStep(path[i], path[i + 1], weakIdx, selectChain[i],
					selectChain[i + 1], equalities, disequalities, neededEqualities, neededDisequalities);
			proof = res(theory.term(SMTLIBConstants.EQUALS, selectChain[i], selectChain[i + 1]), subproof, proof);
		}
		return proof;
	}

	/**
	 * Convert an array lemma of type :read-const-weakeq to a simplified proof.
	 *
	 * @param type
	 *            the lemma type
	 * @param clause
	 *            the clause to check
	 * @param ccAnnotation
	 *            the argument of the lemma annotation.
	 */
	private Term convertArraySelectConstWeakEqLemma(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length >= 3;
		final Theory theory = clause[0].getAtom().getTheory();
		/*
		 * weakPaths maps from a symmetric pair to the set of weak indices such that a weak path was proven for this
		 * pair. strongPaths contains the sets of all proven strong paths.
		 */
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		/* indexDiseqs contains all index equalities in the clause */
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		final Term goalEquality = (Term) ccAnnotation[0];
		assert isApplication("=", goalEquality);
		final Term[] goalTerms = ((ApplicationTerm) goalEquality).getParameters();
		assert goalTerms.length == 2;

		/*
		 * Check the paths in reverse order. Collect proven paths in a hash set, so that they can be used later.
		 */
		assert ccAnnotation.length == 3;
		assert ccAnnotation[1] == ":weakpath";
		final Object[] weakItems = (Object[]) ccAnnotation[2];
		assert weakItems.length == 2;
		final Term mainIdx = (Term) weakItems[0];
		final Term[] mainPath = (Term[]) weakItems[1];

		Term proof = proveSelectOverPath(mainIdx, mainPath, allEqualities.keySet(), allDisequalities.keySet(),
				neededEqualities, neededDisequalities);
		final Term firstTerm = theory.term("select", mainPath[0], mainIdx);
		final Term lastTerm = theory.term("select", mainPath[mainPath.length - 1], mainIdx);
		assert isApplication("const", mainPath[mainPath.length - 1]);
		final Term constParam = ((ApplicationTerm) mainPath[mainPath.length - 1]).getParameters()[0];
		final int goalOrder = goalTerms[1] == constParam ? 0 : 1;
		assert goalTerms[goalOrder] == mSkript.term("select", mainPath[0], mainIdx);
		assert goalTerms[1 - goalOrder] == constParam;
		proof = res(theory.term("=", firstTerm, lastTerm), proof, mProofRules.trans(firstTerm, lastTerm, constParam));
		proof = res(theory.term("=", lastTerm, constParam), mProofRules.constArray(constParam, mainIdx), proof);
		neededDisequalities.add(theory.term("=", firstTerm, constParam));
		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert an array lemma of type :read-over-weakeq to a simplified proof.
	 *
	 * @param type
	 *            the lemma type
	 * @param clause
	 *            the clause to check
	 * @param ccAnnotation
	 *            the argument of the lemma annotation.
	 */
	private Term convertArraySelectWeakEqLemma(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length >= 3;
		final Theory theory = clause[0].getAtom().getTheory();
		/*
		 * weakPaths maps from a symmetric pair to the set of weak indices such that a weak path was proven for this
		 * pair. strongPaths contains the sets of all proven strong paths.
		 */
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		/* indexDiseqs contains all index equalities in the clause */
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		final Term goalEquality = (Term) ccAnnotation[0];
		assert isApplication("=", goalEquality);
		final Term[] goalTerms = ((ApplicationTerm) goalEquality).getParameters();
		assert goalTerms.length == 2;

		/*
		 * Check the paths in reverse order. Collect proven paths in a hash set, so that they can be used later.
		 */
		assert ccAnnotation.length == 3;
		assert ccAnnotation[1] == ":weakpath";
		final Object[] weakItems = (Object[]) ccAnnotation[2];
		assert weakItems.length == 2;
		final Term mainIdx = (Term) weakItems[0];
		final Term[] mainPath = (Term[]) weakItems[1];

		Term proof = proveSelectOverPath(mainIdx, mainPath, allEqualities.keySet(), allDisequalities.keySet(),
				neededEqualities, neededDisequalities);
		assert isApplication("select", goalTerms[0]) && isApplication("select", goalTerms[1]);
		final int goalOrder = ((ApplicationTerm) goalTerms[0]).getParameters()[0] == mainPath[0] ? 0 : 1;
		final Term goal1 = goalTerms[goalOrder];
		final Term goal2 = goalTerms[1 - goalOrder];
		final Term firstTerm = theory.term("select", mainPath[0], mainIdx);
		final Term lastTerm = theory.term("select", mainPath[mainPath.length - 1], mainIdx);
		if (goal1 != firstTerm) {
			assert mainPath[0] == ((ApplicationTerm) goal1).getParameters()[0];
			final Term goalIdx = ((ApplicationTerm) goal1).getParameters()[1];
			proof = res(theory.term("=", firstTerm, lastTerm), proof, mProofRules.trans(goal1, firstTerm, lastTerm));
			proof = res(theory.term("=", goal1, firstTerm), mProofRules.cong(goal1, firstTerm), proof);
			neededEqualities.add(theory.term("=", goalIdx, mainIdx));
			neededEqualities.add(theory.term("=", mainPath[0], mainPath[0]));
		}
		if (goal2 != lastTerm) {
			assert mainPath[mainPath.length - 1] == ((ApplicationTerm) goal2).getParameters()[0];
			final Term goalIdx = ((ApplicationTerm) goal2).getParameters()[1];
			proof = res(theory.term("=", goal1, lastTerm), proof, mProofRules.trans(goal1, lastTerm, goal2));
			proof = res(theory.term("=", lastTerm, goal2), mProofRules.cong(lastTerm, goal2), proof);
			neededEqualities.add(theory.term("=", mainIdx, goalIdx));
			neededEqualities.add(theory.term("=", mainPath[mainPath.length - 1], mainPath[mainPath.length - 1]));
		}
		neededDisequalities.add(theory.term("=", goal1, goal2));
		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert an array lemma of type :weakeq-ext to a simplified proof.
	 *
	 * @param type         the lemma type
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the lemma annotation.
	 */
	private Term convertArrayWeakEqExtLemma(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length >= 3;
		final Theory theory = clause[0].getAtom().getTheory();
		/*
		 * weakPaths maps from a symmetric pair to the set of weak indices such that a weak path was proven for this
		 * pair. strongPaths contains the sets of all proven strong paths.
		 */
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		/* indexDiseqs contains all index equalities in the clause */
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		final Term goalEquality = (Term) ccAnnotation[0];
		assert isApplication("=", goalEquality);
		final Term[] goalTerms = ((ApplicationTerm) goalEquality).getParameters();
		assert goalTerms.length == 2;

		/*
		 * Check the paths in reverse order. Collect proven paths in a hash set, so that they can be used later.
		 */
		assert ccAnnotation.length % 2 == 1;
		assert ccAnnotation[1] == ":subpath";
		final Term[] mainPath = (Term[]) ccAnnotation[2];

		final Term arrayLeft = mainPath[0];
		final Term arrayRight = mainPath[mainPath.length - 1];
		final Term diffTerm = theory.term(SMTInterpolConstants.DIFF, arrayLeft, arrayRight);
		final Term[] mainSelectChain = new Term[mainPath.length];
		for (int i = 0; i < mainPath.length; i++) {
			mainSelectChain[i] = theory.term(SMTLIBConstants.SELECT, mainPath[i], diffTerm);
		}
		final Term selectLeftDiff =  mainSelectChain[0];
		final Term selectRightDiff =  mainSelectChain[mainPath.length - 1];

		final HashSet<SymmetricPair<Term>> weakDisequalities = new HashSet<>();
		final HashSet<Term> neededWeakDisequalities = new HashSet<>();
		/* Collect weak paths */
		for (int i = 3; i < ccAnnotation.length; i += 2) {
			assert ccAnnotation[i] == ":weakpath";
			final Object[] weakItems = (Object[]) ccAnnotation[i + 1];
			final Term idx = (Term) weakItems[0];
			weakDisequalities.add(new SymmetricPair<>(idx, diffTerm));
		}

		/*
		 * Now prove the main select chain.
		 */
		Term mainChainProof = mainPath.length > 2 ? mProofRules.trans(mainSelectChain) : null;
		for (int i = 0; i < mainPath.length - 1; i++) {
			Term proofSelectEq;
			final SymmetricPair<Term> pair = new SymmetricPair<>(mainPath[i], mainPath[i + 1]);
			/* check for strong path first */
			if (allEqualities.containsKey(pair)) {
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, mainPath[i], mainPath[i + 1]));
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, diffTerm, diffTerm));
				proofSelectEq = mProofRules.cong(mainSelectChain[i], mainSelectChain[i + 1]);
			} else {
				proofSelectEq = proveStoreStep(mainPath[i], mainPath[i + 1], diffTerm, weakDisequalities,
						neededWeakDisequalities);
				if (proofSelectEq == null) {
					proofSelectEq = proveStoreStep(mainPath[i + 1], mainPath[i], diffTerm, weakDisequalities,
							neededWeakDisequalities);
					proofSelectEq = res(theory.term(SMTLIBConstants.EQUALS, mainSelectChain[i + 1], mainSelectChain[i]),
							proofSelectEq, mProofRules.symm(mainSelectChain[i], mainSelectChain[i + 1]));
				}
			}
			mainChainProof = res(theory.term(SMTLIBConstants.EQUALS, mainSelectChain[i], mainSelectChain[i + 1]),
					proofSelectEq, mainChainProof);
		}

		/* Now combine with the weak paths */
		for (int i = 3; i < ccAnnotation.length; i += 2) {
			assert ccAnnotation[i] == ":weakpath";
			final Object[] weakItems = (Object[]) ccAnnotation[i + 1];
			final Term idx = (Term) weakItems[0];
			final Term[] weakPath = (Term[]) weakItems[1];

			/* check end points */
			assert arrayLeft == weakPath[0] && arrayRight == weakPath[weakPath.length - 1];
			final Term indexDiseq = theory.term(SMTLIBConstants.EQUALS, idx, diffTerm);
			final boolean changed = neededWeakDisequalities.remove(indexDiseq);
			assert changed;

			final Term selectLeftIdx = theory.term(SMTLIBConstants.SELECT, arrayLeft, idx);
			final Term selectRightIdx = theory.term(SMTLIBConstants.SELECT, arrayRight, idx);
			Term subproof = proveSelectOverPath(idx, weakPath,
					allEqualities.keySet(), allDisequalities.keySet(), neededEqualities, neededDisequalities);
			subproof = res(theory.term(SMTLIBConstants.EQUALS, selectLeftIdx, selectRightIdx),
					subproof, mProofRules.trans(selectLeftDiff, selectLeftIdx, selectRightIdx, selectRightDiff));
			subproof = res(theory.term(SMTLIBConstants.EQUALS, selectLeftDiff, selectLeftIdx),
					mProofRules.cong(selectLeftDiff, selectLeftIdx), subproof);
			subproof = res(theory.term(SMTLIBConstants.EQUALS, selectRightIdx, selectRightDiff),
					mProofRules.cong(selectRightIdx, selectRightDiff), subproof);
			neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, arrayLeft, arrayLeft));
			neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, arrayRight, arrayRight));
			subproof = res(theory.term(SMTLIBConstants.EQUALS, diffTerm, idx), mProofRules.symm(diffTerm, idx),
					subproof);
			mainChainProof = res(indexDiseq, mainChainProof, subproof);
		}
		assert neededWeakDisequalities.isEmpty();

		/* Build the main proof:
		 * use extensionality and equality on select is proved by transitivity over the main path.
		 */
		Term proof = mProofRules.extDiff(arrayLeft, arrayRight);
		proof = res(theory.term("=", selectLeftDiff, selectRightDiff), mainChainProof, proof);
		neededDisequalities.add(theory.term("=", arrayLeft, arrayRight));
		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert a data type project lemma to a minimal proof. This lemma has the form
	 * {@code w != cons(v1,...,vn), seli(w) = vi}. The inequality is missing if it
	 * is implied by reflexivity. The equality is missing if it is a trivial
	 * disequality.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :dt-project annotation. It has the
	 *                     form {@code (= seli(w) vi) :cons cons(v1,...,vn)}.
	 */
	private Term convertDTProject(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length == 3;
		final Theory theory = clause[0].getAtom().getTheory();

		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		final ApplicationTerm goalEquality = (ApplicationTerm) ccAnnotation[0];
		assert isApplication("=", goalEquality);
		assert ccAnnotation[1].equals(":cons");
		final ApplicationTerm consTerm = (ApplicationTerm) ccAnnotation[2];
		final FunctionSymbol consFunc = consTerm.getFunction();
		assert consFunc.isConstructor();
		final Term[] goalTerms = goalEquality.getParameters();
		assert goalTerms.length == 2;

		assert goalTerms[0] instanceof ApplicationTerm;
		final ApplicationTerm selectTerm = (ApplicationTerm) goalTerms[0];
		final FunctionSymbol selector = selectTerm.getFunction();
		assert selector.isSelector();
		final Term selectArg = selectTerm.getParameters()[0];
		final Term selectConsTerm = theory.term(selector, consTerm);
		final Constructor cons = ((DataType) consTerm.getSort().getSortSymbol()).getConstructor(consFunc.getName());
		final int selectPos = cons.getSelectorIndex(selector.getName());
		final Term consArg = consTerm.getParameters()[selectPos];

		Term proof = mProofRules.dtProject(selectConsTerm);
		neededDisequalities.add(theory.term("=", selectTerm, consArg));

		if (selectTerm != selectConsTerm) {
			neededEqualities.add(theory.term("=", selectArg, consTerm));
			proof = res(theory.term("=", selectConsTerm, consArg), proof,
					mProofRules.trans(selectTerm, selectConsTerm, consArg));
			proof = res(theory.term("=", selectTerm, selectConsTerm),
					mProofRules.cong(selectTerm, selectConsTerm), proof);
		}

		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert a data type tester lemma to a minimal proof. This lemma has the form
	 * {@code w != cons(v1,...,vn), is_cons(w) = true} or
	 * {@code w != cons(v1,...,vn), is_cons'(w) = false}. The inequality is missing
	 * if it is implied by reflexivity. The equality is missing if it is a trivial
	 * disequality.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :dt-tester annotation. It has the
	 *                     form
	 *                     {@code (= is_cons(w) true/false) :cons cons(v1,...,vn)}.
	 */
	private Term convertDTTester(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length == 3;
		final Theory theory = clause[0].getAtom().getTheory();
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		final Term goalEquality = (Term) ccAnnotation[0];
		assert isApplication("=", goalEquality);
		assert ccAnnotation[1].equals(":cons");
		final ApplicationTerm consTerm = (ApplicationTerm) ccAnnotation[2];
		final FunctionSymbol consFunc = consTerm.getFunction();
		assert consFunc.isConstructor();
		final Term[] goalTerms = ((ApplicationTerm) goalEquality).getParameters();
		assert goalTerms.length == 2;

		assert goalTerms[0] instanceof ApplicationTerm;
		final ApplicationTerm testerTerm = (ApplicationTerm) goalTerms[0];
		final FunctionSymbol tester = testerTerm.getFunction();
		assert tester.getName().equals(SMTLIBConstants.IS);
		final Term testerArg = testerTerm.getParameters()[0];
		final Term testConsTerm = theory.term(tester, consTerm);
		final Term trueFalseTerm = goalTerms[1];
		final String otherCons = tester.getIndices()[0];
		final boolean isSameCons = consFunc.getName().equals(otherCons);
		assert trueFalseTerm == (isSameCons ? theory.mTrue : theory.mFalse);
		final Term testConsEquality = theory.term(SMTLIBConstants.EQUALS, testConsTerm, trueFalseTerm);

		Term proof;
		if (isSameCons) {
			proof = mProofRules.dtTestI(consTerm);
			proof = res(testConsTerm, proof,
					res(trueFalseTerm, mProofRules.trueIntro(), mProofRules.iffIntro2(testConsEquality)));
		} else {
			proof = mProofRules.dtTestE(otherCons, consTerm);
			proof = res(testConsTerm,
					res(trueFalseTerm, mProofRules.iffIntro1(testConsEquality), mProofRules.falseElim()), proof);
		}
		neededDisequalities.add(theory.term("=", testerTerm, trueFalseTerm));

		if (testerTerm != testConsTerm) {
			neededEqualities.add(theory.term("=", testerArg, consTerm));
			proof = res(theory.term("=", testConsTerm, trueFalseTerm), proof,
					mProofRules.trans(testerTerm, testConsTerm, trueFalseTerm));
			proof = res(theory.term("=", testerTerm, testConsTerm), mProofRules.cong(testerTerm, testConsTerm),
					proof);
		}

		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert a data type constructor lemma to a minimal proof. This lemma has the
	 * form {@code is_cons(w) != true, w = cons(sel1(w),...,seln(w))}.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :dt-tester annotation. It has the
	 *                     form {@code (= w (cons (sel1 w) ... (seln w)))}.
	 */
	private Term convertDTConstructor(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length == 1;
		final Theory theory = clause[0].getAtom().getTheory();

		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		final ApplicationTerm goalEquality = (ApplicationTerm) ccAnnotation[0];
		assert isApplication("=", goalEquality);
		final Term[] goalTerms = goalEquality.getParameters();
		assert goalTerms.length == 2;

		final ApplicationTerm consTerm = (ApplicationTerm) goalTerms[1];
		final Term dataTerm = goalTerms[0];
		final DataType dataType = (DataType) dataTerm.getSort().getSortSymbol();
		final Constructor cons = dataType.getConstructor(consTerm.getFunction().getName());

		final Term testerTerm = theory.term(SMTLIBConstants.IS, new String[] { cons.getName() }, null, dataTerm);
		final Term testerTrueTerm = theory.term(SMTLIBConstants.EQUALS, testerTerm, theory.mTrue);

		neededEqualities.add(testerTrueTerm);
		neededDisequalities.add(theory.term(SMTLIBConstants.EQUALS, consTerm, dataTerm));
		final Term proof = res(testerTerm,
				res(theory.mTrue, mProofRules.trueIntro(), mProofRules.iffElim1(testerTrueTerm)),
				mProofRules.dtCons(testerTerm));

		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert a data type cases lemma to a minimal proof. This lemma has the form
	 * {@code ((_ is cons1) u1) != false, ... ((_ is consn) un) != false, u1 != u2,  ... u1 != un}.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :dt-tester annotation. It is a list
	 *                     of the tester terms {@code ((_ is consi) ui)}.
	 */
	private Term convertDTCases(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		final Theory theory = clause[0].getAtom().getTheory();
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		assert ccAnnotation.length > 0;
		final ApplicationTerm firstTester = (ApplicationTerm) ccAnnotation[0];
		assert isApplication(SMTLIBConstants.IS, firstTester);
		final Term firstData = firstTester.getParameters()[0];


		Term proof = mProofRules.dtExhaust(firstData);
		for (int i = 0; i < ccAnnotation.length; i++) {
			final Term tester = (Term) ccAnnotation[i];
			assert isApplication(SMTLIBConstants.IS, tester);
			final FunctionSymbol testerFunc = ((ApplicationTerm) tester).getFunction();
			final Term arg = ((ApplicationTerm) ccAnnotation[i]).getParameters()[0];
			final Term testerEq = theory.term(SMTLIBConstants.EQUALS, tester, theory.mFalse);
			Term subproof = res(theory.mFalse, mProofRules.iffElim2(testerEq), mProofRules.falseElim());
			neededEqualities.add(testerEq);
			final Term testerFirst = theory.term(testerFunc, firstData);
			if (tester != testerFirst) {
				final Term dataEq = theory.term(SMTLIBConstants.EQUALS, firstData, arg);
				final Term testerFirstEq = theory.term(SMTLIBConstants.EQUALS, testerFirst, tester);
				neededEqualities.add(dataEq);
				subproof = res(testerFirstEq, mProofRules.cong(testerFirst, tester),
						res(tester, mProofRules.iffElim2(testerFirstEq), subproof));
			}
			proof = res(testerFirst, proof, subproof);
		}

		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert a data type cases lemma to a minimal proof. This lemma has the form
	 * {@code ((_ is cons1) u1) != true, ((_ is cons2) u2) != true, u1 != u2}.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :dt-tester annotation. It is a list
	 *                     of the two tester terms {@code ((_ is consi) ui)}.
	 */
	private Term convertDTUnique(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		final Theory theory = clause[0].getAtom().getTheory();
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		assert ccAnnotation.length == 2;
		final ApplicationTerm firstTester = (ApplicationTerm) ccAnnotation[0];
		assert isApplication(SMTLIBConstants.IS, firstTester);
		final Term firstData = firstTester.getParameters()[0];
		final ApplicationTerm secondTester = (ApplicationTerm) ccAnnotation[1];
		assert isApplication(SMTLIBConstants.IS, secondTester);
		final Term secondData = secondTester.getParameters()[0];
		assert firstData.getSort() == secondData.getSort();
		final DataType dataType = (DataType) firstData.getSort().getSortSymbol();
		final Constructor firstCons = dataType.getConstructor(firstTester.getFunction().getIndices()[0]);
		final String[] selectors = firstCons.getSelectors();
		final Term[] selectTerms = new Term[selectors.length];
		for (int i = 0; i < selectors.length; i++) {
			selectTerms[i] = theory.term(selectors[i], firstData);
		}
		final Term consTerm = theory.term(firstCons.getName(), null,
				(firstCons.needsReturnOverload() ? firstData.getSort() : null), selectTerms);
		final Term consEq = theory.term(SMTLIBConstants.EQUALS, consTerm, firstData);
		final Term testConsTerm = theory.term(secondTester.getFunction(), consTerm);
		Term proof = res(consEq, mProofRules.dtCons(firstTester), mProofRules.trans(consTerm, firstData, secondData));
		neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, firstData, secondData));
		proof = res(theory.term(SMTLIBConstants.EQUALS, consTerm, secondData), proof,
				mProofRules.cong(testConsTerm, secondTester));
		final Term secondConsTestEq = theory.term(SMTLIBConstants.EQUALS, testConsTerm, secondTester);
		proof = res(secondConsTestEq, proof, mProofRules.iffElim1(secondConsTestEq));
		proof = res(testConsTerm, proof, mProofRules.dtTestE(secondTester.getFunction().getIndices()[0], consTerm));

		final Term firstTesterEq = theory.term(SMTLIBConstants.EQUALS, firstTester, theory.mTrue);
		neededEqualities.add(firstTesterEq);
		proof = res(firstTester, mProofRules.iffElim1(firstTesterEq), proof);
		final Term secondTesterEq = theory.term(SMTLIBConstants.EQUALS, secondTester, theory.mTrue);
		neededEqualities.add(secondTesterEq);
		proof = res(secondTester, mProofRules.iffElim1(secondTesterEq), proof);
		proof = res(theory.mTrue, mProofRules.trueIntro(), proof);

		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert a data type dt-injective lemma to a minimal proof. This lemma has the
	 * form {@code (cons a1 ... an) != (cons b1 ... bn), ai == bi}
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :dt-injective annotation. It has the
	 *                     form
	 *                     {@code ((= ai bi) :cons (cons a1 ... an) (cons b1 ... bn))}.
	 */
	private Term convertDTInjective(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		final Theory theory = clause[0].getAtom().getTheory();
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		assert ccAnnotation.length == 4;
		final ApplicationTerm goalEquality = (ApplicationTerm) ccAnnotation[0];
		assert ccAnnotation[1].equals(":cons");
		final ApplicationTerm consTerm1 = (ApplicationTerm) ccAnnotation[2];
		final ApplicationTerm consTerm2 = (ApplicationTerm) ccAnnotation[3];
		assert consTerm1.getFunction() == consTerm2.getFunction();
		assert consTerm1.getFunction().isConstructor();
		final Term[] consArgs1 = consTerm1.getParameters();
		final Term[] consArgs2 = consTerm2.getParameters();
		final Term mainEq1 = goalEquality.getParameters()[0];
		final Term mainEq2 = goalEquality.getParameters()[1];

		// find the position of the arguments in the constructor for the terms in the
		// main equality.
		int pos;
		for (pos = 0;; pos++) {
			if (consArgs1[pos] == mainEq1 && consArgs2[pos] == mainEq2) {
				break;
			}
		}

		// the proof basically shows
		// mainEquality[0] = (selpos cons1) = (selpos cons2) = mainEquality[1]
		final DataType dataType = (DataType) consTerm1.getSort().getSortSymbol();
		final Constructor cons = dataType.findConstructor(consTerm1.getFunction().getName());
		final String selector = cons.getSelectors()[pos];
		final Term sel1 = theory.term(selector, consTerm1);
		final Term sel2 = theory.term(selector, consTerm2);
		Term proof = mProofRules.trans(mainEq1, sel1, sel2, mainEq2);
		neededDisequalities.add(goalEquality);
		proof = res(theory.term(SMTLIBConstants.EQUALS, mainEq1, sel1),
				res(theory.term(SMTLIBConstants.EQUALS, sel1, mainEq1), mProofRules.dtProject(sel1),
						mProofRules.symm(mainEq1, sel1)),
				proof);
		proof = res(theory.term(SMTLIBConstants.EQUALS, sel2, mainEq2), mProofRules.dtProject(sel2), proof);
		proof = res(theory.term(SMTLIBConstants.EQUALS, sel1, sel2), mProofRules.cong(sel1, sel2), proof);
		neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, consTerm1, consTerm2));

		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert a data type dt-injective lemma to a minimal proof. This lemma has the
	 * form {@code (cons a1 ... an) != (cons' b1 ... bn')}, where cons and cons' are
	 * different constructors.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :dt-disjoint annotation. It has the
	 *                     form {@code :cons (cons a1 ... an) (cons' b1 ... bn'))}.
	 */
	private Term convertDTDisjoint(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		final Theory theory = clause[0].getAtom().getTheory();
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		assert ccAnnotation.length == 3;
		assert ccAnnotation[0].equals(":cons");
		final ApplicationTerm consTerm1 = (ApplicationTerm) ccAnnotation[1];
		final ApplicationTerm consTerm2 = (ApplicationTerm) ccAnnotation[2];
		assert consTerm1.getFunction() != consTerm2.getFunction();
		assert consTerm1.getFunction().isConstructor();
		assert consTerm2.getFunction().isConstructor();

		// the proof basically shows a contradiction via:
		// (iscons1 cons1) = (iscons1 cons2)
		final Term isCons11 =
				theory.term(SMTLIBConstants.IS, new String[] { consTerm1.getFunction().getName() }, null, consTerm1);
		final Term isCons12 =
				theory.term(SMTLIBConstants.IS, new String[] { consTerm1.getFunction().getName() }, null, consTerm2);
		final Term isConsEq = theory.term(SMTLIBConstants.EQUALS, isCons11, isCons12);
		Term proof = mProofRules.cong(isCons11, isCons12);
		neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, consTerm1, consTerm2));
		proof = res(isConsEq, proof, mProofRules.iffElim2(isConsEq));
		proof = res(isCons11, mProofRules.dtTestI(consTerm1), proof);
		proof = res(isCons12, proof, mProofRules.dtTestE(consTerm1.getFunction().getName(), consTerm2));

		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	private int checkAndFindConsArg(final Term consTerm, final Term argTerm) {
		if (!(consTerm instanceof ApplicationTerm)) {
			return -1;
		}
		final ApplicationTerm appTerm = (ApplicationTerm) consTerm;
		if (!appTerm.getFunction().isConstructor()) {
			return -1;
		}
		final Term[] consArgs = appTerm.getParameters();
		for (int i = 0; i < consArgs.length; i++) {
			if (consArgs[i] == argTerm) {
				return i;
			}
		}
		return -1;
	}

	/**
	 * Convert a data type dt-cycle lemma to a minimal proof. The lemma is annotated
	 * with a cycle {@code a1,b1,a2,b2,..,an} that shows that {@code a1} is equal to
	 * a constructor call on itself. The lemma must contain {@code ai=bi} negated
	 * and {@code a(i+1)} is a child of {@code bi} in the sense that either
	 * {@code bi} is a term {@code cons(..,a(i+1),...)}, or that {@code a(i+1)} is a
	 * term {@code sel(bi)} and for the corresponding constructor
	 * {@code is_cons(bi) = true} occurs negated in the lemma.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :dt-cycle annotation. It has the form
	 *                     {@code :cycle a1 b1 a2 b2 ... an} where a1 == an.
	 */
	private Term convertDTCycle(final ProofLiteral[] clause, final Object[] ccAnnotation) {
		final Theory theory = clause[0].getAtom().getTheory();
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		assert ccAnnotation.length == 2;
		assert ccAnnotation[0].equals(":cycle");
		final Term[] cycle = (Term[]) ccAnnotation[1];
		assert cycle.length >= 3;
		assert cycle.length % 2 == 1;
		assert cycle[0] == cycle[cycle.length - 1];

		// Build the running cons term backwards over the cycle.
		// Also build the proof that the running cons term is equal to the corresponding
		// term in the cycle.

		Term runningTerm = cycle[0];
		Term proof = mProofRules.refl(runningTerm);
		final int[] argSequence = new int[(cycle.length - 1) / 2];
		for (int i = cycle.length - 3; i >= 0; i -= 2) {
			final Term selectTerm = cycle[i+2];
			final Term consTerm = cycle[i+1];
			int pos = checkAndFindConsArg(consTerm, selectTerm);
			if (pos >= 0) {
				if (runningTerm == selectTerm) {
					runningTerm = consTerm;
					proof = mProofRules.refl(runningTerm);
				} else {
					final Term[] consArgs = ((ApplicationTerm) consTerm).getParameters().clone();
					consArgs[pos] = runningTerm;
					for (int argnr = 0; argnr < consArgs.length; argnr++) {
						if (argnr != pos) {
							neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, consArgs[argnr], consArgs[argnr]));
						}
					}
					final Term newRunningTerm = theory.term(((ApplicationTerm) consTerm).getFunction(), consArgs);
					proof = res(theory.term(SMTLIBConstants.EQUALS, runningTerm, selectTerm), proof,
							mProofRules.cong(newRunningTerm, consTerm));
					runningTerm = newRunningTerm;
				}
				argSequence[i / 2] = pos;
			} else {
				final ApplicationTerm appTerm = (ApplicationTerm) selectTerm;
				assert appTerm.getFunction().isSelector();
				assert consTerm == appTerm.getParameters()[0];
				final DataType dataType = (DataType) consTerm.getSort().getSortSymbol();
				final Constructor[] constrs = dataType.getConstructors();
				findSelector: {
					for (final Constructor c : constrs) {
						final String[] selectors = c.getSelectors();
						for (pos = 0; pos < selectors.length; pos++) {
							if (selectors[pos].equals(appTerm.getFunction().getName())) {
								final Term[] consArgs = new Term[selectors.length];
								final Term[] runningArgs = new Term[selectors.length];
								for (int argnr = 0; argnr < consArgs.length; argnr++) {
									consArgs[argnr] = theory.term(selectors[argnr], consTerm);
									if (argnr != pos) {
										runningArgs[argnr] = consArgs[argnr];
										neededEqualities.add(
												theory.term(SMTLIBConstants.EQUALS, consArgs[argnr], consArgs[argnr]));
									} else {
										runningArgs[argnr] = runningTerm;
									}
								}
								final Term newConsTerm = theory.term(c.getName(), null,
										(c.needsReturnOverload() ? consTerm.getSort() : null), consArgs);
								final Term newRunningTerm = theory.term(c.getName(), null,
										(c.needsReturnOverload() ? consTerm.getSort() : null), runningArgs);
								final Term isConsTerm = theory.term(SMTLIBConstants.IS, new String[] { c.getName() },
										null, consTerm);
								proof = res(theory.term(SMTLIBConstants.EQUALS, runningTerm, selectTerm), proof,
										mProofRules.cong(newRunningTerm, newConsTerm));
								proof = res(theory.term(SMTLIBConstants.EQUALS, newRunningTerm, newConsTerm), proof,
										mProofRules.trans(newRunningTerm, newConsTerm, consTerm));
								final Term isConsEq = theory.term(SMTLIBConstants.EQUALS, isConsTerm, theory.mTrue);
								proof = res(theory.term(SMTLIBConstants.EQUALS, newConsTerm, consTerm),
										mProofRules.dtCons(isConsTerm), proof);
								proof = res(isConsTerm,
										res(theory.mTrue, mProofRules.trueIntro(), mProofRules.iffElim1(isConsEq)),
										proof);
								neededEqualities.add(isConsEq);
								runningTerm = newRunningTerm;
								argSequence[i / 2] = pos;
								break findSelector;
							}
						}
					}
					// selector not found in datatype
					throw new AssertionError();
				}
			}
			final Term eqterm = cycle[i];
			if (eqterm != consTerm) {
				proof = res(theory.term(SMTLIBConstants.EQUALS, runningTerm, consTerm), proof,
						mProofRules.trans(runningTerm, consTerm, eqterm));
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, consTerm, eqterm));
			}
		}

		// Now runningTerm = cons(...cycle[0]...) and proof shows runningTerm =
		// cycle[0].

		proof = res(theory.term(SMTLIBConstants.EQUALS, runningTerm, cycle[0]), proof,
				mProofRules.dtAcyclic(runningTerm, argSequence));
		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert an instantiation lemma to a minimal proof.
	 *
	 * @param clause         the clause to convert
	 * @param instAnnotation the argument of the :inst annotation.
	 */
	private void convertInstLemma(final ProofLiteral[] clause, final Object[] quantAnnotation) {
		// the first literal in the lemma is a negated universally quantified literal.
		assert !clause[0].getPolarity();
		final Term firstAtom = clause[0].getAtom();
		assert firstAtom instanceof QuantifiedFormula
				&& ((QuantifiedFormula) firstAtom).getQuantifier() == QuantifiedFormula.FORALL;

		// Check that the annotation of the lemma is well-formed.
		assert quantAnnotation.length == 5
				&& quantAnnotation[0] == ":subs" && (quantAnnotation[2] == ":conflict"
						|| quantAnnotation[2] == ":e-matching" || quantAnnotation[2] == ":enumeration")
				&& quantAnnotation[3] == ":subproof";
		final Term[] subst = (Term[]) quantAnnotation[1];
		final AnnotatedTerm annotSubproof = (AnnotatedTerm) getConverted();
		final Term provedEq = provedTerm(annotSubproof);
		final Term subproof = stripAnnotation(annotSubproof);
		assert isApplication("=", provedEq);
		final Term[] provedEqSides = ((ApplicationTerm) provedEq).getParameters();

		final QuantifiedFormula forall = (QuantifiedFormula) firstAtom;
		final AnnotatedTerm substitute = substituteInQuantInst(subst, forall);
		assert provedTerm(substitute) == provedEqSides[0];
		Term proof = stripAnnotation(substitute);
		proof = mProofRules.resolutionRule(provedEqSides[0], proof, mProofRules.iffElim2(provedEq));
		proof = mProofRules.resolutionRule(provedEq, subproof, proof);
		Term[] result = new Term[] { provedEqSides[1] };
		if (isApplication("false", provedEqSides[1])) {
			result = new Term[0];
			proof = mProofRules.resolutionRule(provedEqSides[1], proof, mProofRules.falseElim());
		} else if (isApplication("or", provedEqSides[1])) {
			result = ((ApplicationTerm) provedEqSides[1]).getParameters();
			proof = mProofRules.resolutionRule(provedEqSides[1], proof, mProofRules.orElim(provedEqSides[1]));
		}
		for (int i = 0; i < result.length; i++) {
			proof = removeNot(proof, result[i], true);
		}
		setResult(proof);
	}

	private Term convertQuant(final Term[] newParams) {
		final Theory theory = mSkript.getTheory();
		final AnnotatedTerm annotatedTerm = (AnnotatedTerm) newParams[0];
		final Annotation varAnnot = annotatedTerm.getAnnotations()[0];
		assert annotatedTerm.getAnnotations().length == 1
				&& (varAnnot.getKey() == ":forall" || varAnnot.getKey() == ":exists")
				&& (varAnnot.getValue() instanceof TermVariable[]);
		final boolean isForall = varAnnot.getKey() == ":forall";
		final TermVariable[] vars = (TermVariable[]) varAnnot.getValue();

		final Term subProof = annotatedTerm.getSubterm();
		/* Check that subproof is an equality */
		Term proof = subproof((AnnotatedTerm) subProof);
		final ApplicationTerm subEquality = (ApplicationTerm) provedTerm((AnnotatedTerm) subProof);
		assert isApplication("=", subEquality);
		final FormulaUnLet unletter = new FormulaUnLet();

		/* first show that subProof holds for all values of the variables */
		final Term[] skolem = mProofRules.getSkolemVars(vars, subEquality, true);
		final Term letEquality = unletter.unlet(theory.let(vars, skolem, subEquality));
		final Term letProof = unletter.unlet(theory.let(vars, skolem, proof));
		final QuantifiedFormula forallSubEquality = (QuantifiedFormula) theory.forall(vars, subEquality);
		final Term forallProof = res(letEquality, letProof, mProofRules.forallIntro(forallSubEquality));

		/* compute the proven equality (= (exists (...) lhs) (exists (...) rhs)) */
		final Term lhs = subEquality.getParameters()[0];
		final Term rhs = subEquality.getParameters()[1];

		final Term[] skolem1 = mProofRules.getSkolemVars(vars, isForall ? lhs : rhs, isForall);
		final Term let1Rhs = unletter.unlet(theory.let(vars, skolem1, rhs));
		final Term let1Lhs = unletter.unlet(theory.let(vars, skolem1, lhs));
		final Term let1Eq = theory.term(SMTLIBConstants.EQUALS, let1Lhs, let1Rhs);
		final Term let1Proof = mProofRules.forallElim(skolem1, forallSubEquality);

		final Term[] skolem2 = mProofRules.getSkolemVars(vars, isForall ? rhs : lhs, isForall);
		final Term let2Lhs = unletter.unlet(theory.let(vars, skolem2, lhs));
		final Term let2Rhs = unletter.unlet(theory.let(vars, skolem2, rhs));
		final Term let2Eq = theory.term(SMTLIBConstants.EQUALS, let2Lhs, let2Rhs);
		final Term let2Proof = mProofRules.forallElim(skolem2, forallSubEquality);
		final QuantifiedFormula quLhs = (QuantifiedFormula) (isForall ? theory.forall(vars, lhs)
				: theory.exists(vars, lhs));
		final QuantifiedFormula quRhs = (QuantifiedFormula) (isForall ? theory.forall(vars, rhs)
				: theory.exists(vars, rhs));
		final Term newEquality = theory.term("=", quLhs, quRhs);

		final Term proof1 = mProofRules.resolutionRule(let1Rhs,
				isForall ? mProofRules.forallElim(skolem1, quRhs) : mProofRules.existsElim(quRhs),
				mProofRules.resolutionRule(let1Lhs,
						mProofRules.resolutionRule(let1Eq, let1Proof, mProofRules.iffElim1(let1Eq)),
						isForall ? mProofRules.forallIntro(quLhs) : mProofRules.existsIntro(skolem1, quLhs)));
		final Term proof2 = mProofRules.resolutionRule(let2Lhs,
				isForall ? mProofRules.forallElim(skolem2, quLhs) : mProofRules.existsElim(quLhs),
				mProofRules.resolutionRule(let2Rhs,
						mProofRules.resolutionRule(let2Eq, let2Proof, mProofRules.iffElim2(let2Eq)),
						isForall ? mProofRules.forallIntro(quRhs) : mProofRules.existsIntro(skolem2, quRhs)));
		proof = proveIff(newEquality, proof2, proof1);
		proof = res(forallSubEquality, forallProof, proof);
		assert checkProof(proof, termToProofLiterals(newEquality));
		return annotateProved(newEquality, proof);
	}

	public Term convertLemma(ProofLiteral[] clause, Annotation annot) {
		final String name = annot.getKey();
		final Object annotValue = annot.getValue();
		Term result;
		switch (name) {
		case ":trans":
		case ":cong":
			result = convertCCLemma(clause, name, (Term[]) annotValue);
			break;
		case ":read-over-weakeq":
			result = convertArraySelectWeakEqLemma(clause, (Object[]) annotValue);
			break;
		case ":weakeq-ext":
			result = convertArrayWeakEqExtLemma(clause, (Object[]) annotValue);
			break;
		case ":read-const-weakeq":
			result = convertArraySelectConstWeakEqLemma(clause, (Object[]) annotValue);
			break;
		case ":dt-project":
			result = convertDTProject(clause, (Object[]) annotValue);
			break;
		case ":dt-tester":
			result = convertDTTester(clause, (Object[]) annotValue);
			break;
		case ":dt-constructor":
			result = convertDTConstructor(clause, (Object[]) annotValue);
			break;
		case ":dt-cases":
			result = convertDTCases(clause, (Object[]) annotValue);
			break;
		case ":dt-unique":
			result = convertDTUnique(clause, (Object[]) annotValue);
			break;
		case ":dt-injective":
			result = convertDTInjective(clause, (Object[]) annotValue);
			break;
		case ":dt-disjoint":
			result = convertDTDisjoint(clause, (Object[]) annotValue);
			break;
		case ":dt-cycle":
			result = convertDTCycle(clause, (Object[]) annotValue);
			break;
		case ":EQ":
			result = convertEQLemma(clause);
			break;
		case ":LA":
			result = convertLALemma(clause, (Term[]) annotValue);
			break;
		case ":trichotomy":
			result = convertTrichotomy(clause);
			break;
		default:
			throw new IllegalArgumentException("Unknown Lemma");
		}
		assert checkProof(result, clause);
		result = annotateProvedClause(result, annot, clause);
		return result;
	}

	private void convertMP(final ProofLiteral[] clause) {
		final AnnotatedTerm rewrite = (AnnotatedTerm) getConverted();
		final ApplicationTerm provedEq = (ApplicationTerm) provedTerm(rewrite);
		assert isApplication(SMTLIBConstants.EQUALS, provedEq);
		final Term[] eqParams = provedEq.getParameters();
		Term proof = res(provedEq, subproof(rewrite), mProofRules.iffElim2(provedEq));
		proof = removeNot(proof, eqParams[0], false);
		proof = removeNot(proof, eqParams[1], true);
		assert checkProof(proof, clause);
		setResult(proof);
	}

	public void convertOracle(final AnnotatedTerm oracle) {
		final Annotation[] annots = oracle.getAnnotations();
		assert annots.length >= 2;

		// annots[0] is :oracle ( proof literals )
		final Object[] lits = (Object[]) annots[0].getValue();
		assert lits.length % 2 == 0;
		final ProofLiteral[] clause = new ProofLiteral[lits.length / 2];
		for (int i = 0; i < clause.length; i++) {
			assert lits[2 * i].equals("+") || lits[2 * i].equals("-");
			clause[i] = new ProofLiteral((Term) lits[2 * i + 1], lits[2 * i].equals("+"));
		}

		// annots[1] is the first oracle annotation and determines the type.
		switch (annots[1].getKey()) {
		case ":trans":
		case ":cong":
		case ":read-over-weakeq":
		case ":weakeq-ext":
		case ":read-const-weakeq":
		case ":dt-project":
		case ":dt-tester":
		case ":dt-constructor":
		case ":dt-cases":
		case ":dt-unique":
		case ":dt-injective":
		case ":dt-disjoint":
		case ":dt-cycle":
		case ":EQ":
		case ":LA":
		case ":trichotomy":
			setResult(convertLemma(clause, annots[1]));
			break;
		case ":true+":
		case ":false-":
		case ":or+":
		case ":or-":
		case ":and+":
		case ":and-":
		case ":=>+":
		case ":=>-":
		case ":xor+1":
		case ":xor+2":
		case ":xor-1":
		case ":xor-2":
		case ":ite+1":
		case ":ite+2":
		case ":ite+red":
		case ":ite-1":
		case ":ite-2":
		case ":ite-red":
		case ":=+1":
		case ":=+2":
		case ":=-1":
		case ":=-2":
		case ":exists-":
		case ":forall+":
		case ":exists+":
		case ":forall-":
		case ":termITE":
		case ":termITEBound":
		case ":trueNotFalse":
		case ":excludedMiddle1":
		case ":excludedMiddle2":
		case ":divHigh":
		case ":divLow":
		case ":toIntHigh":
		case ":toIntLow":
		case ":store":
		case ":diff":
		case ":matchCase":
		case ":matchDefault":
			setResult(convertTautology(clause, annots[1]));
			break;

		case ProofConstants.ANNOTKEY_REWRITE:
			enqueueWalker((NonRecursive engine) -> ((ProofSimplifier) engine).convertMP(clause));
			convert((Term) annots[1].getValue());
			break;
		case ":inst": {
			final Object[] instAnnot = (Object[]) annots[1].getValue();
			assert instAnnot[3] == ":subproof";
			enqueueWalker((NonRecursive engine) -> ((ProofSimplifier) engine).convertInstLemma(clause, instAnnot));
			convert((Term) instAnnot[4]);
			break;
		}
		default:
			setResult(oracle);
			return;
		}
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm old, final Term[] newParams) {
		if (old.getSort().getName() == ProofConstants.SORT_EQPROOF) {
			switch (old.getFunction().getName()) {
			case ProofConstants.FN_TRANS: {
				setResult(convertTrans(newParams));
				return;
			}
			case ProofConstants.FN_CONG: {
				setResult(convertCong(old.getFunction(), newParams));
				return;
			}
			case ProofConstants.FN_MATCH: {
				setResult(convertMatch(newParams));
				return;
			}
			case ProofConstants.FN_QUANT: {
				setResult(convertQuant(newParams));
				return;
			}
			default:
				throw new AssertionError("Cannot translate proof rule: " + old.getFunction());
			}
		} else {
			assert ProofRules.isProof(old);
			super.convertApplicationTerm(old, newParams);
		}
	}

	@Override
	public void convert(final Term term) {
		// don't convert sub-formulas (in optional :proves annotations and resolutions).
		if (term.getSort() == term.getTheory().getBooleanSort()) {
			setResult(term);
		} else if (term.getSort().getName() == ProofConstants.SORT_EQPROOF && term instanceof ApplicationTerm) {
			// handle reflexivity and rewrite proofs
			final ApplicationTerm rewriteProof = (ApplicationTerm) term;
			switch (rewriteProof.getFunction().getName()) {
			case ProofConstants.FN_REFL: {
				final Term t = rewriteProof.getParameters()[0];
				setResult(annotateProved(t.getTheory().term(SMTLIBConstants.EQUALS, t, t), mProofRules.refl(t)));
				return;
			}
			case ProofConstants.FN_REWRITE: {
				final AnnotatedTerm lhsAnnot = (AnnotatedTerm) rewriteProof.getParameters()[0];
				final Annotation annot = lhsAnnot.getAnnotations()[0];
				final Term lhs = lhsAnnot.getSubterm();
				final Term rhs = rewriteProof.getParameters()[1];
				setResult(convertRewrite(lhs, rhs, annot));
				return;
			}
			default:
				super.convert(term);
			}
		} else if (ProofRules.isOracle(term)) {
			convertOracle((AnnotatedTerm) term);
		} else {
			super.convert(term);
		}
	}


	/* === Auxiliary functions === */

	private Term expandAux(final ApplicationTerm auxTerm) {
		final FunctionSymbol auxFunc = auxTerm.getFunction();
		return new FormulaUnLet()
				.unlet(mSkript.let(auxFunc.getDefinitionVars(), auxTerm.getParameters(), auxFunc.getDefinition()));
	}

	private Term expandAuxDef(final ApplicationTerm auxEqTerm) {
		final ApplicationTerm auxTerm = (ApplicationTerm) auxEqTerm.getParameters()[0];
		return expandAux(auxTerm);
	}

	/**
	 * Negate a term, avoiding double negation. If formula is (not x) it returns x, otherwise it returns (not formula).
	 *
	 * @param formula
	 *            the formula to negate.
	 * @return the negated formula.
	 */
	private Term negate(final Term formula) {
		if (isApplication("not", formula)) {
			return ((ApplicationTerm) formula).getParameters()[0];
		}
		return formula.getTheory().term("not", formula);
	}

	/**
	 * Parses a constant term. It handles Rationals given as ConstantTerm or parsed as div terms.
	 *
	 * @param term
	 *            the term to parse.
	 * @returns the parsed constant, null if parse error occured.
	 */
	private Rational parseConstant(final Term term) {
		return Polynomial.parseConstant(term);
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
	private boolean isApplication(final String funcSym, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (func.isIntern() && func.getName().equals(funcSym)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks if a term is zero, either Int or Real.
	 *
	 * @param zero
	 *            the term to check.
	 * @return true if zero is 0.
	 */
	private boolean isZero(final Term zero) {
		return zero == Rational.ZERO.toTerm(zero.getSort());
	}

	/**
	 * Substitute terms in forallElim.
	 *
	 * @param subst substitution
	 * @param qf    universal quantifier
	 * @return substituted formula annotated with proof that qf implies substituted
	 *         formula.
	 */
	private AnnotatedTerm substituteInQuantInst(final Term[] subst, final QuantifiedFormula qf) {
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term rhs = unletter.unlet(qf.getTheory().let(qf.getVariables(), subst, qf.getSubformula()));
		final Term proof = mProofRules.forallElim(subst, qf);
		return (AnnotatedTerm) annotateProved(rhs, proof);
	}

	/**
	 * Prove that first and second are equal (modulo order of operands for +).
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return the proof for `(= first second)` or null if this is not a trivial disequality.
	 */
	private Term proveTrivialEquality(final Term first, final Term second) {
		if (first == second) {
			return mProofRules.refl(first);
		}
		if (!first.getSort().isNumericSort()) {
			return null;
		}
		final SMTAffineTerm diff = new SMTAffineTerm(second);
		diff.negate();
		diff.add(new SMTAffineTerm(first));
		if (diff.isConstant() && diff.getConstant().equals(Rational.ZERO)) {
			final Theory theory = first.getTheory();
			final Term ltTerm = theory.term(SMTLIBConstants.LT, first, second);
			final Term gtTerm = theory.term(SMTLIBConstants.LT, second, first);
			final BigInteger[] one = new BigInteger[] { BigInteger.ONE };
			return res(ltTerm, res(gtTerm, mProofRules.trichotomy(first, second),
					mProofRules.farkas(new Term[] { gtTerm }, one)), mProofRules.farkas(new Term[] { ltTerm }, one));
		} else {
			return null;
		}
	}

	/**
	 * Prove that the disequality between two terms is trivial. There are two cases,
	 * (1) the difference between the terms is constant and nonzero, e.g.
	 * {@code (= x (+ x 1))}, or (2) the difference contains only integer variables
	 * and the constant divided by the gcd of the factors is non-integral, e.g.,
	 * {@code (= (+ x (* 2 y)) (+ x (* 2 z) 1))}.
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return the proof for `~(= first second)` or null if this is not a trivial disequality.
	 */
	private Term proveTrivialDisequality(final Term first, final Term second) {
		final Theory theory = first.getTheory();
		final SMTAffineTerm diff = new SMTAffineTerm(first);
		diff.add(Rational.MONE, second);
		if (diff.isConstant()) {
			if (diff.getConstant().signum() > 0) {
				final Term eqLhs = theory.term(SMTLIBConstants.EQUALS, first, second);
				return mProofRules.farkas(new Term[] { eqLhs }, new BigInteger[] { BigInteger.ONE });
			} else if (diff.getConstant().signum() < 0) {
				final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
				return mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
						mProofRules.farkas(new Term[] { eqSwapped }, new BigInteger[] { BigInteger.ONE }));
			} else {
				return null;
			}
		} else {
			final Rational gcd = diff.getGcd();
			diff.div(gcd);
			final Rational bound = diff.getConstant().negate();
			if (!diff.isAllIntSummands() || bound.isIntegral()) {
				return null;
			}
			final Sort intSort = theory.getSort(SMTLIBConstants.INT);
			diff.add(bound);
			final Term intVar = diff.toTerm(intSort);
			final Term floorBound = bound.floor().toTerm(intSort);
			final Term ceilBound = bound.ceil().toTerm(intSort);
			assert ceilBound != floorBound;
			// show (ceil(bound) <= intVar) || (intVar <= floor(bound)
			final Term geqCeil = theory.term(SMTLIBConstants.LEQ, ceilBound, intVar);
			final Term leqFloor = theory.term(SMTLIBConstants.LEQ, intVar, floorBound);
			final Term proofIntCase = mProofRules.totalInt(intVar, bound.floor().numerator());
			// show inequality in both cases
			final Term eqLhs = theory.term(SMTLIBConstants.EQUALS, first, second);
			final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
			final Term caseCeil = mProofRules.farkas(new Term[] { eqLhs, geqCeil },
					new BigInteger[] { gcd.denominator(), gcd.numerator() });
			final Term caseFloor = mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
					mProofRules.farkas(new Term[] { eqSwapped, leqFloor },
							new BigInteger[] { gcd.denominator(), gcd.numerator() }));
			return mProofRules.resolutionRule(leqFloor, mProofRules.resolutionRule(geqCeil, proofIntCase, caseCeil),
					caseFloor);
		}
	}

	/**
	 * Prove that `(= (abs rat) |rat|)` where rat is a rational constant, |rat| is
	 * the rational for the absolute value of rat, and `(abs rat)` is the SMTLIB
	 * function abs applied to rat.
	 *
	 * @param rat  the rational constant
	 * @param sort the sort of the constant.
	 * @return the proof for the equality.
	 */
	private Term proveAbsConstant(final Rational rat, final Sort sort) {
		final Theory theory = sort.getTheory();
		final Term x = rat.toTerm(sort);
		final Term absx = theory.term(SMTLIBConstants.ABS, x);
		final Term zero = Rational.ZERO.toTerm(sort);
		final Term ltXZero = theory.term("<", x, zero);
		final Term absxDef = theory.term("ite", ltXZero, theory.term("-", x), x);
		Term proof;
		if (rat.signum() >= 0) {
			proof = mProofRules.trans(absx, absxDef, x);
			proof = res(theory.term(SMTLIBConstants.EQUALS, absxDef, x), mProofRules.ite2(absxDef), proof);
			proof = res(ltXZero, proof,
					mProofRules.farkas(new Term[] { ltXZero }, new BigInteger[] { BigInteger.ONE }));
		} else {
			final Term minusX = theory.term("-", x);
			proof = mProofRules.trans(absx, absxDef, minusX, rat.abs().toTerm(sort));
			proof = res(theory.term(SMTLIBConstants.EQUALS, absxDef, minusX), mProofRules.ite1(absxDef), proof);
			proof = res(ltXZero, mProofRules.total(zero, x), proof);
			final Term leqZeroX = theory.term(SMTLIBConstants.LEQ, zero, x);
			proof = res(leqZeroX, proof,
					mProofRules.farkas(new Term[] { leqZeroX }, new BigInteger[] { BigInteger.ONE }));
			final Term eqMinusX = theory.term(SMTLIBConstants.EQUALS, minusX, rat.abs().toTerm(sort));
			proof = res(eqMinusX, convertRewriteCanonicalSum(minusX, rat.abs().toTerm(sort)), proof);
		}
		proof = res(theory.term(SMTLIBConstants.EQUALS, absx, absxDef), mProofRules.expand(absx), proof);
		return proof;
	}

	/**
	 * Prove the needed equalities and disequalities in the right form. It handles
	 * symmetric cases and trivial equalities/disequalities.
	 *
	 * @param proof               the proof that is modified to remove the
	 *                            equalities/disequalities
	 * @param allEqualities       a hash map from symmetric pair to the equality as
	 *                            it appears (negated) in the clause.
	 * @param allDisequalities    a hash map from symmetric pair to the equality as
	 *                            it appears (positive) in the clause.
	 * @param neededEqualities    a set of needed equalities (occurring negative in
	 *                            the proved clause)
	 * @param neededDisequalities a set of needed disequalities (occurring positive
	 *                            in the proved clause).
	 * @return the modified proof.
	 */
	private Term resolveNeededEqualities(Term proof, final Map<SymmetricPair<Term>, Term> allEqualities,
			final Map<SymmetricPair<Term>, Term> allDisequalities, final Set<Term> neededEqualities,
			final Set<Term> neededDisequalities) {
		for (final Term eq : neededEqualities) {
			assert isApplication("=", eq);
			final Term[] eqParam = ((ApplicationTerm) eq).getParameters();
			final Term clauseEq = allEqualities.get(new SymmetricPair<>(eqParam[0], eqParam[1]));
			if (clauseEq != null) {
				if (clauseEq != eq) {
					// need symmetry
					proof = res(eq, mProofRules.symm(eqParam[0], eqParam[1]), proof);
				}
			} else {
				final Term proofEq = proveTrivialEquality(eqParam[0], eqParam[1]);
				assert proofEq != null;
				proof = res(eq, proofEq, proof);
			}
		}
		for (final Term eq : neededDisequalities) {
			assert isApplication("=", eq);
			final Term[] eqParam = ((ApplicationTerm) eq).getParameters();
			final Term clauseEq = allDisequalities.get(new SymmetricPair<>(eqParam[0], eqParam[1]));
			if (clauseEq != eq) {
				// need symmetry
				proof = res(eq, proof, mProofRules.symm(eqParam[1], eqParam[0]));
			}
		}
		return proof;
	}

	/**
	 * Convert a clause term into an Array of terms, one entry for each disjunct.
	 * This also handles singleton and empty clause correctly.
	 *
	 * @param clauseTerm The term representing a clause.
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
	 * Convert an array of terms into an array of proof literals, one entry for each
	 * disjunct. This also removes double negations.
	 *
	 * @param clauseTerm The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private ProofLiteral[] termArrayToProofLiterals(final Term[] clauseLits) {
		final ProofLiteral[] proofLits = new ProofLiteral[clauseLits.length];
		for (int i = 0; i < proofLits.length; i++) {
			Term lit = clauseLits[i];
			boolean polarity = true;
			while (isApplication("not", lit)) {
				lit = ((ApplicationTerm) lit).getParameters()[0];
				polarity = !polarity;
			}
			proofLits[i] = new ProofLiteral(lit, polarity);
		}
		return proofLits;
	}

	/**
	 * Convert a clause term into an array of proof literals, one entry for each
	 * disjunct. This also removes double negations.
	 *
	 * @param clauseTerm The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private ProofLiteral[] termToProofLiterals(final Term clauseTerm) {
		return termArrayToProofLiterals(termToClause(clauseTerm));
	}

	/**
	 * Prove an equality of the form `(= lhs true)`.
	 *
	 * @param equality      an equality of the form `(= lhs true)`.
	 * @param proofLeftTrue a proof for lhs, or `lhs, ~true`.
	 * @return a proof for the equality.
	 */
	private Term proveIffTrue(final Term equality, final Term proofLeftTrue) {
		assert isApplication("=", equality);
		final Term[] sides = ((ApplicationTerm) equality).getParameters();
		assert isApplication("true", sides[1]);
		return res(sides[1], mProofRules.trueIntro(), res(sides[0], proofLeftTrue, mProofRules.iffIntro2(equality)));
	}

	/**
	 * Prove an equality of the form `(= lhs false)`.
	 *
	 * @param equality      an equality of the form `(= lhs false)`.
	 * @param proofLeftTrue a proof for `~lhs` or `false, ~lhs`.
	 * @return a proof for the equality.
	 */
	private Term proveIffFalse(final Term equality, final Term proofLeftFalse) {
		assert isApplication("=", equality);
		final Term[] sides = ((ApplicationTerm) equality).getParameters();
		assert isApplication("false", sides[1]);
		return res(sides[1], res(sides[0], mProofRules.iffIntro1(equality), proofLeftFalse),
				mProofRules.falseElim());
	}

	private Term proveIff(final Term equality, final Term proofLeftToRight, final Term proofRightToLeft) {
		assert isApplication("=", equality);
		final Term[] sides = ((ApplicationTerm) equality).getParameters();
		assert sides.length == 2;
		if (isApplication("true", sides[1])) {
			// simpler proof for common case
			return proveIffTrue(equality, proofRightToLeft);
		} else if (isApplication("false", sides[1])) {
			return proveIffFalse(equality, proofLeftToRight);
		} else {
			return mProofRules.resolutionRule(sides[1],
					mProofRules.resolutionRule(sides[0], mProofRules.iffIntro1(equality), proofLeftToRight),
					mProofRules.resolutionRule(sides[0], proofRightToLeft, mProofRules.iffIntro2(equality)));
		}
	}

	/**
	 * Resolution rule which handles null proofs (for not resolving).
	 *
	 * @param pivot    The pivot literal.
	 * @param proofPos The proof proving `+ pivot`.
	 * @param proofNeg The proof proving `- pivot`.
	 * @return the combined proof.
	 */
	private Term res(final Term pivot, final Term proofPos, final Term proofNeg) {
		return proofPos == null ? proofNeg
				: proofNeg == null ? proofPos : mProofRules.resolutionRule(pivot, proofPos, proofNeg);
	}

	/**
	 * Proves the clause { (= auxTerm false), expanded }.
	 *
	 * @param auxEqAtom the (= auxTerm true) term
	 * @param expanded  the expanded definition of auxTerm
	 * @return the proof
	 */
	private Term proveAuxElim(final ApplicationTerm auxEqAtom, final Term expanded) {
		final ApplicationTerm auxTerm = (ApplicationTerm) auxEqAtom.getParameters()[0];
		final Term falseTerm = mSkript.term(SMTLIBConstants.FALSE);
		final Term expandEq = mSkript.term(SMTLIBConstants.EQUALS, auxTerm, expanded);

		return res(auxTerm, res(falseTerm, mProofRules.iffIntro1(auxEqAtom), mProofRules.falseElim()),
				res(expandEq, mProofRules.expand(auxTerm), mProofRules.iffElim2(expandEq)));
	}

	/**
	 * Proves the equality (= (= auxTerm true) expanded).
	 *
	 * @param auxEqAtom the (= auxTerm true) term
	 * @param expanded  the expanded definition of auxTerm
	 * @return the proof
	 */
	private Term proveAuxExpand(final ApplicationTerm auxEqAtom, final Term expanded) {
		final ApplicationTerm auxTerm = (ApplicationTerm) auxEqAtom.getParameters()[0];
		final Term trueTerm = mSkript.term(SMTLIBConstants.TRUE);
		final Term firstEq = mSkript.term(SMTLIBConstants.EQUALS, auxEqAtom, auxTerm);
		final Term secondEq = mSkript.term(SMTLIBConstants.EQUALS, auxTerm, expanded);

		return mProofRules.resolutionRule(firstEq,
						mProofRules.resolutionRule(trueTerm, mProofRules.trueIntro(),
								proveIff(firstEq, mProofRules.iffElim1(auxEqAtom),
										mProofRules.iffIntro2(auxEqAtom))),
						mProofRules.resolutionRule(secondEq, mProofRules.expand(auxTerm),
						mProofRules.trans(auxEqAtom, auxTerm, expanded)));
	}

	/**
	 * Proof a linear equality rhs from a linear equality lhs. This proves
	 *
	 * <pre>
	 * (=&gt; (= lhs[0] lhs[1]) (= rhs[0] rhs[1])
	 * </pre>
	 *
	 * where (lhs[0] - lhs[1]) * multiplier == (rhs[0] - rhs[1]).
	 *
	 * @param lhs        the terms that are known to be equal
	 * @param rhs        the terms that should be proved to be equal.
	 * @param multiplier the factor that makes the sides equal.
	 * @return the proof.
	 */
	private Term proveEqWithMultiplier(final Term[] lhs, final Term[] rhs, final Rational multiplier) {
		final Theory theory = lhs[0].getTheory();
		final Term eqLhs = theory.term(SMTLIBConstants.EQUALS, lhs[0], lhs[1]);
		final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, lhs[1], lhs[0]);
		final Term ltRhs1 = theory.term(SMTLIBConstants.LT, rhs[0], rhs[1]);
		final Term ltRhs2 = theory.term(SMTLIBConstants.LT, rhs[1], rhs[0]);
		final boolean isSwapped2 = multiplier.signum() < 0;
		final BigInteger[] coeffs = new BigInteger[] { multiplier.numerator().abs(), multiplier.denominator() };
		final Term proof1 = mProofRules.farkas(new Term[] { isSwapped2 ? eqLhs : eqSwapped, ltRhs1 }, coeffs);
		final Term proof2 = mProofRules.farkas(new Term[] { isSwapped2 ? eqSwapped : eqLhs, ltRhs2 }, coeffs);
		Term proof = res(ltRhs1, res(ltRhs2, mProofRules.trichotomy(rhs[0], rhs[1]), proof2), proof1);
		proof = res(eqSwapped, mProofRules.symm(lhs[1], lhs[0]), proof);
		return proof;
	}

	private Term proveRewriteWithLinEq(final Term lhs, final Term rhs) {
		final Theory theory = lhs.getTheory();
		assert isApplication("=", lhs) && isApplication("=", rhs);

		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
		final SMTAffineTerm lhsAffine = new SMTAffineTerm(lhsParams[0]);
		lhsAffine.add(Rational.MONE, lhsParams[1]);
		final SMTAffineTerm rhsAffine = new SMTAffineTerm(rhsParams[0]);
		rhsAffine.add(Rational.MONE, rhsParams[1]);
		// we cannot compute gcd on constants so check for this and bail out
		assert !lhsAffine.isConstant() && !rhsAffine.isConstant() : "A trivial equality was created";
		Rational multiplier = lhsAffine.getGcd().div(rhsAffine.getGcd());
		rhsAffine.mul(multiplier);
		final boolean swapSides = !lhsAffine.equals(rhsAffine);
		if (swapSides) {
			rhsAffine.negate();
			multiplier = multiplier.negate();
		}
		assert lhsAffine.equals(rhsAffine);
		return proveIff(theory.term(SMTLIBConstants.EQUALS, lhs, rhs),
				proveEqWithMultiplier(lhsParams, rhsParams, multiplier.inverse()),
				proveEqWithMultiplier(rhsParams, lhsParams, multiplier));
	}

	private Term proveRewriteWithLeq(final Term lhs, final Term rhs, final boolean allowFactor) {
		final Theory theory = lhs.getTheory();

		final boolean isGreater = isApplication(">", lhs) || isApplication(">=", lhs);
		final boolean rhsIsNegated = isApplication("not", rhs);
		final Term rhsAtom = rhsIsNegated ? negate(rhs) : rhs;
		Term[] lhsParam = ((ApplicationTerm) lhs).getParameters();
		final Term[] rhsAtomParam = ((ApplicationTerm) rhsAtom).getParameters();
		final boolean isStrictLhs = isApplication("<", lhs) || isApplication(">", lhs);
		final boolean isStrictRhsAtom = isApplication("<", rhsAtom);

		if (isGreater) {
			lhsParam = new Term[] { lhsParam[1], lhsParam[0] };
		}
		final Term posLhs = theory.term(isStrictLhs ? "<" : "<=", lhsParam[0], lhsParam[1]);
		final Term negLhs = theory.term(isStrictLhs ? "<=" : "<", lhsParam[1], lhsParam[0]);

		Rational factor = Rational.ONE;
		boolean needsIntReasoning = false;
		if (allowFactor) {
			final SMTAffineTerm lhsAffine = new SMTAffineTerm(lhsParam[0]);
			lhsAffine.add(Rational.MONE, lhsParam[1]);
			final SMTAffineTerm rhsAffine = new SMTAffineTerm(rhsAtomParam[0]);
			rhsAffine.add(Rational.MONE, rhsAtomParam[1]);
			assert !lhsAffine.isConstant() && !rhsAffine.isConstant();
			final Term someTerm = lhsAffine.getSummands().keySet().iterator().next();
			factor = lhsAffine.getSummands().get(someTerm).div(rhsAffine.getSummands().get(someTerm)).abs();

			// Round constant up for integers: (<= (x + 1.25) 0) --> (<= (x + 2) 0)
			if (lhsParam[0].getSort().getName().equals(SMTLIBConstants.INT)) {
				needsIntReasoning = !lhsAffine.getConstant().div(factor).isIntegral() || rhsIsNegated;
			}
		}

		Term negRhsAtom;
		Term rhsTotality;
		if (needsIntReasoning) {
			assert isZero(rhsAtomParam[1]);
			assert !isStrictLhs && !isStrictRhsAtom;
			final Term one = Rational.ONE.toTerm(rhsAtomParam[1].getSort());
			negRhsAtom = theory.term("<=", one, rhsAtomParam[0]);
			rhsTotality = mProofRules.totalInt(rhsAtomParam[0], BigInteger.ZERO);
		} else {
			negRhsAtom = theory.term(isStrictRhsAtom ? "<=" : "<", rhsAtomParam[1], rhsAtomParam[0]);
			rhsTotality = mProofRules.total(rhsAtomParam[isStrictRhsAtom ? 1 : 0],
					rhsAtomParam[isStrictRhsAtom ? 0 : 1]);
		}
		Term proofToRhsAtom = mProofRules.farkas(new Term[] { rhsIsNegated ? negLhs : posLhs, negRhsAtom },
				new BigInteger[] { factor.denominator(), factor.numerator() });
		proofToRhsAtom = mProofRules.resolutionRule(negRhsAtom, rhsTotality, proofToRhsAtom);
		final Term proofFromRhsAtom = mProofRules.farkas(new Term[] { rhsIsNegated ? posLhs : negLhs, rhsAtom },
				new BigInteger[] { factor.denominator(), factor.numerator() });
		Term proofLhsToRhs = rhsIsNegated
				? mProofRules.resolutionRule(rhsAtom, mProofRules.notIntro(rhs), proofFromRhsAtom)
				: proofToRhsAtom;
		Term proofRhsToLhs = rhsIsNegated
				? mProofRules.resolutionRule(rhsAtom, proofToRhsAtom, mProofRules.notElim(rhs))
				: proofFromRhsAtom;
		proofRhsToLhs = mProofRules.resolutionRule(negLhs,
				mProofRules.total(lhsParam[isStrictLhs ? 1 : 0], lhsParam[isStrictLhs ? 0 : 1]), proofRhsToLhs);
		Term greaterEq = null;
		if (isGreater) {
			greaterEq = theory.term("=", lhs, posLhs);
			proofLhsToRhs = mProofRules.resolutionRule(posLhs, mProofRules.iffElim2(greaterEq), proofLhsToRhs);
			proofRhsToLhs = mProofRules.resolutionRule(posLhs, proofRhsToLhs, mProofRules.iffElim1(greaterEq));

		}
		Term proof = proveIff(theory.term("=", lhs, rhs), proofLhsToRhs, proofRhsToLhs);
		if (isGreater) {
			proof = mProofRules.resolutionRule(greaterEq,
					isStrictLhs ? mProofRules.gtDef(lhs) : mProofRules.geqDef(lhs), proof);
		}
		return proof;
	}

	public Term transformProof(Term proof) {
		final CollectSkolemAux collector = new CollectSkolemAux();
		proof = collector.transform(proof);
		mAuxDefs = collector.getAuxDef();
		proof = super.transform(proof);
		final TermVariable[] freeVars = proof.getFreeVars();
		if (freeVars.length > 0) {
			final Theory theory = proof.getTheory();
			final Term[] values = new Term[freeVars.length];
			for (int i = 0; i < freeVars.length; i++) {
				values[i] = mProofRules.choose(freeVars[i], theory.mTrue);
			}
			proof = new FormulaUnLet().unlet(theory.let(freeVars, values, proof));
		}
		// add function symbols in reverse order
		final ArrayDeque<FunctionSymbol> reversedOrder = new ArrayDeque<>();
		for (final FunctionSymbol function : mAuxDefs.keySet()) {
			reversedOrder.addFirst(function);
		}
		for (final FunctionSymbol function : reversedOrder) {
			proof = mProofRules.defineFun(function, mAuxDefs.get(function), proof);
		}
		return proof;
	}

	class CollectSkolemAux extends TermTransformer {
		private final HashMap<FunctionSymbol, LambdaTerm> mQuantDefinedTerms = new LinkedHashMap<>();

		public HashMap<FunctionSymbol, LambdaTerm> getAuxDef() {
			return mQuantDefinedTerms;
		}

		@Override
		public void convert(Term term) {
			if (isAuxApplication(term) || isSkolem(term)) {
				final FunctionSymbol func = ((ApplicationTerm) term).getFunction();
				if (!mQuantDefinedTerms.containsKey(func)) {
					// recursively convert function definition, pop it from the result stack
					// afterwards, and only then add the function definition to make sure it's
					// dependent functions are defined first.
					enqueueWalker((final NonRecursive engine) -> {
						((CollectSkolemAux) engine).getConverted();
						if (!mQuantDefinedTerms.containsKey(func)) {
							mQuantDefinedTerms.put(func, (LambdaTerm) func.getTheory().lambda(func.getDefinitionVars(),
									func.getDefinition()));
						}
					});
					super.convert(func.getDefinition());
				}
			}
			super.convert(term);
		}
	}
}
