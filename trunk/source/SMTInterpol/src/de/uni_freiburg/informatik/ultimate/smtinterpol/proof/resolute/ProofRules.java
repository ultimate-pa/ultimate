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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;

public class ProofRules {
	// the function symbols
	public final static String RES = "res";
	public final static String ASSUME = "assume";
	public final static String AXIOM = "axiom";

	// the axioms
	public final static String ORACLE = ":oracle";
	public final static String FALSEE = ":false-";
	public final static String TRUEI = ":true+";
	public final static String NOTI = ":not+";
	public final static String NOTE = ":not-";
	public final static String ORI = ":or+";
	public final static String ORE = ":or-";
	public final static String ANDI = ":and+";
	public final static String ANDE = ":and-";
	public final static String IMPI = ":=>+";
	public final static String IMPE = ":=>-";
	public final static String IFFI1 = ":=+1";
	public final static String IFFI2 = ":=+2";
	public final static String IFFE1 = ":=-1";
	public final static String IFFE2 = ":=-2";
	public final static String XORI = ":xor+";
	public final static String XORE = ":xor-";
	public final static String FORALLI = ":forall+";
	public final static String FORALLE = ":forall-";
	public final static String EXISTSI = ":exists+";
	public final static String EXISTSE = ":exists-";
	// equality chains of length >=3
	public final static String EQI = ":=+";
	public final static String EQE = ":=-";
	public final static String DISTINCTI = ":distinct+";
	public final static String DISTINCTE = ":distinct-";

	public final static String ITE1 = ":ite1";
	public final static String ITE2 = ":ite2";
	public final static String REFL = ":refl";
	public final static String SYMM = ":symm";
	public final static String TRANS = ":trans";
	public final static String CONG = ":cong";
	public final static String EXPAND = ":expand";
	public final static String DELANNOT = ":del!";

	// rules for (non-)linear arithmetic
	public final static String TRICHOTOMY = ":trichotomy";
	public final static String TOTAL = ":total";
	public final static String TOTALINT = ":total-int";
	public final static String FARKAS = ":farkas";
	public final static String MULPOS = ":mulpos";
	public final static String TOINTHIGH = ":to_int-high";
	public final static String TOINTLOW = ":to_int-low";
	public final static String DIVIDEDEF = ":/def";
	public final static String POLYADD = ":poly+";
	public final static String POLYMUL = ":poly*";
	public final static String TOREALDEF = ":to_real-def";

	// rules for div/mod arithmetic
	public final static String DIVLOW = ":div-low";
	public final static String DIVHIGH = ":div-high";
	public final static String MODDEF = ":mod-def";

	// axioms for arrays
	public final static String SELECTSTORE1 = ":selectstore1";
	public final static String SELECTSTORE2 = ":selectstore2";
	public final static String EXTDIFF = ":extdiff";
	public final static String CONST = ":const";

	// axioms for datatypes
	public final static String DT_PROJECT = ":dt-project";
	public final static String DT_CONS = ":dt-cons";
	public final static String DT_TESTI = ":dt-test+";
	public final static String DT_TESTE = ":dt-test-";
	public final static String DT_EXHAUST = ":dt-exhaust";
	public final static String DT_ACYCLIC = ":dt-acyclic";
	public final static String DT_MATCH = ":dt-match";

	// axioms for bitvectors
	public final static String BVCONST = ":bvconst";
	public final static String BVLITERAL = ":bvliteral";
	public final static String INT2UBV2INT = ":int2ubv2int";
	public final static String INT2SBV2INT = ":int2sbv2int";
	public final static String UBV2INT2BV = ":ubv2int2bv";

	public final static String POW2CONST = ":pow2const";
	public final static String POW2ADD = ":pow2add";
	public final static String LOG2LOW = ":log2low";
	public final static String LOG2HIGH = ":log2high";

	public final static String BWANDFLAT = ":&flat";
	public final static String BWANDSHIFT = ":&shift";
	public final static String BWANDSPLIT = ":&split";
	public final static String BWANDBOUND = ":&bound";
	public final static String BWANDNONNEG = ":&nonneg";

	/**
	 * sort name for proofs.
	 */
	public final static String PROOF = "Proof";
	public final static String CHOOSE = "choose";

	public final static String PREFIX = "..";

	public final static String ANNOT_DEFINE_FUN = ":define-fun";
	public final static String ANNOT_REFINE_FUN = ":refine-fun";
	public final static String ANNOT_DECLARE_FUN = ":declare-fun";

	public ProofRules(final Theory theory) {
		mTheory = theory;
		setupTheory();
		mAxiom = theory.term(PREFIX + AXIOM);
	}

	private final Theory mTheory;
	private final Term mAxiom;

	private void setupTheory() {

		if (mTheory.getDeclaredSorts().containsKey(PREFIX + PROOF)) {
			return;
		}

		// In case SMTInterpol is not running
		if (mTheory.getLogic().isArray() && !mTheory.getFunctionFactories().containsKey(SMTInterpolConstants.DIFF)) {
			final Sort[] vars = mTheory.createSortVariables("Index", "Elem");
			final Sort array = mTheory.getSort("Array", vars);
			mTheory.declareInternalPolymorphicFunction(SMTInterpolConstants.DIFF, vars, new Sort[] { array, array },
					vars[0], FunctionSymbol.UNINTERPRETEDINTERNAL);
		}

		mTheory.declareInternalSort(PREFIX + PROOF, 0, 0);
		final Sort proofSort = mTheory.getSort(PREFIX + PROOF);
		final Sort boolSort = mTheory.getBooleanSort();
		final Sort[] generic = mTheory.createSortVariables("X");
		final Sort[] bool1 = new Sort[] { boolSort };
		final Sort[] sort0 = new Sort[0];
		final Sort[] lambda1 = new Sort[] { mTheory.getSort(SMTLIBConstants.FUNC, generic[0], boolSort) };

		mTheory.declareInternalFunction(PREFIX + RES, new Sort[] { boolSort, proofSort, proofSort }, proofSort, 0);
		mTheory.declareInternalFunction(PREFIX + AXIOM, sort0, proofSort, 0);
		mTheory.declareInternalFunction(PREFIX + ASSUME, bool1, proofSort, 0);
		mTheory.declareInternalPolymorphicFunction(PREFIX + CHOOSE, generic, lambda1, generic[0], 0);
	}

	public Theory getTheory() {
		return mTheory;
	}

	/**
	 * Check whether all terms have the same sort.
	 *
	 * @param terms an array of terms to check.
	 * @return true, iff all terms have the same sort.
	 */
	private static boolean equalSorts(Term[] terms) {
		final Sort sort = terms[0].getSort();
		for (int i = 1; i < terms.length; i++) {
			if (terms[i].getSort() != sort) {
				return false;
			}
		}
		return true;
	}

	public Term resolutionRule(final Term pivot, final Term proofPos, final Term proofNeg) {
		return mTheory.term(PREFIX + RES, pivot, proofPos, proofNeg);
	}

	public Term asserted(final Term t) {
		return mTheory.term(PREFIX + ASSUME, t);
	}

	public static Object[] convertProofLiteralsToAnnotation(final ProofLiteral[] literals) {
		final Object[] clause = new Object[2 * literals.length];
		for (int i = 0; i < literals.length; i++) {
			clause[2 * i] = literals[i].getPolarity() ? "+" : "-";
			clause[2 * i + 1] = literals[i].getAtom();
		}
		return clause;
	}

	public static ProofLiteral[] proofLiteralsFromAnnotation(final Object[] literals) {
		assert literals.length % 2 == 0;
		final ProofLiteral[] clause = new ProofLiteral[literals.length / 2];
		for (int i = 0; i < clause.length; i++) {
			assert literals[2 * i] == "+" || literals[2 * i] == "-";
			clause[i] = new ProofLiteral((Term) literals[2 * i + 1], literals[2 * i] == "+");
		}
		return clause;
	}

	public Term oracle(final ProofLiteral[] literals, final Annotation[] annots) {
		final Object[] clause = convertProofLiteralsToAnnotation(literals);
		final Annotation[] annotations = new Annotation[annots.length + 1];
		annotations[0] = new Annotation(ORACLE, clause);
		System.arraycopy(annots, 0, annotations, 1, annots.length);
		return mTheory.annotatedTerm(annotations, mAxiom);
	}

	public Term choose(final TermVariable tv, final Term formula) {
		final Term lambda = mTheory.lambda(new TermVariable[] { tv }, formula);
		return mTheory.term(PREFIX + CHOOSE, lambda);
	}

	public Term[] getSkolemVars(final TermVariable[] termVars, final Term subterm, final boolean isForall) {
		final Term[] skolemTerms = new Term[termVars.length];
		final FormulaUnLet unletter = new FormulaUnLet();
		for (int i = 0; i < skolemTerms.length; i++) {
			Term subform = subterm;
			if (i + 1 < skolemTerms.length) {
				final TermVariable[] remainingVars = new TermVariable[skolemTerms.length - i - 1];
				System.arraycopy(termVars, i + 1, remainingVars, 0, remainingVars.length);
				subform = isForall ? mTheory.forall(remainingVars, subform) : mTheory.exists(remainingVars, subform);
			}
			if (isForall) {
				subform = mTheory.term(SMTLIBConstants.NOT, subform);
			}
			if (i > 0) {
				final TermVariable[] precedingVars = new TermVariable[i];
				final Term[] precedingSkolems = new Term[i];
				System.arraycopy(termVars, 0, precedingVars, 0, i);
				System.arraycopy(skolemTerms, 0, precedingSkolems, 0, i);
				subform = unletter.unlet(mTheory.let(precedingVars, precedingSkolems, subform));
			}
			skolemTerms[i] = choose(termVars[i], subform);
		}
		return skolemTerms;
	}

	private Annotation[] annotate(final String rule, final Object... value) {
		return new Annotation[] { new Annotation(rule, value) };
	}

	public Term trueIntro() {
		return mTheory.annotatedTerm(annotate(TRUEI), mAxiom);
	}

	public Term falseElim() {
		return mTheory.annotatedTerm(annotate(FALSEE), mAxiom);
	}

	public Term notIntro(final Term notTerm) {
		assert notTerm instanceof TermVariable
				|| ((ApplicationTerm) notTerm).getFunction().getName() == SMTLIBConstants.NOT;
		return mTheory.annotatedTerm(annotate(NOTI, notTerm), mAxiom);
	}

	public Term notElim(final Term notTerm) {
		assert notTerm instanceof TermVariable
				|| ((ApplicationTerm) notTerm).getFunction().getName() == SMTLIBConstants.NOT;
		return mTheory.annotatedTerm(annotate(NOTE, notTerm), mAxiom);
	}

	public Term orIntro(final int pos, final Term orTerm) {
		assert orTerm instanceof TermVariable
				|| ((ApplicationTerm) orTerm).getFunction().getName() == SMTLIBConstants.OR;
		return mTheory.annotatedTerm(annotate(ORI, pos, orTerm), mAxiom);
	}

	public Term orElim(final Term orTerm) {
		assert orTerm instanceof TermVariable
				|| ((ApplicationTerm) orTerm).getFunction().getName() == SMTLIBConstants.OR;
		return mTheory.annotatedTerm(annotate(ORE, orTerm), mAxiom);
	}

	public Term andIntro(final Term andTerm) {
		assert andTerm instanceof TermVariable
				|| ((ApplicationTerm) andTerm).getFunction().getName() == SMTLIBConstants.AND;
		return mTheory.annotatedTerm(annotate(ANDI, andTerm), mAxiom);
	}

	public Term andElim(final int pos, final Term andTerm) {
		assert andTerm instanceof TermVariable
				|| ((ApplicationTerm) andTerm).getFunction().getName() == SMTLIBConstants.AND;
		return mTheory.annotatedTerm(annotate(ANDE, pos, andTerm), mAxiom);
	}

	public Term impIntro(final int pos, final Term impTerm) {
		assert impTerm instanceof TermVariable
				|| ((ApplicationTerm) impTerm).getFunction().getName() == SMTLIBConstants.IMPLIES;
		return mTheory.annotatedTerm(annotate(IMPI, pos, impTerm), mAxiom);
	}

	public Term impElim(final Term impTerm) {
		assert impTerm instanceof TermVariable
				|| ((ApplicationTerm) impTerm).getFunction().getName() == SMTLIBConstants.IMPLIES;
		return mTheory.annotatedTerm(annotate(IMPE, impTerm), mAxiom);
	}

	public Term iffIntro1(final Term iffTerm) {
		assert iffTerm instanceof TermVariable
				|| (((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS
						&& ((ApplicationTerm) iffTerm).getParameters().length == 2
						&& ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL);
		return mTheory.annotatedTerm(annotate(IFFI1, iffTerm), mAxiom);
	}

	public Term iffIntro2(final Term iffTerm) {
		assert iffTerm instanceof TermVariable
				|| (((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS
						&& ((ApplicationTerm) iffTerm).getParameters().length == 2
						&& ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL);
		return mTheory.annotatedTerm(annotate(IFFI2, iffTerm), mAxiom);
	}

	public Term iffElim1(final Term iffTerm) {
		assert iffTerm instanceof TermVariable
				|| (((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS
						&& ((ApplicationTerm) iffTerm).getParameters().length == 2
						&& ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL);
		return mTheory.annotatedTerm(annotate(IFFE1, iffTerm), mAxiom);
	}

	public Term iffElim2(final Term iffTerm) {
		assert iffTerm instanceof TermVariable
				|| (((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS
						&& ((ApplicationTerm) iffTerm).getParameters().length == 2
						&& ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL);
		return mTheory.annotatedTerm(annotate(IFFE2, iffTerm), mAxiom);
	}

	private Term xorAxiom(final String name, final Term[]... xorArgs) {
		assert CoreRules.checkXorParams(xorArgs);
		return mTheory.annotatedTerm(new Annotation[] { new Annotation(name, xorArgs) }, mAxiom);
	}

	public Term xorIntro(final Term[] xorArgs1, final Term[] xorArgs2, final Term[] xorArgs3) {
		return xorAxiom(XORI, xorArgs1, xorArgs2, xorArgs3);
	}

	public Term xorElim(final Term[] xorArgs1, final Term[] xorArgs2, final Term[] xorArgs3) {
		return xorAxiom(XORE, xorArgs1, xorArgs2, xorArgs3);
	}

	public Term forallIntro(final QuantifiedFormula forallTerm) {
		assert forallTerm.getQuantifier() == QuantifiedFormula.FORALL;
		return mTheory.annotatedTerm(annotate(FORALLI, forallTerm), mAxiom);
	}

	public Term forallElim(final Term[] subst, final QuantifiedFormula forallTerm) {
		assert forallTerm.getQuantifier() == QuantifiedFormula.FORALL;
		return mTheory.annotatedTerm(annotate(FORALLE, subst, forallTerm), mAxiom);
	}

	public Term existsIntro(final Term[] subst, final QuantifiedFormula existsTerm) {
		assert existsTerm.getQuantifier() == QuantifiedFormula.EXISTS;
		return mTheory.annotatedTerm(annotate(EXISTSI, subst, existsTerm), mAxiom);
	}

	public Term existsElim(final QuantifiedFormula existsTerm) {
		assert existsTerm.getQuantifier() == QuantifiedFormula.EXISTS;
		return mTheory.annotatedTerm(annotate(EXISTSE, existsTerm), mAxiom);
	}

	public Term equalsIntro(final Term eqTerm) {
		assert ((ApplicationTerm) eqTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		return mTheory.annotatedTerm(annotate(EQI, eqTerm), mAxiom);
	}

	public Term equalsElim(final int pos1, final int pos2, final Term eqTerm) {
		assert ((ApplicationTerm) eqTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		assert 0 <= pos1 && pos1 < ((ApplicationTerm) eqTerm).getParameters().length;
		assert 0 <= pos2 && pos2 < ((ApplicationTerm) eqTerm).getParameters().length;
		return mTheory.annotatedTerm(annotate(EQE, pos1, pos2, eqTerm), mAxiom);
	}

	public Term distinctIntro(final Term disTerm) {
		assert ((ApplicationTerm) disTerm).getFunction().getName() == SMTLIBConstants.DISTINCT;
		return mTheory.annotatedTerm(annotate(DISTINCTI, disTerm), mAxiom);
	}

	public Term distinctElim(final int pos1, final int pos2, final Term disTerm) {
		assert ((ApplicationTerm) disTerm).getFunction().getName() == SMTLIBConstants.DISTINCT;
		assert 0 <= pos1 && pos1 < ((ApplicationTerm) disTerm).getParameters().length;
		assert 0 <= pos2 && pos2 < ((ApplicationTerm) disTerm).getParameters().length;
		return mTheory.annotatedTerm(annotate(DISTINCTE, pos1, pos2, disTerm), mAxiom);
	}

	public Term refl(final Term term) {
		return mTheory.annotatedTerm(annotate(REFL, (Object[]) new Term[] { term }), mAxiom);
	}

	public Term symm(final Term term1, final Term term2) {
		return mTheory.annotatedTerm(annotate(SYMM, (Object[]) new Term[] { term1, term2 }), mAxiom);
	}

	public Term trans(final Term... terms) {
		assert terms.length > 2;
		assert equalSorts(terms);
		return mTheory.annotatedTerm(annotate(TRANS, (Object[]) terms), mAxiom);
	}

	public Term cong(final Term term1, final Term term2) {
		return mTheory.annotatedTerm(annotate(CONG, (Object[]) new Term[] { term1, term2 }), mAxiom);
	}

	public Term expand(final Term term) {
		return mTheory.annotatedTerm(annotate(EXPAND, term), mAxiom);
	}

	public Term ite1(final Term iteTerm) {
		assert iteTerm instanceof TermVariable
				|| ((ApplicationTerm) iteTerm).getFunction().getName() == SMTLIBConstants.ITE;
		return mTheory.annotatedTerm(annotate(ITE1, iteTerm), mAxiom);
	}

	public Term ite2(final Term iteTerm) {
		assert iteTerm instanceof TermVariable
				|| ((ApplicationTerm) iteTerm).getFunction().getName() == SMTLIBConstants.ITE;
		return mTheory.annotatedTerm(annotate(ITE2, iteTerm), mAxiom);
	}

	public Term delAnnot(final Term annotTerm) {
		return mTheory.annotatedTerm(annotate(DELANNOT, annotTerm), mAxiom);
	}

	public Term trichotomy(final Term lhs, final Term rhs) {
		return mTheory.annotatedTerm(annotate(TRICHOTOMY, (Object[]) new Term[] { lhs, rhs }), mAxiom);
	}

	public Term total(final Term lhs, final Term rhs) {
		return mTheory.annotatedTerm(annotate(TOTAL, (Object[]) new Term[] { lhs, rhs }), mAxiom);
	}

	/**
	 * Axiom for integer reasoning. This proves
	 *
	 * <pre>
	 * (+ (&lt;= x c) + (&lt;= (c+1) x))
	 * </pre>
	 *
	 * where x is a term of sort Int and c an integer constant. Here c+1 is the
	 * constant c increased by one.
	 *
	 * @param x
	 *            a term of sort Int.
	 * @param c
	 *            an integer constant.
	 * @return the axiom.
	 */
	public Term totalInt(final Term x, final Rational c) {
		assert c.isIntegral();
		return mTheory.annotatedTerm(annotate(TOTALINT, (Object[]) new Term[] { x, c.toTerm(x.getSort()) }),
				mAxiom);
	}

	/**
	 * The axiom {@code (farkas c1 (<=? a1 b1) ... cn (<=? an bn))} is proving that
	 * the inequalities are inconsistent. Here <=? stands for `<`, `=`, or `<=`. The
	 * inequalities must all be given. The ci must be BigInteger. The side condition
	 * is c = c1 * (a1 - b1) + ... + cn * (an - bn) is a non-negative constant. If
	 * there is no strict condition, then c must also not be zero.
	 *
	 * @param params an alternating sequence of BigInteger and inequality terms.
	 * @return the axiom.
	 */
	public Term farkas(final Object... params) {
		return mTheory.annotatedTerm(annotate(FARKAS, params), mAxiom);
	}

	/**
	 * Axiom stating `- (<=? 0 a) - (<=? 0 b) + (<=? 0 (* a b))`. Here <=? stands
	 * for `<` or `<=`. The inequalities must all be given, including the goal
	 * inequality. The side condition is that the left-hand side of all inequalities
	 * is 0, that the right-hand side of the last inequality is equal to the product
	 * of the other right-hand sides (modulo polynomial simplification), and the
	 * goal inequality must be <=, or all inequalities must be <.
	 *
	 * @param inequalities the literals of the axioms, the last is the goal
	 *                     inequality
	 * @return the axiom.
	 */
	public Term mulPos(final Term[] inequalities) {
		return mTheory.annotatedTerm(annotate(MULPOS, (Object[]) inequalities), mAxiom);
	}

	/**
	 * Axiom stating `(= (+ a1... an) = result)` where result is equal to the
	 * polynom addition of polynomials a1 ... an in standard form.
	 *
	 * @param plusTerm
	 *            the plus term.
	 * @param result
	 *            the result term.
	 * @return the axiom.
	 */
	public Term polyAdd(final Term plusTerm, final Term result) {
		return mTheory.annotatedTerm(annotate(POLYADD, (Object[]) new Term[] { plusTerm, result }), mAxiom);
	}

	/**
	 * Axiom stating `(= (+ a1... an) = result)` where result is equal to the
	 * polynom addition of polynomials a1 ... an in standard form.
	 *
	 * @param mulTerm
	 *            the plus term.
	 * @param result
	 *            the result term.
	 * @return the axiom.
	 */
	public Term polyMul(final Term mulTerm, final Term result) {
		return mTheory.annotatedTerm(annotate(POLYMUL, (Object[]) new Term[] { mulTerm, result }), mAxiom);
	}

	/**
	 * Axiom stating `(= (to_real a) = result)` where result is equal to the left
	 * hand side in standard form.
	 *
	 * @param integerTerm the term a.
	 * @param result      the result term.
	 * @return the axiom.
	 */
	public Term toRealDef(final Term integerTerm) {
		return mTheory.annotatedTerm(annotate(TOREALDEF, integerTerm), mAxiom);
	}

	/**
	 * Axiom stating `(= (* b1 ... bn (/ a b1 ...bn)) a)` or `(= b1 0)` ... or `(=
	 * bn 0)`.
	 *
	 * @param divParams the parameters `a, b1, ..., bn`.
	 * @return the axiom.
	 */
	public Term divideDef(final Term... divParams) {
		return mTheory.annotatedTerm(annotate(DIVIDEDEF, (Object[]) divParams), mAxiom);
	}

	/**
	 * Axiom stating `(<= (to_real (to_int arg)) arg)`.
	 *
	 * @param arg
	 *            a term of type Real.
	 * @return the axiom.
	 */
	public Term toIntLow(final Term arg) {
		assert arg.getSort().getSortSymbol().getName().equals("Real");
		return mTheory.annotatedTerm(annotate(TOINTLOW, (Object[]) new Term[] { arg }), mAxiom);
	}

	/**
	 * Axiom stating `(< arg (+ (to_real (to_int arg)) 1.0)`.
	 *
	 * @param arg
	 *            a term of type Real.
	 * @return the axiom.
	 */
	public Term toIntHigh(final Term arg) {
		assert arg.getSort().getSortSymbol().getName().equals("Real");
		return mTheory.annotatedTerm(annotate(TOINTHIGH, (Object[]) new Term[] { arg }), mAxiom);
	}

	/**
	 * Axiom stating `(<= (* divisor (div arg divisor)) arg)` or `(= divisor 0)`.
	 *
	 * @param arg
	 *            a term of type Int.
	 * @param divisor
	 *            a term of type Int.
	 * @return the axiom.
	 */
	public Term divLow(final Term arg, final Term divisor) {
		assert arg.getSort().getSortSymbol().getName().equals("Int");
		assert divisor.getSort() == arg.getSort();
		return mTheory.annotatedTerm(annotate(DIVLOW, (Object[]) new Term[] { arg, divisor }), mAxiom);
	}

	/**
	 * Axiom stating `(< arg (+ (* divisor (div arg divisor)) (abs divisor)))` or
	 * `(= divisor 0)`.
	 *
	 * @param arg
	 *            a term of type Int.
	 * @param divisor
	 *            a term of type Int.
	 * @return the axiom.
	 */
	public Term divHigh(final Term arg, final Term divisor) {
		assert arg.getSort().getSortSymbol().getName().equals("Int");
		assert divisor.getSort() == arg.getSort();
		return mTheory.annotatedTerm(annotate(DIVHIGH, (Object[]) new Term[] { arg, divisor }), mAxiom);
	}

	/**
	 * Axiom stating `(= (+ (* divisor (div arg divisor)) (mod arg divisor)) arg` or
	 * `(= divisor 0)`.
	 *
	 * @param arg
	 *            a term of type Int.
	 * @param divisor
	 *            a term of type Int.
	 * @return the axiom.
	 */
	public Term modDef(final Term arg, final Term divisor) {
		assert arg.getSort().getSortSymbol().getName().equals("Int");
		assert divisor.getSort() == arg.getSort();
		return mTheory.annotatedTerm(annotate(MODDEF, (Object[]) new Term[] { arg, divisor }), mAxiom);
	}

	public Term selectStore1(final Term array, final Term index, final Term value) {
		assert array.getSort().getSortSymbol().getName().equals(SMTLIBConstants.ARRAY);
		assert array.getSort().getArguments()[0] == index.getSort();
		assert array.getSort().getArguments()[1] == value.getSort();
		return mTheory.annotatedTerm(annotate(SELECTSTORE1, (Object[]) new Term[] { array, index, value }),
				mAxiom);
	}

	public Term selectStore2(final Term array, final Term index, final Term value, final Term index2) {
		assert array.getSort().getSortSymbol().getName().equals(SMTLIBConstants.ARRAY);
		assert array.getSort().getArguments()[0] == index.getSort();
		assert array.getSort().getArguments()[1] == value.getSort();
		assert array.getSort().getArguments()[0] == index2.getSort();
		return mTheory.annotatedTerm(
				annotate(SELECTSTORE2, (Object[]) new Term[] { array, index, value, index2 }), mAxiom);
	}

	public Term extDiff(final Term array1, final Term array2) {
		assert array1.getSort() == array2.getSort();
		assert array1.getSort().getSortSymbol().getName().equals(SMTLIBConstants.ARRAY);
		return mTheory.annotatedTerm(annotate(EXTDIFF, (Object[]) new Term[] { array1, array2 }), mAxiom);
	}

	public Term constArray(final Term constValue, final Term index) {
		return mTheory.annotatedTerm(annotate(CONST, (Object[]) new Term[] { constValue, index }), mAxiom);
	}

	public Term defineFun(final FunctionSymbol func, final Term definition, final Term subProof) {
		return mTheory.annotatedTerm(annotate(ANNOT_DEFINE_FUN, func, definition), subProof);
	}

	public Term refineFun(final FunctionSymbol func, final Term definition, final Term subProof) {
		return mTheory.annotatedTerm(annotate(ANNOT_REFINE_FUN, func, definition), subProof);
	}

	public Term declareFun(final FunctionSymbol func, final Term subProof) {
		return mTheory.annotatedTerm(annotate(ANNOT_DECLARE_FUN, func), subProof);
	}

	public Term dtProject(final Term selConsTerm) {
		return mTheory.annotatedTerm(annotate(DT_PROJECT, (Object[]) new Term[] { selConsTerm }), mAxiom);
	}

	public Term dtCons(final Term isConsTerm) {
		return mTheory.annotatedTerm(annotate(DT_CONS, (Object[]) new Term[] { isConsTerm }), mAxiom);
	}

	public Term dtTestI(final Term consTerm) {
		return mTheory.annotatedTerm(annotate(DT_TESTI, (Object[]) new Term[] { consTerm }), mAxiom);
	}

	public Term dtTestE(final String otherConstructor, final Term consTerm) {
		return mTheory.annotatedTerm(annotate(DT_TESTE, otherConstructor, consTerm), mAxiom);
	}

	public Term dtExhaust(final Term term) {
		assert term.getSort().getSortSymbol() instanceof DataType;
		return mTheory.annotatedTerm(annotate(DT_EXHAUST, (Object[]) new Term[] { term }), mAxiom);
	}

	public Term dtAcyclic(final Term consTerm, final int[] positions) {
		return mTheory.annotatedTerm(annotate(DT_ACYCLIC, new Object[] { consTerm, positions }), mAxiom);
	}

	public Term dtMatch(final Term matchTerm) {
		return mTheory.annotatedTerm(annotate(DT_MATCH, (Object[]) new Term[] { matchTerm }), mAxiom);
	}

	/**
	 * Axiom stating that `(= (_ bvconstValue bitLength) ((_ int2bv bitLength)
	 * constValue))`.
	 *
	 * @param constValue A natural number.
	 * @param bitLength  The bit length of the bitvector.
	 * @return the axiom.
	 */
	public Term bvConst(final BigInteger constValue, final BigInteger bitLength) {
		assert constValue.signum() >= 0;
		assert bitLength.bitCount() <= 32;
		assert constValue.bitLength() <= bitLength.intValue();
		final Term constTerm = Rational.valueOf(constValue, BigInteger.ONE).toTerm(mTheory.getNumericSort());
		return mTheory.annotatedTerm(annotate(BVCONST, constTerm, bitLength.intValue()), mAxiom);
	}

	public Term bvLiteral(final String bvLiteral) {
		assert bvLiteral.matches("#x[0-9a-fA-F]+") || bvLiteral.matches("#b[01]+");
		final Term litTerm = bvLiteral.startsWith("#b") ? mTheory.binary(bvLiteral) : mTheory.hexadecimal(bvLiteral);
		return mTheory.annotatedTerm(annotate(BVLITERAL, litTerm), mAxiom);
	}

	/**
	 * Axiom stating `(= (ubv_to_int ((_ int_to_bv bitLength) natTerm)) (mod natTerm
	 * 2^bitLength))`
	 *
	 * @param bitLength the length of the bit vector.
	 * @param natTerm   the nat term that is converted to bv and back.
	 * @return the axiom.
	 */
	public Term int2ubv2int(final BigInteger bitLength, final Term natTerm) {
		assert natTerm.getSort().isInternal() && natTerm.getSort().getName().equals("Int");
		assert bitLength.bitCount() <= 32;
		return mTheory.annotatedTerm(annotate(INT2UBV2INT, bitLength.intValue(), natTerm), mAxiom);
	}

	/**
	 * Axiom stating `(= (sbv_to_int ((_ int_to_bv bitLength) natTerm)) (+ (mod (+
	 * natTerm 2^(bitlength-1)) 2^bitLength) (- 2^(bitlength-1)))`
	 *
	 * @param bitLength the length of the bit vector.
	 * @param natTerm   the nat term that is converted to bv and back.
	 * @return the axiom.
	 */
	public Term int2sbv2int(final BigInteger bitLength, final Term natTerm) {
		assert natTerm.getSort().isInternal() && natTerm.getSort().getName().equals("Int");
		assert bitLength.bitCount() <= 32;
		return mTheory.annotatedTerm(annotate(INT2SBV2INT, bitLength.intValue(), natTerm), mAxiom);
	}

	/**
	 * Axiom stating `(= ((_ int_to_bv bitLength) (ubv_to_int bvTerm)) bvTerm)`.
	 * Here bitLength is the size of the bitvector bvTerm (so that the equality
	 * type-checks).
	 *
	 * @param bvTerm the bv term that is converted to int and back.
	 * @return the axiom.
	 */
	public Term ubv2int2bv(final Term bvTerm) {
		assert bvTerm.getSort().isBitVecSort();
		return mTheory.annotatedTerm(annotate(UBV2INT2BV, bvTerm), mAxiom);
	}

	public static void printProof(final Appendable appender, final Term proof) {
		new PrintProof().append(appender, proof);
	}

	static boolean isApplication(final String funcName, final Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol func = ((ApplicationTerm) term).getFunction();
			return func.isIntern() && func.getName().equals(funcName);
		}
		return false;
	}

	public static boolean checkConstructorPath(Term consTerm, final int[] positions) {
		if (positions.length == 0) {
			return false;
		}
		for (final int pos : positions) {
			final ApplicationTerm term = (ApplicationTerm) consTerm;
			if (!term.getFunction().isConstructor() || pos < 0 || pos >= term.getParameters().length) {
				return false;
			}
			consTerm = term.getParameters()[pos];
		}
		return true;
	}

	public static boolean isAxiom(final Term proof) {
		return proof instanceof AnnotatedTerm && isApplication(PREFIX + AXIOM, ((AnnotatedTerm) proof).getSubterm());
	}

	public static boolean isOracle(Term proof) {
		return isAxiom(proof) && ((AnnotatedTerm) proof).getAnnotations()[0].getKey().equals(ORACLE);
	}

	public static boolean isProofRule(final String rule, final Term proof) {
		return proof instanceof ApplicationTerm
				&& ((ApplicationTerm) proof).getFunction().getName().equals(PREFIX + rule);
	}

	public static boolean isDefineFun(final Term proof) {
		return proof instanceof AnnotatedTerm
				&& ANNOT_DEFINE_FUN.equals(((AnnotatedTerm) proof).getAnnotations()[0].getKey());
	}

	public static boolean isRefineFun(final Term proof) {
		return proof instanceof AnnotatedTerm
				&& ANNOT_REFINE_FUN.equals(((AnnotatedTerm) proof).getAnnotations()[0].getKey());
	}

	public static boolean isDeclareFun(final Term proof) {
		return proof instanceof AnnotatedTerm
				&& ANNOT_DECLARE_FUN.equals(((AnnotatedTerm) proof).getAnnotations()[0].getKey());
	}

	public static boolean isProof(final Term proof) {
		return proof.getSort().isInternal() && proof.getSort().getName().equals(PREFIX + PROOF);
	}
}
