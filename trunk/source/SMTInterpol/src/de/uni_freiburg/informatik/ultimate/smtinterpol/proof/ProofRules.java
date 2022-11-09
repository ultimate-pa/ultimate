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
import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
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
	public final static String ORACLE = "oracle";
	public final static String FALSEE = "false-";
	public final static String TRUEI = "true+";
	public final static String NOTI = "not+";
	public final static String NOTE = "not-";
	public final static String ORI = "or+";
	public final static String ORE = "or-";
	public final static String ANDI = "and+";
	public final static String ANDE = "and-";
	public final static String IMPI = "=>+";
	public final static String IMPE = "=>-";
	public final static String IFFI1 = "=+1";
	public final static String IFFI2 = "=+2";
	public final static String IFFE1 = "=-1";
	public final static String IFFE2 = "=-2";
	public final static String XORI = "xor+";
	public final static String XORE = "xor-";
	public final static String FORALLI = "forall+";
	public final static String FORALLE = "forall-";
	public final static String EXISTSI = "exists+";
	public final static String EXISTSE = "exists-";
	// equality chains of length >=3
	public final static String EQI = "=+";
	public final static String EQE = "=-";
	public final static String DISTINCTI = "distinct+";
	public final static String DISTINCTE = "distinct-";

	public final static String ITE1 = "ite1";
	public final static String ITE2 = "ite2";
	public final static String REFL = "refl";
	public final static String SYMM = "symm";
	public final static String TRANS = "trans";
	public final static String CONG = "cong";
	public final static String EXPAND = "expand";
	public final static String DELANNOT = "del!";

	// rules for (non-)linear arithmetic
	public final static String DIVISIBLEDEF = "divisible-def";
	public final static String GTDEF = ">def";
	public final static String GEQDEF = ">=def";
	public final static String TRICHOTOMY = "trichotomy";
	public final static String TOTAL = "total";
	public final static String TOTALINT = "total-int";
	public final static String FARKAS = "farkas";
	public final static String TOINTHIGH = "to_int-high";
	public final static String TOINTLOW = "to_int-low";
	public final static String MINUSDEF = "-def";
	public final static String DIVIDEDEF = "/def";
	public final static String POLYADD = "poly+";
	public final static String POLYMUL = "poly*";
	public final static String TOREALDEF = "to_real-def";

	// rules for div/mod arithmetic
	public final static String DIVLOW = "div-low";
	public final static String DIVHIGH = "div-high";
	public final static String MODDEF = "mod-def";

	// axioms for arrays
	public final static String SELECTSTORE1 = "selectstore1";
	public final static String SELECTSTORE2 = "selectstore2";
	public final static String EXTDIFF = "extdiff";
	public final static String CONST = "const";

	// axioms for datatypes
	public final static String DT_PROJECT = "dt-project";
	public final static String DT_CONS = "dt-cons";
	public final static String DT_TESTI = "dt-test+";
	public final static String DT_TESTE = "dt-test-";
	public final static String DT_EXHAUST = "dt-exhaust";
	public final static String DT_ACYCLIC = "dt-acyclic";
	public final static String DT_MATCH = "dt-match";

	/**
	 * sort name for proofs.
	 */
	public final static String PROOF = "Proof";
	public final static String CHOOSE = "choose";

	public final static String PREFIX = "..";

	public final static String ANNOT_VALUES = ":values";
	public final static String ANNOT_COEFFS = ":coeffs";
	public final static String ANNOT_DIVISOR = ":divisor";
	public final static String ANNOT_POS = ":pos";
	public final static String ANNOT_UNIT = ":unit";
	public final static String ANNOT_DEFINE_FUN = ":define-fun";
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

	private static boolean isKeyword(final Object obj) {
		return obj instanceof String && ((String) obj).charAt(0) == ':';
	}

	static Annotation[] convertSExprToAnnotation(final Object[] objects) {
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < objects.length; i++) {
			assert isKeyword(objects[i]);
			final String keyword = (String) objects[i];
			Object value = null;
			if (i + 1 < objects.length && !isKeyword(objects[i + 1])) {
				i++;
				value = objects[i];
			}
			annots.add(new Annotation(keyword, value));
		}
		return annots.toArray(new Annotation[annots.size()]);
	}

	static Object[] convertAnnotationsToSExpr(final Annotation[] annots) {
		final ArrayList<Object> sexpr = new ArrayList<>();
		for (final Annotation a : annots) {
			sexpr.add(a.getKey());
			if (a.getValue() != null) {
				sexpr.add(a.getValue());
			}
		}
		return sexpr.toArray(new Object[sexpr.size()]);
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
		return mTheory.annotatedTerm(annotate(":" + ORACLE, clause, annots), mAxiom);
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

	private Annotation[] annotate(final String rule, final Object value, final Annotation... moreAnnots) {
		final Annotation[] annots = new Annotation[moreAnnots.length + 1];
		annots[0] = new Annotation(rule, value);
		System.arraycopy(moreAnnots, 0, annots, 1, moreAnnots.length);
		return annots;
	}

	public Term trueIntro() {
		return mTheory.annotatedTerm(annotate(":" + TRUEI, null), mAxiom);
	}

	public Term falseElim() {
		return mTheory.annotatedTerm(annotate(":" + FALSEE, null), mAxiom);
	}

	public Term notIntro(final Term notTerm) {
		assert notTerm instanceof TermVariable
				|| ((ApplicationTerm) notTerm).getFunction().getName() == SMTLIBConstants.NOT;
		return mTheory.annotatedTerm(annotate(":" + NOTI, notTerm), mAxiom);
	}

	public Term notElim(final Term notTerm) {
		assert notTerm instanceof TermVariable
				|| ((ApplicationTerm) notTerm).getFunction().getName() == SMTLIBConstants.NOT;
		return mTheory.annotatedTerm(annotate(":" + NOTE, notTerm), mAxiom);
	}

	public Term orIntro(final int pos, final Term orTerm) {
		assert orTerm instanceof TermVariable
				|| ((ApplicationTerm) orTerm).getFunction().getName() == SMTLIBConstants.OR;
		return mTheory.annotatedTerm(
				annotate(":" + ORI, orTerm, new Annotation(ANNOT_POS, pos)),
				mAxiom);
	}

	public Term orElim(final Term orTerm) {
		assert orTerm instanceof TermVariable
				|| ((ApplicationTerm) orTerm).getFunction().getName() == SMTLIBConstants.OR;
		return mTheory.annotatedTerm(annotate(":" + ORE, orTerm), mAxiom);
	}

	public Term andIntro(final Term andTerm) {
		assert andTerm instanceof TermVariable
				|| ((ApplicationTerm) andTerm).getFunction().getName() == SMTLIBConstants.AND;
		return mTheory.annotatedTerm(annotate(":" + ANDI, andTerm), mAxiom);
	}

	public Term andElim(final int pos, final Term andTerm) {
		assert andTerm instanceof TermVariable
				|| ((ApplicationTerm) andTerm).getFunction().getName() == SMTLIBConstants.AND;
		return mTheory.annotatedTerm(
				annotate(":" + ANDE, andTerm, new Annotation(ANNOT_POS, pos)),
				mAxiom);
	}

	public Term impIntro(final int pos, final Term impTerm) {
		assert impTerm instanceof TermVariable
				|| ((ApplicationTerm) impTerm).getFunction().getName() == SMTLIBConstants.IMPLIES;
		return mTheory.annotatedTerm(
				annotate(":" + IMPI, impTerm, new Annotation(ANNOT_POS, pos)),
				mAxiom);
	}

	public Term impElim(final Term impTerm) {
		assert impTerm instanceof TermVariable
				|| ((ApplicationTerm) impTerm).getFunction().getName() == SMTLIBConstants.IMPLIES;
		return mTheory.annotatedTerm(annotate(":" + IMPE, impTerm), mAxiom);
	}

	public Term iffIntro1(final Term iffTerm) {
		assert iffTerm instanceof TermVariable
				|| (((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS
						&& ((ApplicationTerm) iffTerm).getParameters().length == 2
						&& ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL);
		return mTheory.annotatedTerm(annotate(":" + IFFI1, iffTerm), mAxiom);
	}

	public Term iffIntro2(final Term iffTerm) {
		assert iffTerm instanceof TermVariable
				|| (((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS
						&& ((ApplicationTerm) iffTerm).getParameters().length == 2
						&& ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL);
		return mTheory.annotatedTerm(annotate(":" + IFFI2, iffTerm), mAxiom);
	}

	public Term iffElim1(final Term iffTerm) {
		assert iffTerm instanceof TermVariable
				|| (((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS
						&& ((ApplicationTerm) iffTerm).getParameters().length == 2
						&& ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL);
		return mTheory.annotatedTerm(annotate(":" + IFFE1, iffTerm), mAxiom);
	}

	public Term iffElim2(final Term iffTerm) {
		assert iffTerm instanceof TermVariable
				|| (((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS
						&& ((ApplicationTerm) iffTerm).getParameters().length == 2
						&& ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL);
		return mTheory.annotatedTerm(annotate(":" + IFFE2, iffTerm), mAxiom);
	}

	private Term xorAxiom(final String name, final Term[]... xorArgs) {
		assert checkXorParams(xorArgs);
		return mTheory.annotatedTerm(new Annotation[] { new Annotation(name, xorArgs) }, mAxiom);
	}

	public Term xorIntro(final Term[] xorArgs1, final Term[] xorArgs2, final Term[] xorArgs3) {
		return xorAxiom(":" + XORI, xorArgs1, xorArgs2, xorArgs3);
	}

	public Term xorElim(final Term[] xorArgs1, final Term[] xorArgs2, final Term[] xorArgs3) {
		return xorAxiom(":" + XORE, xorArgs1, xorArgs2, xorArgs3);
	}

	public Term forallIntro(final QuantifiedFormula forallTerm) {
		assert forallTerm.getQuantifier() == QuantifiedFormula.FORALL;
		return mTheory.annotatedTerm(annotate(":" + FORALLI, forallTerm), mAxiom);
	}

	public Term forallElim(final Term[] subst, final QuantifiedFormula forallTerm) {
		assert forallTerm.getQuantifier() == QuantifiedFormula.FORALL;
		return mTheory.annotatedTerm(annotate(":" + FORALLE, forallTerm,
				new Annotation(ANNOT_VALUES, subst)), mAxiom);
	}

	public Term existsIntro(final Term[] subst, final QuantifiedFormula existsTerm) {
		assert existsTerm.getQuantifier() == QuantifiedFormula.EXISTS;
		return mTheory.annotatedTerm(annotate(":" + EXISTSI, existsTerm,
				new Annotation(ANNOT_VALUES, subst)), mAxiom);
	}

	public Term existsElim(final QuantifiedFormula existsTerm) {
		assert existsTerm.getQuantifier() == QuantifiedFormula.EXISTS;
		return mTheory.annotatedTerm(annotate(":" + EXISTSE, existsTerm), mAxiom);
	}

	public Term equalsIntro(final Term eqTerm) {
		assert ((ApplicationTerm) eqTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		return mTheory.annotatedTerm(annotate(":" + EQI, eqTerm), mAxiom);
	}

	public Term equalsElim(final int pos1, final int pos2, final Term eqTerm) {
		assert ((ApplicationTerm) eqTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		assert 0 <= pos1 && pos1 < ((ApplicationTerm) eqTerm).getParameters().length;
		assert 0 <= pos2 && pos2 < ((ApplicationTerm) eqTerm).getParameters().length;
		return mTheory.annotatedTerm(annotate(":" + EQE, eqTerm,
				new Annotation(ANNOT_POS, new Integer[] { pos1, pos2 })), mAxiom);
	}

	public Term distinctIntro(final Term disTerm) {
		assert ((ApplicationTerm) disTerm).getFunction().getName() == SMTLIBConstants.DISTINCT;
		return mTheory.annotatedTerm(annotate(":" + DISTINCTI, disTerm), mAxiom);
	}

	public Term distinctElim(final int pos1, final int pos2, final Term disTerm) {
		assert ((ApplicationTerm) disTerm).getFunction().getName() == SMTLIBConstants.DISTINCT;
		assert 0 <= pos1 && pos1 < ((ApplicationTerm) disTerm).getParameters().length;
		assert 0 <= pos2 && pos2 < ((ApplicationTerm) disTerm).getParameters().length;
		return mTheory.annotatedTerm(annotate(":" + DISTINCTE, disTerm,
				new Annotation(ANNOT_POS, new Integer[] { pos1, pos2 })), mAxiom);
	}

	public Term refl(final Term term) {
		return mTheory.annotatedTerm(annotate(":" + REFL, new Term[] { term }), mAxiom);
	}

	public Term symm(final Term term1, final Term term2) {
		return mTheory.annotatedTerm(annotate(":" + SYMM, new Term[] { term1, term2 }), mAxiom);
	}

	public Term trans(final Term... terms) {
		assert terms.length > 2;
		return mTheory.annotatedTerm(annotate(":" + TRANS, terms), mAxiom);
	}

	public Term cong(final FunctionSymbol func, final Term[] params1, final Term[] params2) {
		assert params1.length == params2.length;
		final Annotation[] annot = new Annotation[] {
				new Annotation(":" + CONG, new Object[] { func, params1, params2 }) };
		return mTheory.annotatedTerm(annot, mAxiom);
	}

	public Term cong(final Term term1, final Term term2) {
		final ApplicationTerm app1 = (ApplicationTerm) term1;
		final ApplicationTerm app2 = (ApplicationTerm) term2;
		assert app1.getFunction() == app2.getFunction();
		return cong(app1.getFunction(), app1.getParameters(), app2.getParameters());
	}

	public Term expand(final Term term) {
		final Annotation[] annot = new Annotation[] { new Annotation(":" + EXPAND,
				new Object[] { ((ApplicationTerm) term).getFunction(), ((ApplicationTerm) term).getParameters(), }) };
		return mTheory.annotatedTerm(annot, mAxiom);
	}

	public Term ite1(final Term iteTerm) {
		assert iteTerm instanceof TermVariable
				|| ((ApplicationTerm) iteTerm).getFunction().getName() == SMTLIBConstants.ITE;
		return mTheory.annotatedTerm(annotate(":" + ITE1, iteTerm), mAxiom);
	}

	public Term ite2(final Term iteTerm) {
		assert iteTerm instanceof TermVariable
				|| ((ApplicationTerm) iteTerm).getFunction().getName() == SMTLIBConstants.ITE;
		return mTheory.annotatedTerm(annotate(":" + ITE2, iteTerm), mAxiom);
	}

	public Term delAnnot(final Term annotTerm) {
		final Term subterm = ((AnnotatedTerm) annotTerm).getSubterm();
		final Object[] subAnnots = convertAnnotationsToSExpr(((AnnotatedTerm) annotTerm).getAnnotations());
		return mTheory.annotatedTerm(annotate(":" + DELANNOT, new Object[] { subterm, subAnnots }), mAxiom);
	}

	public Term divisible(final BigInteger divisor, final Term lhs) {
		assert divisor.signum() > 0;
		assert lhs.getSort().getName().equals(SMTLIBConstants.INT);
		return mTheory.annotatedTerm(
				annotate(":" + DIVISIBLEDEF, new Term[] { lhs }, new Annotation(ANNOT_DIVISOR, divisor)), mAxiom);
	}

	public Term gtDef(final Term greaterTerm) {
		assert ((ApplicationTerm) greaterTerm).getFunction().getName() == SMTLIBConstants.GT;
		return mTheory.annotatedTerm(annotate(":" + GTDEF, ((ApplicationTerm) greaterTerm).getParameters()), mAxiom);
	}

	public Term geqDef(final Term greaterTerm) {
		assert ((ApplicationTerm) greaterTerm).getFunction().getName() == SMTLIBConstants.GEQ;
		return mTheory.annotatedTerm(annotate(":" + GEQDEF, ((ApplicationTerm) greaterTerm).getParameters()), mAxiom);
	}

	public Term trichotomy(final Term lhs, final Term rhs) {
		return mTheory.annotatedTerm(annotate(":" + TRICHOTOMY, new Term[] { lhs, rhs }), mAxiom);
	}

	public Term total(final Term lhs, final Term rhs) {
		return mTheory.annotatedTerm(annotate(":" + TOTAL, new Term[] { lhs, rhs }), mAxiom);
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
	public Term totalInt(final Term x, final BigInteger c) {
		return mTheory.annotatedTerm(annotate(":" + TOTALINT, new Object[] { x, c }), mAxiom);
	}

	public Term farkas(final Term[] inequalities, final BigInteger[] coefficients) {
		return mTheory.annotatedTerm(annotate(":" + FARKAS, inequalities, new Annotation(ANNOT_COEFFS, coefficients)),
				mAxiom);
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
		return mTheory.annotatedTerm(annotate(":" + POLYADD, new Term[] { plusTerm, result }), mAxiom);
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
		return mTheory.annotatedTerm(annotate(":" + POLYMUL, new Term[] { mulTerm, result }), mAxiom);
	}

	/**
	 * Axiom stating `(= (to_real a) = result)` where result is equal to the left
	 * hand side in standard form.
	 *
	 * @param toRealTerm
	 *            the to_real term.
	 * @param result
	 *            the result term.
	 * @return the axiom.
	 */
	public Term toRealDef(final Term toRealTerm) {
		assert isApplication(SMTLIBConstants.TO_REAL, toRealTerm);
		return mTheory.annotatedTerm(annotate(":" + TOREALDEF, ((ApplicationTerm) toRealTerm).getParameters()), mAxiom);
	}

	/**
	 * Axiom stating `(= (* b1 ... bn (/ a b1 ...bn)) a)` or `(= b1 0)` ... or `(=
	 * bn 0)`.
	 *
	 * @param divideTerm
	 *            the term `(/a b1 ... bn)`.
	 * @return the axiom.
	 */
	public Term divideDef(final Term divTerm) {
		assert isApplication(SMTLIBConstants.DIVIDE, divTerm);
		return mTheory.annotatedTerm(annotate(":" + DIVIDEDEF, ((ApplicationTerm) divTerm).getParameters()), mAxiom);
	}

	/**
	 * Axiom stating `(= (- a) (* (- 1) a)` resp. `(= (- a b1 .. bn) (+ a (* (- 1)
	 * b1) .. (* (- 1) bn))`.
	 *
	 * @param minusTerm
	 *            the minus term.
	 * @return the axiom.
	 */
	public Term minusDef(final Term minusTerm) {
		assert isApplication(SMTLIBConstants.MINUS, minusTerm);
		return mTheory.annotatedTerm(annotate(":" + MINUSDEF, ((ApplicationTerm) minusTerm).getParameters()), mAxiom);
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
		return mTheory.annotatedTerm(annotate(":" + TOINTLOW, new Term[] { arg }), mAxiom);
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
		return mTheory.annotatedTerm(annotate(":" + TOINTHIGH, new Term[] { arg }), mAxiom);
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
		return mTheory.annotatedTerm(annotate(":" + DIVLOW, new Term[] { arg, divisor }), mAxiom);
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
		return mTheory.annotatedTerm(annotate(":" + DIVHIGH, new Term[] { arg, divisor }), mAxiom);
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
		return mTheory.annotatedTerm(annotate(":" + MODDEF, new Term[] { arg, divisor }), mAxiom);
	}

	public Term selectStore1(final Term array, final Term index, final Term value) {
		assert array.getSort().getSortSymbol().getName().equals(SMTLIBConstants.ARRAY);
		assert array.getSort().getArguments()[0] == index.getSort();
		assert array.getSort().getArguments()[1] == value.getSort();
		return mTheory.annotatedTerm(annotate(":" + SELECTSTORE1, new Term[] { array, index, value }), mAxiom);
	}

	public Term selectStore2(final Term array, final Term index, final Term value, final Term index2) {
		assert array.getSort().getSortSymbol().getName().equals(SMTLIBConstants.ARRAY);
		assert array.getSort().getArguments()[0] == index.getSort();
		assert array.getSort().getArguments()[1] == value.getSort();
		assert array.getSort().getArguments()[0] == index2.getSort();
		return mTheory.annotatedTerm(annotate(":" + SELECTSTORE2, new Term[] { array, index, value, index2 }), mAxiom);
	}

	public Term extDiff(final Term array1, final Term array2) {
		assert array1.getSort() == array2.getSort();
		assert array1.getSort().getSortSymbol().getName().equals(SMTLIBConstants.ARRAY);
		return mTheory.annotatedTerm(annotate(":" + EXTDIFF, new Term[] { array1, array2 }), mAxiom);
	}

	public Term constArray(final Term constValue, final Term index) {
		return mTheory.annotatedTerm(annotate(":" + CONST, new Term[] { constValue, index }), mAxiom);
	}

	public Term defineFun(final FunctionSymbol func, final Term definition, final Term subProof) {
		return mTheory.annotatedTerm(
				new Annotation[] { new Annotation(ANNOT_DEFINE_FUN, new Object[] { func, definition }), }, subProof);
	}

	public Term declareFun(final FunctionSymbol func, final Term subProof) {
		return mTheory.annotatedTerm(new Annotation[] { new Annotation(ANNOT_DECLARE_FUN, new Object[] { func }), },
				subProof);
	}

	public Term dtProject(final Term selConsTerm) {
		return mTheory.annotatedTerm(annotate(":" + DT_PROJECT, new Term[] { selConsTerm }), mAxiom);
	}

	public Term dtCons(final Term isConsTerm) {
		return mTheory.annotatedTerm(annotate(":" + DT_CONS, new Term[] { isConsTerm }), mAxiom);
	}

	public Term dtTestI(final Term consTerm) {
		return mTheory.annotatedTerm(annotate(":" + DT_TESTI, new Term[] { consTerm }), mAxiom);
	}

	public Term dtTestE(final String otherConstructor, final Term consTerm) {
		return mTheory.annotatedTerm(annotate(":" + DT_TESTE, new Object[] { otherConstructor, consTerm }), mAxiom);
	}

	public Term dtExhaust(final Term term) {
		assert term.getSort().getSortSymbol() instanceof DataType;
		return mTheory.annotatedTerm(annotate(":" + DT_EXHAUST, new Term[] { term }), mAxiom);
	}

	public Term dtAcyclic(final Term consTerm, final int[] positions) {
		return mTheory.annotatedTerm(annotate(":" + DT_ACYCLIC, new Object[] { consTerm, positions }), mAxiom);
	}

	public Term dtMatch(final Term matchTerm) {
		return mTheory.annotatedTerm(annotate(":" + DT_MATCH, new Term[] { matchTerm }), mAxiom);
	}

	public static void printProof(final Appendable appender, final Term proof) {
		new PrintProof().append(appender, proof);
	}

	private static boolean isApplication(final String funcName, final Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol func = ((ApplicationTerm) term).getFunction();
			return func.isIntern() && func.getName().equals(funcName);
		}
		return false;
	}

	/**
	 * Check the parameters of a poly+ axiom. It checks that the plusTerm is an
	 * application of `+` and that the sum of its arguments minus the results (using
	 * polynomial addition) sums to zero.
	 *
	 * @param plusTerm
	 *            the plus term (first argument of the poly+ axiom).
	 * @param result
	 *            the result term (second argument of the poly+ axiom).
	 * @return true iff the parameters are wellformed.
	 */
	public static boolean checkPolyAdd(final Term plusTerm, final Term result) {
		if (!isApplication(SMTLIBConstants.PLUS, plusTerm)) {
			return false;
		}
		final Polynomial poly = new Polynomial();
		for (final Term t : ((ApplicationTerm) plusTerm).getParameters()) {
			poly.add(Rational.ONE, t);
		}
		poly.add(Rational.MONE, result);
		return poly.isZero();
	}

	/**
	 * Check the parameters of a poly* axiom. It checks that the mulTerm is an
	 * application of `*` and that the product of its arguments minus the results
	 * (using polynomial multiplication and subtraction) gives zero.
	 *
	 * @param mulTerm
	 *            the mul term (first argument of the poly* axiom).
	 * @param result
	 *            the result term (second argument of the poly* axiom).
	 * @return true iff the parameters are wellformed.
	 */
	public static boolean checkPolyMul(final Term mulTerm, final Term result) {
		if (!isApplication(SMTLIBConstants.MUL, mulTerm)) {
			return false;
		}
		final Polynomial poly = new Polynomial();
		poly.add(Rational.ONE);
		for (final Term t : ((ApplicationTerm) mulTerm).getParameters()) {
			poly.mul(new Polynomial(t));
		}
		poly.add(Rational.MONE, result);
		return poly.isZero();
	}

	private static Term computeFactorToReal(final Term factor) {
		if (factor instanceof ConstantTerm && ((ConstantTerm) factor).getValue() instanceof Rational) {
			return ((Rational) ((ConstantTerm) factor).getValue()).toTerm(factor.getTheory().getSort("Real"));
		} else {
			return factor.getTheory().term(SMTLIBConstants.TO_REAL, factor);
		}
	}

	private static Term computeMonomialToReal(final Term monomial) {
		if (isApplication(SMTLIBConstants.MUL, monomial)) {
			final Term[] oldParams = ((ApplicationTerm) monomial).getParameters();
			final Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				newParams[i] = computeFactorToReal(oldParams[i]);
			}
			return monomial.getTheory().term(SMTLIBConstants.MUL, newParams);
		} else {
			return computeFactorToReal(monomial);
		}
	}

	public static Term computePolyToReal(final Term poly) {
		if (isApplication(SMTLIBConstants.PLUS, poly)) {
			final Term[] oldParams = ((ApplicationTerm) poly).getParameters();
			final Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				newParams[i] = computeMonomialToReal(oldParams[i]);
			}
			return poly.getTheory().term(SMTLIBConstants.PLUS, newParams);
		} else {
			return computeMonomialToReal(poly);
		}
	}

	public static Term computePolyMinus(final Term minusTerm) {
		assert isApplication(SMTLIBConstants.MINUS, minusTerm);
		final Theory theory = minusTerm.getTheory();
		final Term[] params = ((ApplicationTerm) minusTerm).getParameters();
		final Term minusOne = Rational.MONE.toTerm(minusTerm.getSort());
		if (params.length == 1) {
			return theory.term(SMTLIBConstants.MUL, minusOne, params[0]);
		} else {
			final Term[] rhsParams = new Term[params.length];
			rhsParams[0] = params[0];
			for (int i = 1; i < params.length; i++) {
				rhsParams[i] = theory.term(SMTLIBConstants.MUL, minusOne, params[i]);
			}
			return theory.term(SMTLIBConstants.PLUS, rhsParams);
		}
	}

	public static boolean checkFarkas(final Term[] inequalities, final BigInteger[] coefficients) {
		if (inequalities.length != coefficients.length) {
			return false;
		}
		final Polynomial sum = new Polynomial();
		boolean strict = false;
		for (int i = 0; i < inequalities.length; i++) {
			if (coefficients[i].signum() != 1) {
				return false;
			}
			if (!isApplication(SMTLIBConstants.LT, inequalities[i])
					&& !isApplication(SMTLIBConstants.LEQ, inequalities[i])
					&& !isApplication(SMTLIBConstants.EQUALS, inequalities[i])) {
				return false;
			}
			final ApplicationTerm appTerm = (ApplicationTerm) inequalities[i];
			final Term[] params = appTerm.getParameters();
			if (params.length != 2) {
				return false;
			}
			if (appTerm.getFunction().getName() == SMTLIBConstants.LT) {
				strict = true;
			}
			final Rational coeff = Rational.valueOf(coefficients[i], BigInteger.ONE);
			sum.add(coeff, params[0]);
			sum.add(coeff.negate(), params[1]);
		}
		final boolean okay = sum.isConstant() && sum.getConstant().signum() >= (strict ? 0 : 1);
		return okay;
	}

	public static boolean checkXorParams(final Term[][] xorArgs) {
		assert xorArgs.length == 3;
		final HashSet<Term> xorSum = new HashSet<>();
		for (final Term[] args : xorArgs) {
			for (final Term arg : args) {
				if (xorSum.contains(arg)) {
					xorSum.remove(arg);
				} else {
					xorSum.add(arg);
				}
			}
		}
		return xorSum.isEmpty();
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
		return isAxiom(proof) && ((AnnotatedTerm) proof).getAnnotations()[0].getKey().equals(":" + ORACLE);
	}

	public static boolean isProofRule(final String rule, final Term proof) {
		return proof instanceof ApplicationTerm
				&& ((ApplicationTerm) proof).getFunction().getName().equals(PREFIX + rule);
	}

	public static boolean isDefineFun(final Term proof) {
		return proof instanceof AnnotatedTerm
				&& ((AnnotatedTerm) proof).getAnnotations()[0].getKey() == ANNOT_DEFINE_FUN;
	}

	public static boolean isDeclareFun(final Term proof) {
		return proof instanceof AnnotatedTerm
				&& ((AnnotatedTerm) proof).getAnnotations()[0].getKey() == ANNOT_DECLARE_FUN;
	}

	public static boolean isProof(final Term proof) {
		return proof.getSort().isInternal() && proof.getSort().getName().equals(PREFIX + PROOF);
	}

	public static class PrintProof extends PrintTerm {
		@Override
		public void walkTerm(final Term proof) {
			if (proof instanceof AnnotatedTerm) {
				final AnnotatedTerm annotTerm = (AnnotatedTerm) proof;
				final Annotation[] annots = annotTerm.getAnnotations();
				if (annots.length == 1 && annots[0].getKey() == ANNOT_DEFINE_FUN) {
					final Object[] annotVal = (Object[]) annots[0].getValue();
					assert annotVal.length == 2;
					final FunctionSymbol func = (FunctionSymbol) annotVal[0];
					final LambdaTerm definition = (LambdaTerm) annotVal[1];
					mTodo.add(")");
					mTodo.add(annotTerm.getSubterm());
					mTodo.add(" ");
					mTodo.add(")");
					mTodo.add(definition.getSubterm());
					mTodo.add(") ");
					final TermVariable[] vars = definition.getVariables();
					for (int i = vars.length - 1; i >= 0; i--) {
						mTodo.add(")");
						mTodo.add(vars[i].getSort());
						mTodo.add(" ");
						mTodo.add(vars[i]);
						mTodo.add(i == 0 ? "(" : " (");
					}
					mTodo.add(" (");
					mTodo.add(func.getApplicationString());
					mTodo.add("((" + annots[0].getKey().substring(1) + " ");
					return;
				} else if (annots.length == 1 && annots[0].getKey() == ANNOT_DECLARE_FUN) {
					final Object[] annotVal = (Object[]) annots[0].getValue();
					assert annotVal.length == 1;
					final FunctionSymbol func = (FunctionSymbol) annotVal[0];
					mTodo.add(")");
					mTodo.add(annotTerm.getSubterm());
					mTodo.add(" ");
					mTodo.add(")");
					mTodo.add(func.getReturnSort());
					mTodo.add(") ");
					final Sort[] paramSorts = func.getParameterSorts();
					for (int i = paramSorts.length - 1; i >= 0; i--) {
						mTodo.add(paramSorts[i]);
						if (i > 0) {
							mTodo.add(" ");
						}
					}
					mTodo.add(" (");
					mTodo.add(func.getApplicationString());
					mTodo.add("((" + annots[0].getKey().substring(1) + " ");
					return;
				} else if (annotTerm.getSubterm() instanceof ApplicationTerm
						&& ((ApplicationTerm) annotTerm.getSubterm()).getFunction().getName() == PREFIX + AXIOM) {
					switch (annots[0].getKey()) {
					case ":" + ORACLE: {
						assert annots.length >= 1;
						final Object[] clause = (Object[]) annots[0].getValue();
						mTodo.add(")");
						for (int i = annots.length - 1; i >= 1; i--) {
							if (annots[i].getValue() != null) {
								mTodo.add(annots[i].getValue());
								mTodo.add(" ");
							}
							mTodo.add(annots[i].getKey());
							mTodo.add(" ");
						}
						mTodo.add(clause);
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}
					case ":" + TRUEI:
					case ":" + FALSEE: {
						assert annots.length == 1;
						assert annots[0].getValue() == null;
						mTodo.add(annots[0].getKey().substring(1));
						return;
					}
					case ":" + NOTI:
					case ":" + NOTE:
					case ":" + ORE:
					case ":" + ANDI:
					case ":" + IMPE:
					case ":" + IFFI1:
					case ":" + IFFI2:
					case ":" + IFFE1:
					case ":" + IFFE2:
					case ":" + ITE1:
					case ":" + ITE2:
					case ":" + EQI:
					case ":" + DISTINCTI: {
						assert annots.length == 1;
						final Term param = (Term) annots[0].getValue();
						mTodo.add(")");
						mTodo.add(param);
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}

					case ":" + REFL:
					case ":" + SYMM:
					case ":" + TRANS:
					case ":" + GTDEF:
					case ":" + GEQDEF:
					case ":" + TRICHOTOMY:
					case ":" + TOTAL:
					case ":" + POLYADD:
					case ":" + POLYMUL:
					case ":" + DIVIDEDEF:
					case ":" + MINUSDEF:
					case ":" + TOREALDEF:
					case ":" + TOINTLOW:
					case ":" + TOINTHIGH:
					case ":" + DIVLOW:
					case ":" + DIVHIGH:
					case ":" + MODDEF:
					case ":" + SELECTSTORE1:
					case ":" + SELECTSTORE2:
					case ":" + EXTDIFF:
					case ":" + CONST:
					case ":" + DT_PROJECT:
					case ":" + DT_CONS:
					case ":" + DT_TESTI:
					case ":" + DT_EXHAUST:
					case ":" + DT_MATCH: {
						assert annots.length == 1;
						final Term[] params = (Term[]) annots[0].getValue();
						mTodo.add(")");
						for (int i = params.length - 1; i >= 0; i--) {
							mTodo.add(params[i]);
							mTodo.add(" ");
						}
						mTodo.add("(" + annots[0].getKey().substring(1));
						return;
					}
					case ":" + ORI:
					case ":" + ANDE:
					case ":" + IMPI: {
						final Term param = (Term) annots[0].getValue();
						assert annots.length == 2;
						assert annots[1].getKey() == ANNOT_POS;
						mTodo.add(")");
						mTodo.add(param);
						mTodo.add(" ");
						mTodo.add(annots[1].getValue());
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}
					case ":" + EQE:
					case ":" + DISTINCTE: {
						final Term param = (Term) annots[0].getValue();
						assert annots.length == 2;
						assert annots[1].getKey() == ANNOT_POS;
						final Integer[] positions = (Integer[]) annots[1].getValue();
						mTodo.add(")");
						mTodo.add(param);
						mTodo.add(" ");
						mTodo.add(positions[0] + " " + positions[1]);
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}
					case ":" + CONG: {
						assert annots.length == 1;
						final Object[] congArgs = (Object[]) annots[0].getValue();
						assert congArgs.length == 3;
						final FunctionSymbol func = (FunctionSymbol) congArgs[0];
						final Term[] params1 = (Term[]) congArgs[1];
						final Term[] params2 = (Term[]) congArgs[2];
						mTodo.add("))");
						for (int i = params2.length - 1; i >= 0; i--) {
							mTodo.add(params2[i]);
							mTodo.add(" ");
						}
						mTodo.add(func.getApplicationString());
						mTodo.add(") (");
						for (int i = params1.length - 1; i >= 0; i--) {
							mTodo.add(params1[i]);
							mTodo.add(" ");
						}
						mTodo.add(func.getApplicationString());
						mTodo.add("(" + annots[0].getKey().substring(1) + " (");
						return;
					}
					case ":" + XORI:
					case ":" + XORE: {
						assert annots.length == 1;
						final Term[][] xorLists = (Term[][]) annots[0].getValue();
						assert xorLists.length == 3;
						mTodo.add(")");
						for (int i = 2; i >= 0; i--) {
							mTodo.add(")");
							for (int j = xorLists[i].length - 1; j >= 0; j--) {
								mTodo.add(xorLists[i][j]);
								if (j > 0) {
									mTodo.add(" ");
								}
							}
							mTodo.add(" (");
						}
						mTodo.add("(" + annots[0].getKey().substring(1));
						return;
					}
					case ":" + EXPAND: {
						assert annots.length == 1;
						final Object[] expandParams = (Object[]) annots[0].getValue();
						assert expandParams.length == 2;
						final FunctionSymbol func = (FunctionSymbol) expandParams[0];
						final Term[] params = (Term[]) expandParams[1];
						mTodo.add(")");
						if (params.length > 0) {
							mTodo.add(")");
							for (int i = params.length - 1; i >= 0; i--) {
								mTodo.add(params[i]);
								mTodo.add(" ");
							}
							mTodo.add(func.getApplicationString());
							mTodo.add("(");
						} else {
							mTodo.add(func.getApplicationString());
						}
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}
					case ":" + FORALLE:
					case ":" + EXISTSI: {
						assert annots.length == 2;
						final Term quant = (Term) annots[0].getValue();
						assert annots[1].getKey() == ANNOT_VALUES;
						final Term[] values = (Term[]) annots[1].getValue();
						mTodo.add(")");
						mTodo.add(quant);
						mTodo.add(") ");
						for (int i = values.length - 1; i >= 0; i--) {
							mTodo.add(values[i]);
							if (i > 0) {
								mTodo.add(" ");
							}
						}
						mTodo.add("(" + annots[0].getKey().substring(1) + " (");
						return;
					}
					case ":" + FORALLI:
					case ":" + EXISTSE: {
						assert annots.length == 1;
						final Term quant = (Term) annots[0].getValue();

						mTodo.add(")");
						mTodo.add(quant);
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}
					case ":" + DELANNOT: {
						mTodo.add("))");
						assert annots.length == 1;
						final Object[] params = (Object[]) annots[0].getValue();
						assert params.length == 2;
						final Term subterm = (Term) params[0];
						final Object[] subAnnots = (Object[]) params[1];
						for (int i = subAnnots.length - 1; i >= 0; i--) {
							mTodo.addLast(subAnnots[i]);
							mTodo.addLast(" ");
						}
						mTodo.addLast(subterm);
						mTodo.add("(" + DELANNOT + " (! ");
						return;
					}
					case ":" + DIVISIBLEDEF: {
						assert annots.length == 2;
						final Term[] params = (Term[]) annots[0].getValue();
						assert params.length == 1;
						assert annots[1].getKey() == ANNOT_DIVISOR;
						mTodo.add(")");
						mTodo.add(annots[1].getValue());
						mTodo.add(" ");
						for (int i = params.length - 1; i >= 0; i--) {
							mTodo.add(params[i]);
							mTodo.add(" ");
						}
						mTodo.add("(" + annots[0].getKey().substring(1));
						return;
					}
					case ":" + TOTALINT: {
						final Object[] params = (Object[]) annots[0].getValue();
						final BigInteger c = (BigInteger) params[1];
						final Term x = (Term) params[0];
						assert annots.length == 1;
						mTodo.add(")");
						if (c.signum() < 0) {
							mTodo.add("(- " + c.abs().toString() + ")");
						} else {
							mTodo.add(c);
						}
						mTodo.add(" ");
						mTodo.add(x);
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}
					case ":" + FARKAS: {
						final Term[] params = (Term[]) annots[0].getValue();
						assert annots.length == 2;
						assert annots[1].getKey() == ANNOT_COEFFS;
						final BigInteger[] coeffs = (BigInteger[]) annots[1].getValue();
						assert params.length == coeffs.length;
						mTodo.add(")");
						for (int i = params.length - 1; i >= 0; i--) {
							mTodo.add(params[i]);
							mTodo.add(" ");
							mTodo.add(coeffs[i]);
							mTodo.add(" ");
						}
						mTodo.add("(" + annots[0].getKey().substring(1));
						return;
					}
					case ":" + DT_TESTE: {
						assert annots.length == 1;
						final Object[] params = (Object[]) annots[0].getValue();
						assert params.length == 2;
						mTodo.add(")");
						mTodo.add(params[1]);
						mTodo.add(" ");
						mTodo.add(params[0]);
						mTodo.add("(" + DT_TESTE + " ");
						return;
					}
					case ":" + DT_ACYCLIC: {
						assert annots.length == 1;
						final Object[] params = (Object[]) annots[0].getValue();
						assert params.length == 2;
						final int[] positions = (int[]) params[1];
						assert positions.length > 0;
						mTodo.add("))");
						for (int i = positions.length - 1; i >= 1; i--) {
							mTodo.add(" " + positions[i]);
						}
						mTodo.add(" (" + positions[0]);
						mTodo.add(params[0]);
						mTodo.add("(" + DT_ACYCLIC + " ");
						return;
					}
					}
				}
			}

			if (proof instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) proof;
				final Term[] params = appTerm.getParameters();
				switch (appTerm.getFunction().getName()) {
				case PREFIX + RES: {
					assert params.length == 3;
					mTodo.add(")");
					for (int i = params.length - 1; i >= 0; i--) {
						mTodo.add(params[i]);
						mTodo.add(" ");
					}
					mTodo.add("(" + RES);
					return;
				}
				case PREFIX + CHOOSE: {
					assert params.length == 1;
					final LambdaTerm lambda = (LambdaTerm) params[0];
					assert lambda.getVariables().length == 1;
					mTodo.add(")");
					mTodo.add(lambda.getSubterm());
					mTodo.add(") ");
					mTodo.add(lambda.getVariables()[0].getSort());
					mTodo.add(" ");
					mTodo.add(lambda.getVariables()[0]);
					mTodo.add("(" + CHOOSE + " (");
					return;
				}
				case PREFIX + ASSUME: {
					assert params.length == 1;
					mTodo.add(")");
					mTodo.add(params[0]);
					mTodo.add("(" + ASSUME + " ");
					return;
				}
				default:
					break;
				}
			}

			if (proof instanceof LetTerm) {
				final LetTerm let = (LetTerm) proof;
				final TermVariable[] vars = let.getVariables();
				final Term[] values = let.getValues();
				boolean hasLetProof = false;
				boolean hasLetTerm = false;
				for (int i = 0; i < vars.length; i++) {
					if (isProof(values[i])) {
						hasLetProof = true;
					} else {
						hasLetTerm = true;
					}
				}
				// close parentheses
				if (hasLetTerm) {
					mTodo.addLast(")");
				}
				if (hasLetProof) {
					mTodo.addLast(")");
				}
				// Add subterm to stack.
				mTodo.addLast(let.getSubTerm());
				// add the let-proof for proof variables.
				if (hasLetProof) {
					// Add subterm to stack.
					// Add assigned values to stack
					String sep = ")) ";
					for (int i = values.length - 1; i >= 0; i--) {
						if (isProof(values[i])) {
							mTodo.addLast(sep);
							mTodo.addLast(values[i]);
							mTodo.addLast("(" + vars[i].toString() + " ");
							sep = ") ";
						}
					}
					mTodo.addLast("(let-proof (");
				}
				// add the let for non-proof variables.
				if (hasLetTerm) {
					// Add assigned values to stack
					String sep = ")) ";
					for (int i = values.length - 1; i >= 0; i--) {
						if (!isProof(values[i])) {
							mTodo.addLast(sep);
							mTodo.addLast(values[i]);
							mTodo.addLast("(" + vars[i].toString() + " ");
							sep = ") ";
						}
					}
					mTodo.addLast("(let (");
				}
				return;
			}
			super.walkTerm(proof);
		}
	}
}
