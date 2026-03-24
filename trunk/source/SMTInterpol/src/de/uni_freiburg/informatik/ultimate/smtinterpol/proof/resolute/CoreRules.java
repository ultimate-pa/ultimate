/*
 * Copyright (C) 2026 University of Freiburg
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

import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.AND;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BOOL;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.DISTINCT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EQUALS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.FALSE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.IMPLIES;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.ITE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.NOT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.OR;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.TRUE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.XOR;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Proof rules for the core theory.
 */
public class CoreRules {

	public static void registerRules(MinimalProofChecker checker) {
		checker.registerAxiom(ProofRules.TRUEI, CoreRules::trueI);
		checker.registerAxiom(ProofRules.FALSEE, CoreRules::falseE);
		checker.registerAxiom(ProofRules.NOTI, CoreRules::notI);
		checker.registerAxiom(ProofRules.NOTE, CoreRules::notE);
		checker.registerAxiom(ProofRules.ORI, CoreRules::orI);
		checker.registerAxiom(ProofRules.ORE, CoreRules::orE);
		checker.registerAxiom(ProofRules.ANDI, CoreRules::andI);
		checker.registerAxiom(ProofRules.ANDE, CoreRules::andE);
		checker.registerAxiom(ProofRules.IMPI, CoreRules::impI);
		checker.registerAxiom(ProofRules.IMPE, CoreRules::impE);
		checker.registerAxiom(ProofRules.IFFI1, CoreRules::iffI1);
		checker.registerAxiom(ProofRules.IFFI2, CoreRules::iffI2);
		checker.registerAxiom(ProofRules.IFFE1, CoreRules::iffE1);
		checker.registerAxiom(ProofRules.IFFE2, CoreRules::iffE2);
		checker.registerAxiom(ProofRules.XORI, CoreRules::xorI);
		checker.registerAxiom(ProofRules.XORE, CoreRules::xorE);
		checker.registerAxiom(ProofRules.EQI, CoreRules::eqI);
		checker.registerAxiom(ProofRules.EQE, CoreRules::eqE);
		checker.registerAxiom(ProofRules.DISTINCTI, CoreRules::distinctI);
		checker.registerAxiom(ProofRules.DISTINCTE, CoreRules::distinctE);
		checker.registerAxiom(ProofRules.ITE1, CoreRules::ite1);
		checker.registerAxiom(ProofRules.ITE2, CoreRules::ite2);
		checker.registerAxiom(ProofRules.DELANNOT, CoreRules::delAnnot);
		checker.registerAxiom(ProofRules.REFL, CoreRules::refl);
		checker.registerAxiom(ProofRules.SYMM, CoreRules::symm);
		checker.registerAxiom(ProofRules.TRANS, CoreRules::trans);
		checker.registerAxiom(ProofRules.CONG, CoreRules::cong);
		checker.registerAxiom(ProofRules.EXPAND, CoreRules::expand);
		checker.registerAxiom(ProofRules.FORALLI, CoreRules::forallI);
		checker.registerAxiom(ProofRules.FORALLE, CoreRules::forallE);
		checker.registerAxiom(ProofRules.EXISTSI, CoreRules::existsI);
		checker.registerAxiom(ProofRules.EXISTSE, CoreRules::existsE);
	}

	public static ProofLiteral[] trueI(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 0;
		return new ProofLiteral[] { new ProofLiteral(theory.term(TRUE), true) };
	}

	public static ProofLiteral[] falseE(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 0;
		return new ProofLiteral[] { new ProofLiteral(theory.term(FALSE), false) };
	}

	public static ProofLiteral[] notI(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 1;
		final ApplicationTerm notTerm = (ApplicationTerm) params[0];
		if (!ProofRules.isApplication(NOT, notTerm)) {
			throw new IllegalArgumentException("not+ requires not");
		}
		// (not t), t
		return new ProofLiteral[] { new ProofLiteral(notTerm, true),
				new ProofLiteral(notTerm.getParameters()[0], true) };
	}

	public static ProofLiteral[] notE(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 1;
		final ApplicationTerm notTerm = (ApplicationTerm) params[0];
		if (!ProofRules.isApplication(NOT, notTerm)) {
			throw new IllegalArgumentException("not- requires not");
		}
		// ~(not t), ~t
		return new ProofLiteral[] { new ProofLiteral(notTerm, false),
				new ProofLiteral(notTerm.getParameters()[0], false) };
	}

	public static ProofLiteral[] orI(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 2;
		final ApplicationTerm orTerm = (ApplicationTerm) params[1];
		if (!ProofRules.isApplication(OR, orTerm)) {
			throw new IllegalArgumentException("or+ requires or");
		}
		final Term[] orParams = orTerm.getParameters();
		final int pos = (Integer) params[0];
		assert pos >= 0 && pos < orParams.length;

		// (or t1 ... tn), ~tpos
		return new ProofLiteral[] { new ProofLiteral(orTerm, true), new ProofLiteral(orParams[pos], false) };
	}

	public static ProofLiteral[] orE(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm orTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(OR, orTerm)) {
			throw new IllegalArgumentException("or- requires or");
		}
		final Term[] orParams = orTerm.getParameters();

		// ~(or t1 ... tn), t1, ..., tn
		final HashSet<ProofLiteral> clause = new LinkedHashSet<>();
		clause.add(new ProofLiteral(orTerm, false));
		for (final Term param : orParams) {
			clause.add(new ProofLiteral(param, true));
		}
		return clause.toArray(new ProofLiteral[clause.size()]);
	}

	public static ProofLiteral[] andI(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm andTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(AND, andTerm)) {
			throw new IllegalArgumentException("and+ requires and");
		}
		final Term[] params = andTerm.getParameters();

		// (and t1 ... tn), ~t1, ..., ~tn
		final HashSet<ProofLiteral> clause = new LinkedHashSet<>();
		clause.add(new ProofLiteral(andTerm, true));
		for (final Term param : params) {
			clause.add(new ProofLiteral(param, false));
		}
		return clause.toArray(new ProofLiteral[clause.size()]);
	}

	public static ProofLiteral[] andE(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 2;
		final ApplicationTerm andTerm = (ApplicationTerm) ruleParams[1];
		if (!ProofRules.isApplication(AND, andTerm)) {
			throw new IllegalArgumentException("and- requires and");
		}
		final Term[] params = andTerm.getParameters();
		final int pos = (Integer) ruleParams[0];
		assert pos >= 0 && pos < params.length;

		// ~(and t1 ... tn), tpos
		return new ProofLiteral[] { new ProofLiteral(andTerm, false), new ProofLiteral(params[pos], true) };
	}

	public static ProofLiteral[] impI(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 2;
		final ApplicationTerm impTerm = (ApplicationTerm) ruleParams[1];
		if (!ProofRules.isApplication(IMPLIES, impTerm)) {
			throw new IllegalArgumentException("=>+ requires =>");
		}
		final Term[] params = impTerm.getParameters();
		final int pos = (Integer) ruleParams[0];
		assert pos >= 0 && pos < params.length;

		// (=> t1 ... tn), tpos (~tpos if pos == n)
		return new ProofLiteral[] { new ProofLiteral(impTerm, true),
				new ProofLiteral(params[pos], pos < params.length - 1) };
	}

	public static ProofLiteral[] impE(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm impTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(IMPLIES, impTerm)) {
			throw new IllegalArgumentException("=>- requires =>");
		}
		final Term[] params = impTerm.getParameters();

		// ~(=> t1 ... tn), ~t1, ..., ~tn-1, tn
		final HashSet<ProofLiteral> clause = new LinkedHashSet<>();
		clause.add(new ProofLiteral(impTerm, false));
		for (int i = 0; i < params.length; i++) {
			clause.add(new ProofLiteral(params[i], i == params.length - 1));
		}
		return clause.toArray(new ProofLiteral[clause.size()]);
	}

	public static ProofLiteral[] iffI1(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm iffTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(EQUALS, iffTerm)) {
			throw new IllegalArgumentException("=+ requires =");
		}
		final Term[] params = iffTerm.getParameters();
		if (params.length != 2 || params[0].getSort().getName() != BOOL) {
			throw new IllegalArgumentException("bool arguments expected");
		}

		// (= t1 t2), t1, t2
		return new ProofLiteral[] { new ProofLiteral(iffTerm, true), new ProofLiteral(params[0], true),
				new ProofLiteral(params[1], true) };
	}

	public static ProofLiteral[] iffI2(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm iffTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(EQUALS, iffTerm)) {
			throw new IllegalArgumentException("=+ requires =");
		}
		final Term[] params = iffTerm.getParameters();
		if (params.length != 2 || params[0].getSort().getName() != BOOL) {
			throw new IllegalArgumentException("bool arguments expected");
		}

		// (= t1 t2), ~t1, ~t2
		return new ProofLiteral[] { new ProofLiteral(iffTerm, true), new ProofLiteral(params[0], false),
				new ProofLiteral(params[1], false) };
	}

	public static ProofLiteral[] iffE1(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm iffTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(EQUALS, iffTerm)) {
			throw new IllegalArgumentException("=- requires =");
		}
		final Term[] params = iffTerm.getParameters();
		if (params.length != 2 || params[0].getSort().getName() != BOOL) {
			throw new IllegalArgumentException("bool arguments expected");
		}

		// ~(= t1 t2), t1, ~t2
		return new ProofLiteral[] { new ProofLiteral(iffTerm, false), new ProofLiteral(params[0], true),
				new ProofLiteral(params[1], false) };
	}

	public static ProofLiteral[] iffE2(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm iffTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(EQUALS, iffTerm)) {
			throw new IllegalArgumentException("=- requires =");
		}
		final Term[] params = iffTerm.getParameters();
		if (params.length != 2 || params[0].getSort().getName() != BOOL) {
			throw new IllegalArgumentException("bool arguments expected");
		}

		// ~(= t1 t2), ~t1, t2
		return new ProofLiteral[] { new ProofLiteral(iffTerm, false), new ProofLiteral(params[0], false),
				new ProofLiteral(params[1], true) };
	}

	public static ProofLiteral[] xorI(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		return xorAxiom(true, theory, (Term[][]) ruleParams);
	}

	public static ProofLiteral[] xorE(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		return xorAxiom(false, theory, (Term[][]) ruleParams);
	}

	public static ProofLiteral[] eqI(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm eqTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(EQUALS, eqTerm)) {
			throw new IllegalArgumentException("=+ requires =");
		}
		final Term[] params = eqTerm.getParameters();

		// (= t1 ... tn), ~(= t1 t2), ~(tn-1 tn)
		final ProofLiteral[] clause = new ProofLiteral[params.length];
		clause[0] = new ProofLiteral(eqTerm, true);
		for (int i = 0; i < params.length - 1; i++) {
			clause[i + 1] = new ProofLiteral(theory.term(EQUALS, params[i], params[i + 1]), false);
		}
		return clause;
	}

	public static ProofLiteral[] eqE(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 3;
		final ApplicationTerm eqTerm = (ApplicationTerm) ruleParams[2];
		if (!ProofRules.isApplication(EQUALS, eqTerm)) {
			throw new IllegalArgumentException("=- requires =");
		}
		final Term[] params = eqTerm.getParameters();
		final int pos0 = (Integer) ruleParams[0];
		final int pos1 = (Integer) ruleParams[1];
		assert 0 <= pos0 && pos0 < params.length && 0 <= pos1 && pos1 < params.length;

		// ~(= t1 ... tn), (= ti tj)
		return new ProofLiteral[] { new ProofLiteral(eqTerm, false),
				new ProofLiteral(theory.term(EQUALS, params[pos0], params[pos1]), true) };
	}

	public static ProofLiteral[] distinctI(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm distinctTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(DISTINCT, distinctTerm)) {
			throw new IllegalArgumentException("distinct+ requires distinct");
		}
		final Term[] params = distinctTerm.getParameters();
		final int len = params.length;

		// (distinct t1 ... tn), (= t1 t2),...
		final ProofLiteral[] clause = new ProofLiteral[1 + len * (len - 1) / 2];
		clause[0] = new ProofLiteral(distinctTerm, true);
		int pos = 1;
		for (int i = 0; i < len - 1; i++) {
			for (int j = i + 1; j < len; j++) {
				clause[pos++] = new ProofLiteral(theory.term(EQUALS, params[i], params[j]), true);
			}
		}
		assert pos == clause.length;
		return clause;
	}

	public static ProofLiteral[] distinctE(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 3;
		final ApplicationTerm distinctTerm = (ApplicationTerm) ruleParams[2];
		if (!ProofRules.isApplication(DISTINCT, distinctTerm)) {
			throw new IllegalArgumentException("distinct- requires distinct");
		}
		final Term[] params = distinctTerm.getParameters();
		final int pos0 = (Integer) ruleParams[0];
		final int pos1 = (Integer) ruleParams[1];
		assert 0 <= pos0 && pos0 < params.length && 0 <= pos1 && pos1 < params.length;

		// ~(distinct t1 ... tn), ~(= ti tj)
		return new ProofLiteral[] { new ProofLiteral(distinctTerm, false),
				new ProofLiteral(theory.term(EQUALS, params[pos0], params[pos1]), false) };
	}

	public static ProofLiteral[] ite1(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm iteTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(ITE, iteTerm)) {
			throw new IllegalArgumentException("ite1 requires ite");
		}
		final Term[] params = iteTerm.getParameters();
		assert params.length == 3;

		// (= (ite c t e) t), ~c
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, iteTerm, params[1]), true),
				new ProofLiteral(params[0], false) };
	}

	public static ProofLiteral[] ite2(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm iteTerm = (ApplicationTerm) ruleParams[0];
		if (!ProofRules.isApplication(ITE, iteTerm)) {
			throw new IllegalArgumentException("ite2 requires ite");
		}
		final Term[] params = iteTerm.getParameters();
		assert params.length == 3;

		// (= (ite c t e) e), c
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, iteTerm, params[2]), true),
				new ProofLiteral(params[0], true) };
	}

	public static ProofLiteral[] delAnnot(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		if (!(ruleParams[0] instanceof AnnotatedTerm)) {
			throw new IllegalArgumentException("delAnnot requires annotated term");
		}
		final AnnotatedTerm annotTerm = (AnnotatedTerm) ruleParams[0];
		final Term subterm = annotTerm.getSubterm();

		// (= (! t :...) t)
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, annotTerm, subterm), true) };
	}

	public static ProofLiteral[] refl(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final Term a = (Term) ruleParams[0];

		// (= a a)
		return new ProofLiteral[] {
				new ProofLiteral(theory.term(EQUALS, a, a), true) };
	}

	public static ProofLiteral[] symm(MinimalProofChecker checker, Theory theory, Object[] params) {
		final Term[] ruleParams = (Term[]) params;
		assert ruleParams.length == 2;

		// (= a0 a1), ~(= a1 a0)
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, ruleParams), true),
				new ProofLiteral(theory.term(EQUALS, ruleParams[1], ruleParams[0]), false) };
	}

	public static ProofLiteral[] trans(MinimalProofChecker checker, Theory theory, Object[] params) {
		final Term[] ruleParams = (Term[]) params;
		assert ruleParams.length > 2;
		final int len = ruleParams.length;

		// (= a0 alen-1), ~(= a0 a1), ..., ~(= alen-2 alen-1)
		final ProofLiteral[] clause = new ProofLiteral[len];
		clause[0] = new ProofLiteral(theory.term(EQUALS, ruleParams[0], ruleParams[len - 1]), true);
		for (int i = 0; i < len - 1; i++) {
			clause[i + 1] = new ProofLiteral(theory.term(EQUALS, ruleParams[i], ruleParams[i + 1]),
					false);
		}
		return clause;
	}

	public static ProofLiteral[] cong(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		final Term[] congArgs = (Term[]) ruleParams;
		assert congArgs.length == 2;
		final FunctionSplit split0 = splitApplication(congArgs[0]);
		final FunctionSplit split1 = splitApplication(congArgs[1]);
		if (split0 == null || split1 == null || split0.mFunc != split1.mFunc
				|| split0.mParams.length != split1.mParams.length) {
			throw new IllegalArgumentException("malformed congruence");
		}
		final FunctionSymbol func = split0.mFunc;
		final int paramCount = split0.mParams.length;
		final Term app0 = theory.term(func, split0.mParams);
		final Term app1 = theory.term(func, split1.mParams);

		// (= (f a0...an) (f b0... bn)), ~(= a0 b0), ..., ~(= an bn)
		final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>();
		clause.add(new ProofLiteral(theory.term(EQUALS, app0, app1), true));
		for (int i = 0; i < paramCount; i++) {
			clause.add(new ProofLiteral(theory.term(EQUALS, split0.mParams[i], split1.mParams[i]), false));
		}
		return clause.toArray(new ProofLiteral[clause.size()]);
	}

	public static ProofLiteral[] expand(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final ApplicationTerm app = (ApplicationTerm) ruleParams[0];
		final FunctionSymbol func = app.getFunction();
		final Term[] params = app.getParameters();
		Term rhs;
		if (func.isLeftAssoc() && params.length > 2) {
			rhs = params[0];
			for (int i = 1; i < params.length; i++) {
				rhs = theory.term(func, rhs, params[i]);
			}
		} else if (func.isRightAssoc() && params.length > 2) {
			rhs = params[params.length - 1];
			for (int i = params.length - 2; i >= 0; i--) {
				rhs = theory.term(func, params[i], rhs);
			}
		} else if (func.isChainable() && params.length > 2) {
			final Term[] chain = new Term[params.length - 1];
			for (int i = 0; i < chain.length; i++) {
				chain[i] = theory.term(func, params[i], params[i + 1]);
			}
			rhs = theory.term("and", chain);
		} else {
			rhs = checker.expandFunctionSymbol(func, params);
		}
		return new ProofLiteral[] { new ProofLiteral(theory.term("=", app, rhs), true) };
	}

	public static ProofLiteral[] forallI(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final QuantifiedFormula quant = (QuantifiedFormula) ruleParams[0];
		if (quant.getQuantifier() != QuantifiedFormula.FORALL) {
			throw new IllegalArgumentException("forall quantifier expected");
		}
		return skolemQuant(true, quant);
	}

	public static ProofLiteral[] forallE(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 2;
		final QuantifiedFormula quant = (QuantifiedFormula) ruleParams[1];
		if (quant.getQuantifier() != QuantifiedFormula.FORALL) {
			throw new IllegalArgumentException("forall quantifier expected");
		}
		return instantiateQuant(true, (Term[]) ruleParams[0], quant);
	}

	public static ProofLiteral[] existsI(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 2;
		final QuantifiedFormula quant = (QuantifiedFormula) ruleParams[1];
		if (quant.getQuantifier() != QuantifiedFormula.EXISTS) {
			throw new IllegalArgumentException("exists quantifier expected");
		}
		return instantiateQuant(false, (Term[]) ruleParams[0], quant);
	}

	public static ProofLiteral[] existsE(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		assert ruleParams.length == 1;
		final QuantifiedFormula quant = (QuantifiedFormula) ruleParams[0];
		if (quant.getQuantifier() != QuantifiedFormula.EXISTS) {
			throw new IllegalArgumentException("exists quantifier expected");
		}
		return skolemQuant(false, quant);
	}

	private static ProofLiteral[] xorAxiom(boolean isIntro, Theory theory, Term[][] xorLists) {
		if (!checkXorParams(xorLists)) {
			throw new IllegalArgumentException("xor side condition violated");
		}
		// intro: (xor set0), (xor set1), ~(xor set2)
		// elim: ~(xor set0), ~(xor set1), ~(xor set2)
		final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>();
		for (int i = 0; i < 3; i++) {
			final Term term = xorLists[i].length == 1 ? xorLists[i][0] : theory.term(XOR, xorLists[i]);
			assert term != null;
			clause.add(new ProofLiteral(term, isIntro && i < 2));
		}
		return clause.toArray(new ProofLiteral[clause.size()]);
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

	/**
	 * Split an application term into function symbol and parameters. This also
	 * supports splitting integer and rational constants like {@code (/ 3.0 5.0)} or
	 * {@code (- 5)}.
	 *
	 * @param term The term to split.
	 * @return The function symbol and the paramters.
	 */
	private static FunctionSplit splitApplication(Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm app = (ApplicationTerm) term;
			return new FunctionSplit(app.getFunction(), app.getParameters());
		} else if (term instanceof ConstantTerm) {
			final Theory t = term.getTheory();
			final Sort sort = term.getSort();
			final Object value = ((ConstantTerm) term).getValue();
			if (value instanceof Rational) {
				final Rational rat = (Rational) value;
				if (!rat.isIntegral()) {
					final FunctionSymbol fsym = t.getFunctionWithResult(SMTLIBConstants.DIVIDE, null, null,
							new Sort[] { sort, sort });
					final Term[] params = new Term[2];
					params[0] = Rational.valueOf(rat.numerator(), BigInteger.ONE).toTerm(sort);
					params[1] = Rational.valueOf(rat.denominator(), BigInteger.ONE).toTerm(sort);
					assert term == t.term(fsym, params);
					return new FunctionSplit(fsym, params);
				} else if (rat.signum() < 0) {
					final FunctionSymbol fsym = t.getFunctionWithResult(SMTLIBConstants.MINUS, null, null,
							new Sort[] { sort });
					final Term[] params = new Term[1];
					params[0] = rat.negate().toTerm(sort);
					assert term == t.term(fsym, params);
					return new FunctionSplit(fsym, params);
				}
			} else if (value instanceof BigInteger) {
				final BigInteger bigInt = (BigInteger) value;
				if (bigInt.signum() < 0) {
					final FunctionSymbol fsym = t.getFunctionWithResult(SMTLIBConstants.MINUS, null, null,
							new Sort[] { sort });
					final Term[] params = new Term[1];
					params[0] = t.constant(bigInt.negate(), sort);
					assert term == t.term(fsym, params);
					return new FunctionSplit(fsym, params);
				}
			}
		}
		return null;
	}


	private static ProofLiteral[] skolemQuant(boolean isForall, QuantifiedFormula quant) {
		final Theory theory = quant.getTheory();
		final TermVariable[] termVars = quant.getVariables();
		final Term[] skolemTerms = new ProofRules(theory).getSkolemVars(termVars, quant.getSubformula(), isForall);
		final Term letted = theory.let(termVars, skolemTerms, quant.getSubformula());

		// (forall (vars) F), ~(let skolem F)
		// ~(exists (vars) F), (let skolem F)
		return new ProofLiteral[] { new ProofLiteral(quant, isForall),
				new ProofLiteral(new FormulaUnLet().unlet(letted), !isForall) };
	}

	private static ProofLiteral[] instantiateQuant(boolean isForall, Term[] values, QuantifiedFormula quant) {
		final Theory theory = quant.getTheory();
		final TermVariable[] termVars = quant.getVariables();
		final Term letted = theory.let(termVars, values, quant.getSubformula());

		// ~(forall (vars) F), (let values F)
		// (exists (vars) F), ~(let values F)
		return new ProofLiteral[] { new ProofLiteral(quant, !isForall),
				new ProofLiteral(new FormulaUnLet().unlet(letted), isForall) };
	}

	static class FunctionSplit {
		final FunctionSymbol mFunc;
		final Term[] mParams;

		public FunctionSplit(FunctionSymbol func, Term[] params) {
			mFunc = func;
			mParams = params;
		}
	}
}
