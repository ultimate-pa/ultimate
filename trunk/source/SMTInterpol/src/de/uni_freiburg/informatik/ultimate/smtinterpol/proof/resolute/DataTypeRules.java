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
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EQUALS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.IS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.ITE;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Proof rules for the datatype theory.
 */
public class DataTypeRules {

	public static void registerRules(MinimalProofChecker checker) {
		checker.registerAxiom(ProofRules.DT_PROJECT, DataTypeRules::dtProject);
		checker.registerAxiom(ProofRules.DT_CONS, DataTypeRules::dtCons);
		checker.registerAxiom(ProofRules.DT_TESTI, DataTypeRules::dtTestI);
		checker.registerAxiom(ProofRules.DT_TESTE, DataTypeRules::dtTestE);
		checker.registerAxiom(ProofRules.DT_EXHAUST, DataTypeRules::dtExhaust);
		checker.registerAxiom(ProofRules.DT_ACYCLIC, DataTypeRules::dtAcyclic);
		checker.registerAxiom(ProofRules.DT_MATCH, DataTypeRules::dtMatch);
	}

	public static ProofLiteral[] dtProject(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 1;
		final ApplicationTerm selConsTerm = (ApplicationTerm) params[0];
		final FunctionSymbol selector = selConsTerm.getFunction();
		assert selector.isSelector();
		final ApplicationTerm consTerm = (ApplicationTerm) selConsTerm.getParameters()[0];
		if (!consTerm.getFunction().isConstructor()) {
			throw new IllegalArgumentException("side condition violated");
		}
		final DataType dataType = (DataType) consTerm.getSort().getSortSymbol();
		final Constructor cons = dataType.getConstructor(consTerm.getFunction().getName());
		final int selectPos = cons.getSelectorIndex(selector.getName());
		final Term consArg = consTerm.getParameters()[selectPos];

		// + (= (seli (cons a1 ... an)) ai)
		final Term provedEq = theory.term(EQUALS, selConsTerm, consArg);
		return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
	}

	public static ProofLiteral[] dtCons(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 1;
		final ApplicationTerm isConsTerm = (ApplicationTerm) params[0];
		if (!isConsTerm.getFunction().getName().equals(IS)) {
			throw new IllegalArgumentException("side condition violated");
		}
		final Term dataTerm = isConsTerm.getParameters()[0];
		final DataType dataType = (DataType) dataTerm.getSort().getSortSymbol();
		final Constructor cons = dataType.getConstructor(isConsTerm.getFunction().getIndices()[0]);
		final String[] selectors = cons.getSelectors();
		final Term[] selectTerms = new Term[selectors.length];
		for (int i = 0; i < selectors.length; i++) {
			selectTerms[i] = theory.term(selectors[i], dataTerm);
		}
		final Term consTerm = theory.term(cons.getName(), null,
				(cons.needsReturnOverload() ? dataTerm.getSort() : null), selectTerms);

		// - ((_ is cons) u), + (= (cons (sel1 u) ... (seln u)) u)
		final Term provedEq = theory.term(EQUALS, consTerm, dataTerm);
		return new ProofLiteral[] { new ProofLiteral(isConsTerm, false), new ProofLiteral(provedEq, true) };
	}

	public static ProofLiteral[] dtTestI(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 1;
		final ApplicationTerm consTerm = (ApplicationTerm) params[0];
		final FunctionSymbol consFunc = consTerm.getFunction();
		if (!consFunc.isConstructor()) {
			throw new IllegalArgumentException("side condition violated");
		}
		final Term isTerm = theory.term(IS, new String[] { consFunc.getName() }, null, consTerm);

		// + ((_ is cons) (cons a1 ... an))
		return new ProofLiteral[] { new ProofLiteral(isTerm, true) };
	}

	public static ProofLiteral[] dtTestE(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 2;
		final String otherCons = (String) params[0];
		final ApplicationTerm consTerm = (ApplicationTerm) params[1];
		final FunctionSymbol consFunc = consTerm.getFunction();
		if (!consFunc.isConstructor() || consFunc.getName().equals(otherCons)) {
			throw new IllegalArgumentException("side condition violated");
		}
		final Term isTerm = theory.term(IS, new String[] { otherCons }, null, consTerm);

		// + ((_ is otherCons) (cons a1 ... an))
		return new ProofLiteral[] { new ProofLiteral(isTerm, false) };
	}

	public static ProofLiteral[] dtExhaust(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 1;
		final Term data = (Term) params[0];
		final DataType dataType = (DataType) data.getSort().getSortSymbol();
		final Constructor[] constrs = dataType.getConstructors();
		// + ((_ is cons0) data) ... + ((_ is consn) data)
		final ProofLiteral[] lits = new ProofLiteral[constrs.length];
		for (int i = 0; i < lits.length; i++) {
			final Term tester = theory.term(IS, new String[] { constrs[i].getName() }, null, data);
			lits[i] = new ProofLiteral(tester, true);
		}
		return lits;
	}

	public static ProofLiteral[] dtAcyclic(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 2;
		final Term consTerm = (Term) params[0];
		final int[] positions = (int[]) params[1];
		if (positions.length == 0) {
			throw new IllegalArgumentException("side condition violated");
		}
		Term subTerm = consTerm;
		for (final int pos : positions) {
			final ApplicationTerm parent = (ApplicationTerm) subTerm;
			if (!parent.getFunction().isConstructor()) {
				throw new IllegalArgumentException("side condition violated");
			}
			subTerm = parent.getParameters()[pos];
		}
		final Term provedIneq = theory.term(EQUALS, consTerm, subTerm);
		return new ProofLiteral[] { new ProofLiteral(provedIneq, false) };
	}

	public static ProofLiteral[] dtMatch(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 1;
		if (!(params[0] instanceof MatchTerm)) {
			throw new IllegalArgumentException("match term expected");
		}
		final MatchTerm matchTerm = (MatchTerm) params[0];
		final Term iteTerm = buildIteForMatch(matchTerm);

		final Term provedEq = theory.term(EQUALS, matchTerm, iteTerm);
		return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
	}

	private static Term buildLetForMatch(final Constructor constr, final TermVariable[] vars, final Term dataTerm,
			final Term caseTerm) {
		final Theory theory = dataTerm.getTheory();
		final Term[] selectTerms = new Term[vars.length];
		if (constr == null) {
			assert vars.length == 1;
			selectTerms[0] = dataTerm;
		} else {
			assert constr.getSelectors().length == vars.length;
			for (int i = 0; i < vars.length; i++) {
				selectTerms[i] = theory.term(constr.getSelectors()[i], dataTerm);
			}
		}
		return new FormulaUnLet().unlet(theory.let(vars, selectTerms, caseTerm));
	}

	public static Term buildIteForMatch(final MatchTerm matchTerm) {
		final Theory theory = matchTerm.getTheory();
		final Term dataTerm = matchTerm.getDataTerm();
		final Term[] cases = matchTerm.getCases();
		final TermVariable[][] vars = matchTerm.getVariables();
		final Constructor[] constrs = matchTerm.getConstructors();

		Term iteTerm;
		iteTerm = buildLetForMatch(constrs[constrs.length - 1], vars[constrs.length - 1], dataTerm,
				cases[constrs.length - 1]);
		for (int i = constrs.length - 2; i >= 0; i--) {
			final Term caseTerm = buildLetForMatch(constrs[i], vars[i], dataTerm, cases[i]);
			if (constrs[i] == null) {
				// SMT-LIB standard allows the default case in the middle, with the semantics
				// that all following cases are redundant.
				iteTerm = caseTerm;
			} else {
				final Term condTerm = theory.term(IS, new String[] { constrs[i].getName() }, null,
						dataTerm);
				iteTerm = theory.term(ITE, condTerm, caseTerm, iteTerm);
			}
		}
		return iteTerm;
	}
}
