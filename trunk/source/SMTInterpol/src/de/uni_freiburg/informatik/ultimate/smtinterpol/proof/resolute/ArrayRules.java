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
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.ARRAY;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.CONST;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EQUALS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.SELECT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.STORE;
import static de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants.DIFF;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Proof rules for the array theory.
 */
public class ArrayRules {

	public static void registerRules(MinimalProofChecker checker) {
		checker.registerAxiom(ProofRules.SELECTSTORE1, ArrayRules::selectStore1);
		checker.registerAxiom(ProofRules.SELECTSTORE2, ArrayRules::selectStore2);
		checker.registerAxiom(ProofRules.EXTDIFF, ArrayRules::extDiff);
		checker.registerAxiom(ProofRules.CONST, ArrayRules::constAxiom);
	}

	public static ProofLiteral[] selectStore1(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		final Term[] params = (Term[]) ruleParams;
		assert params.length == 3;

		// (= (select (store a i v) i) v)
		final Term store = theory.term(STORE, params[0], params[1], params[2]);
		final Term selectStore = theory.term(SELECT, store, params[1]);
		return new ProofLiteral[] {
				new ProofLiteral(theory.term(EQUALS, selectStore, params[2]), true) };
	}

	public static ProofLiteral[] selectStore2(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		final Term[] params = (Term[]) ruleParams;
		assert params.length == 4;

		// (= (select (store a i v) j) (select a j))
		final Term store = theory.term(STORE, params[0], params[1], params[2]);
		final Term selectStore = theory.term(SELECT, store, params[3]);
		final Term select = theory.term(SELECT, params[0], params[3]);
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, selectStore, select), true),
				new ProofLiteral(theory.term(EQUALS, params[1], params[3]), true) };
	}

	public static ProofLiteral[] extDiff(MinimalProofChecker checker, Theory theory, Object[] ruleParams) {
		final Term[] params = (Term[]) ruleParams;
		assert params.length == 2;

		// (= a b), ~(= (select a (@diff a b)) (select b (@diff a b)))
		final Term diff = theory.term(DIFF, params[0], params[1]);
		final Term select0 = theory.term(SELECT, params[0], diff);
		final Term select1 = theory.term(SELECT, params[1], diff);
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, params[0], params[1]), true),
				new ProofLiteral(theory.term(EQUALS, select0, select1), false) };
	}

	public static ProofLiteral[] constAxiom(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 2;
		final Term value = (Term) params[0];
		final Term index = (Term) params[1];

		// (= (select (const value) index) value)
		final Sort arraySort = theory.getSort(ARRAY, index.getSort(), value.getSort());
		final Term constArray = theory.term(CONST, null, arraySort, value);
		final Term select = theory.term(SELECT, constArray, index);
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, select, value), true) };
	}
}
