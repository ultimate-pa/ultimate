/*
 * Copyright (C) 2012 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * A rewrite tracker that does nothing.  This can be used to "track" rewrites if
 * proof production is disabled.
 * @author Juergen Christ
 */
public class NoopProofTracker implements IProofTracker {

	@Override
	public void reset() { /* Noop */ }

	@Override
	public void expand(ApplicationTerm orig) { /* Noop */ }

	@Override
	public void distinct(Term[] args, Term res, int rule) { /* Noop */ }

	@Override
	public void negation(Term pos, Term res, int rule) { /* Noop */ }

	@Override
	public void or(Term[] args, Term res, int rule) { /* Noop */ }

	@Override
	public void ite(
			Term cond, Term thenTerm, Term elseTerm, Term res, int rule) {
		/* Noop */
	}

	@Override
	public void strip(AnnotatedTerm orig) { /* Noop */ }

	@Override
	public void sum(FunctionSymbol fsym, Term[] args, Term res) { /* Noop */ }

	@Override
	public void leqSimp(SMTAffineTerm leq, Term res, int rule) { /* Noop */ }

	@Override
	public void desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs) {
	    // Noop
	}

	@Override
	public void divisible(FunctionSymbol divn, Term div, Term res) {
	    // Noop 
	}

	@Override
	public void expandDef(Term orig, Term res) { /* Noop */ }

	@Override
	public Term getRewriteProof(Term asserted) {
		return null;
	}

	@Override
	public void equality(Term[] args, Object res, int rule) { /* Noop */ }

	@Override
	public void distinctBoolEq(Term lhs, Term rhs, boolean firstNegated) {
		/* Noop */
	}

	@Override
	public void removeConnective(Term[] origArgs, Term result, int rule) {
		/* Noop */
	}

	@Override
	public void quoted(Term orig, Literal quote) { /* Noop */ }

	@Override
	public void eq(Term lhs, Term rhs, Term res) { /* Noop */ }

	@Override
	public void eq(Term lhs, Term rhs, DPLLAtom eqAtom) { /* Noop */ }

	@Override
	public void leq0(SMTAffineTerm sum, Literal lit) { /* Noop */ }

	@Override
	public Term split(Term res, Term proof, int splitKind) {
		return null;
	}

	@Override
	public void intern(Term term, Literal lit) { /* Noop */ }

	@Override
	public Term clause(Term proof) {
		return null;
	}

	@Override
	public Term auxAxiom(
			int auxKind, Literal auxLit, Term res, Term base, Object auxData) {
		return null;
	}

	@Override
	public IProofTracker getDescendent() {
		return this;
	}

	@Override
	public void modulo(ApplicationTerm appTerm, Term res) { /* Noop */ }

	@Override
	public void mod(Term x, Term y, Term res,
			int rule) { /* Noop */ }

	@Override
	public void div(Term x, Term y, Term res,
			int rule) { /* Noop */ }

	@Override
	public void toInt(Term arg, Term res) { /* Noop */ }

	@Override
	public void negateLit(Literal lit, Theory theory) { /* Noop */ }

	@Override
	public Term[] prepareIRAHack(Term[] args) { // NOPMD
		return null;
	}

	@Override
	public void arrayRewrite(Term[] args, Term result, int rule) { /* Noop */ }

	@Override
	public void flatten(Term[] args, boolean simpOr) { /* Noop */ }

	@Override
	public void orSimpClause(Term[] args) { /* Noop */ }

	@Override
	public void markPosition() { /* Noop */ }

	@Override
	public Term[] produceAuxAxiom(Literal auxlit, Term... args) { // NOPMD
		return null;
	}

	@Override
	public void save() { /* Noop */ }

	@Override
	public void restore() { /* Noop */ }

	@Override
	public void cleanSave() { /* Noop */ }

	@Override
	public void normalized(ConstantTerm term, SMTAffineTerm res) { /* Noop */ }

	@Override
	public boolean notifyLiteral(Literal lit, Term t) {
		// Never return false => Never restore this tracker...
		return true;
	}

	@Override
	public void notifyFalseLiteral(Term t) { /* Noop */ }

	@Override
	public void storeRewrite(
			ApplicationTerm store, Term result, boolean arrayFirst) {
	    // Noop
	}

	@Override
	public void toReal(Term arg, Term res) { /* Noop */ }

}
