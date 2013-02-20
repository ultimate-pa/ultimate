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
	public void reset() {}

	@Override
	public void expand(ApplicationTerm orig) {}

	@Override
	public void distinct(Term[] args, Term res, int rule) {}

	@Override
	public void negation(Term pos, Term res, int rule) {}

	@Override
	public void or(Term[] args, Term res, int rule) {}

	@Override
	public void ite(Term cond, Term thenTerm, Term elseTerm, Term res, int rule) {}

	@Override
	public void strip(AnnotatedTerm orig) {}

	@Override
	public void sum(FunctionSymbol fsym, Term[] args, Term res) {}

	@Override
	public void toLeq0(Term orig, SMTAffineTerm leq, int rule) {}

	@Override
	public void leqSimp(SMTAffineTerm leq, Term res, int rule) {}

	@Override
	public void desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs) {}

	@Override
	public void divisible(Term div, Term res) {}

	@Override
	public void expandDef(Term orig, Term res) {}

	@Override
	public Term getRewriteProof(Term asserted, Term result) {
		return null;
	}

	@Override
	public void equality(Term[] args, Object res, int rule) {}

	@Override
	public void distinctBinary(Term lhs, Term rhs, boolean firstNegated) {}

	@Override
	public void removeConnective(Term[] origArgs, Term result, int rule) {}

	@Override
	public void quoted(Term orig, Literal quote) {}

	@Override
	public void eq(Term lhs, Term rhs, Term res) {}

	@Override
	public void eq(Term lhs, Term rhs, DPLLAtom eqAtom) {}

	@Override
	public void leq0(SMTAffineTerm sum, Literal lit) {}

	@Override
	public Term split(Term res, Term proof, int splitKind) {
		return null;
	}

	@Override
	public void intern(Term term, Literal lit) {}

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
	public void modulo(ApplicationTerm appTerm, Term res) {}

	@Override
	public void mod(SMTAffineTerm x, SMTAffineTerm y, SMTAffineTerm res,
			int rule) {}

	@Override
	public void div(SMTAffineTerm x, SMTAffineTerm y, SMTAffineTerm res,
			int rule) {}

	@Override
	public void toInt(SMTAffineTerm arg, SMTAffineTerm res) {}

	@Override
	public void negateLit(Literal lit, Theory theory) {}

	@Override
	public Term[] prepareIRAHack(Term[] args) {
		return null;
	}

}
