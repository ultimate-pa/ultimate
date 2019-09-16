/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TermTuple {

	public final int arity;
	public final Term[] terms;

	private TermTuple(Term[] terms, int arity) {
		this.terms = terms;
		this.arity = arity;
	}

	public TermTuple(Term[] arguments) {
		this(arguments, arguments.length);
	}

	@Override
	public boolean equals(Object arg0) {
		if (!(arg0 instanceof TermTuple))
			return false;
		TermTuple other = (TermTuple) arg0;
		if (other.arity != this.arity)
			return false;
		for (int i = 0; i < arity; i++) {
			if (!other.terms[i].equals(this.terms[i]))
				return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
		// TODO: double-check if this is a good hashing strategy
		return HashUtils.hashJenkins(31, (Object[]) terms);
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		String comma = "";
		for (Term t : terms) {
			sb.append(comma + t.toString());
			comma = ", ";
		}
		sb.append(")");
		return sb.toString();
	}



	public TTSubstitution match(TermTuple other,
			EqualityManager equalityManager) {
		return match(other, new TTSubstitution(), equalityManager);
	}

	/**
	 * @param other A TermTuple that may contain variables and constants
	 * @param newSubs a substitution that constrains the matching of variables
	 * @return a possibly more constrained substitution that is a unifier, null if there is no unifier
	 */
	public TTSubstitution match(
			TermTuple other,
			TTSubstitution subs,
			EqualityManager equalityManager) {
		assert this.arity == other.arity;

		TermTuple thisTT = subs.apply(new TermTuple(terms));
		TermTuple otherTT = subs.apply(new TermTuple(other.terms));

		TTSubstitution resultSubs = subs; // TODO: or is a copy needed?
		for (int i = 0; i < this.terms.length; i++) {
			Term thisTerm = thisTT.terms[i];
			Term otherTerm = otherTT.terms[i];

			TermVariable tvTerm = null;
			Term termTerm = null;

			if (thisTerm.equals(otherTerm)) {
				//match -- > do nothing
				continue;
			} else if (otherTerm instanceof TermVariable) {
				tvTerm = (TermVariable) otherTerm;
				termTerm = thisTerm;
			} else if (thisTerm instanceof TermVariable) {
				tvTerm = (TermVariable) thisTerm;
				termTerm = otherTerm;
			}

			if (tvTerm == null) {
				ArrayList<CCEquality> eqPath = equalityManager.isEqual((ApplicationTerm) thisTerm, (ApplicationTerm) otherTerm);
				if (eqPath == null){
					return null;
				}
				resultSubs.addEquality(thisTerm, otherTerm, eqPath);
				assert false : "TODO: rework/rethink equality handling (now that we switched to CDCL..)";
			} else {
				resultSubs.addSubs(termTerm, tvTerm);
			}
			thisTT = resultSubs.apply(thisTT);
			otherTT = resultSubs.apply(otherTT);
		}
		assert resultSubs.apply(this).equals(resultSubs.apply(other))
			: "the returned substitution should be a unifier";
		return resultSubs;
	}

	public boolean onlyContainsConstants() {
		//TODO cache
		boolean result = true;
		for (Term t : terms)
			result &= t.getFreeVars().length == 0;
		return result;
	}

	public TermTuple applySubstitution(Map<TermVariable, Term> sub) {
		Term[] newTerms = new Term[terms.length];
		for (int i = 0; i < newTerms.length; i++)
			if (terms[i] instanceof TermVariable
					&& sub.containsKey(terms[i]))
				newTerms[i] = sub.get(terms[i]);
			else
				newTerms[i] = terms[i];

		assert nonNull(newTerms) : "substitution created a null-entry";
		return new TermTuple(newTerms);
	}

	private boolean nonNull(Term[] trms) {
		for (Term t : trms)
			if (t == null)
				return false;
		return true;
	}

	public HashSet<TermVariable> getFreeVars() {
		HashSet<TermVariable> result = new HashSet<TermVariable>();
		for (Term t : terms)
			if (t instanceof TermVariable)
				result.add((TermVariable) t);
		return result;
	}

	public HashSet<ApplicationTerm> getConstants() {
		HashSet<ApplicationTerm> result = new HashSet<ApplicationTerm>();
		for (Term t : terms)
			if (t instanceof ApplicationTerm)
				result.add((ApplicationTerm) t);
		return result;
	}

	public boolean isGround() {
		return getFreeVars().size() == 0;
	}
}
