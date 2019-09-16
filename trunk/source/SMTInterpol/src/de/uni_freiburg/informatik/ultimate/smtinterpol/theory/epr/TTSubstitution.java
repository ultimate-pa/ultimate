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
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TTSubstitution {
//	ArrayList<TPair> subs;
	ArrayList<SubsPair> subs;
	HashSet<TermVariable> tvSet = new HashSet<TermVariable>();

	public TTSubstitution() {
		super();
		this.subs = new ArrayList<SubsPair>();
	}

	public TTSubstitution(TermVariable tv, Term t) {
		this();
		this.addSubs(t, tv);
	}

	public TTSubstitution(TTSubstitution substitution) {
		// TODO is DeepCopy necessary?
		this();
		for (SubsPair tp : substitution.subs) {
			if (tp instanceof TPair)
				addSubs(tp.top, (TermVariable) tp.bot);
			else
				addEquality((EqPair) tp);
		}
	}

	public TTSubstitution(SortedSet<TermVariable> colnames, List<ApplicationTerm> point) {
		this();
		assert colnames.size() == point.size();
		Iterator<TermVariable> colIt = colnames.iterator();
		for (int i = 0; i < point.size(); i++) {
			TermVariable colName = colIt.next();
			addSubs(point.get(i), colName);
		}
	}

	public ArrayList<CCEquality> getEqPathForEquality(ApplicationTerm a, ApplicationTerm b) {
		for (SubsPair sp : subs) {
			if (sp instanceof EqPair) {
				EqPair ep = (EqPair) sp;
				if ((ep.bot.equals(a) && ep.top.equals(b))
						|| (ep.bot.equals(b) && ep.top.equals(a))) {
					return ep.eqPath;
				}
			}
		}
		assert false : "should not happen..";
		return null;
	}

	public void addEquality(EqPair eqp) {
		addEquality(eqp.top, eqp.bot, eqp.eqPath);
	}

	/**
	 * @param top
	 * @param bot
	 * @param eqPath a list of CCEqualities which are all true and together imply (= top bot)
	 */
	public void addEquality(Term top, Term bot, ArrayList<CCEquality> eqPath) {
		subs.add(new EqPair(top, bot, eqPath));
	}

	public void addSubs(Term top, TermVariable bot) {
		tvSet.add((TermVariable) bot);
		subs.add(new TPair(top, (TermVariable) bot));
	}

	public TermTuple apply(TermTuple tt) {
		if (subs.isEmpty())
			return tt;

		Term[] newTerms = new Term[tt.terms.length];
		for (int i = 0; i < newTerms.length; i++)
			newTerms[i] = tt.terms[i];
//		Arrays.copyOf(tt.terms, tt.terms.length);//new Term[tt.terms.length];//makes problems if the copied Array has a more special type

		for (int i = 0; i < tt.terms.length; i++) {
			for (int j = 0; j < subs.size(); j++) {
				SubsPair tp = subs.get(j);

				if (newTerms[i].equals(tp.bot))
					newTerms[i] = tp.top;
			}
		}
		return new TermTuple(newTerms);
	}

	/**
	 * true if application of this substitution is the identity function
	 */
	public boolean isEmpty() {
		return subs.isEmpty();
	}

	public Set<TermVariable> tvSet() {
		return tvSet;
	}

	@Override
	public String toString() {
		return subs.toString();
	}

	public ArrayList<SubsPair> getSubsPairs() {
		return subs;
	}

	public abstract class SubsPair {
		public final Term top;
		public final Term bot;
		public SubsPair(Term top, Term bot) {
			this.top = top;
			this.bot = bot;
		}

		@Override
		public String toString() {
			return String.format("(%s,%s)", top.toString(), bot.toString());
		}
	}

	public class EqPair extends SubsPair {

		ArrayList<CCEquality> eqPath;

		public EqPair(Term top, Term bot, ArrayList<CCEquality> eqPath) {
			super(top, bot);
			this.eqPath = eqPath;
		}

		@Override
		public String toString() {
			return String.format("(%s,%s)", top.toString(), bot.toString());

		}

	}

	public class TPair extends SubsPair {
		public final Term t;
		public final TermVariable tv;

		public TPair(Term top, TermVariable bot) {
			super(top, bot);
			this.t = top;
			this.tv = bot;
		}

		@Override
		public String toString() {
			return String.format("(%s,%s)", tv.toString(), t.toString());
		}
	}
}
