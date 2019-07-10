/* $Id: Decision.java 328 2008-08-06 11:19:16Z jfaber $
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * TODO : Documentation hoenicke.
 *
 * @author hoenicke
 *
 */
public abstract class Decision<T extends Decision<T>> {

	public boolean implies(final Decision<?> other, final CDD[] childs, final CDD[] ochilds) {
		/* default implementation for boolean decisions */
		for (int i = 0; i < childs.length; i++) {
			if (!childs[i].implies(ochilds[i])) {
				return false;
			}
		}
		return true;
	}

	public CDD simplify(final CDD[] childs) {
		for (int i = 1; i < childs.length; i++) {
			if (childs[i] != childs[0]) {
				return CDD.create(this, childs);
			}
		}
		return childs[0];
	}

	public CDD and(final Decision<?> other, final CDD[] childs, final CDD[] ochilds,
			final Map<CDD, Map<CDD, CDD>> cache) {
		/* default implementation for boolean decisions */
		final CDD[] nchilds = new CDD[childs.length];

		for (int i = 0; i < childs.length; i++) {
			nchilds[i] = childs[i].and(ochilds[i], cache);
		}
		return simplify(nchilds);
	}

	public CDD or(final Decision<?> other, final CDD[] childs, final CDD[] ochilds,
			final Map<CDD, Map<CDD, CDD>> cache) {
		/* default implementation for boolean decisions */
		final CDD[] nchilds = new CDD[childs.length];

		for (int i = 0; i < childs.length; i++) {
			nchilds[i] = childs[i].or(ochilds[i], cache);
		}
		return simplify(nchilds);
	}

	public CDD assume(final Decision<?> other, final CDD[] childs, final CDD[] ochilds) {
		/* default implementation for boolean decisions */
		final CDD[] nchilds = new CDD[childs.length];

		for (int i = 0; i < childs.length; i++) {
			nchilds[i] = childs[i].assume(ochilds[i]);
		}

		return simplify(nchilds);
	}

	/**
	 * Create a Decision where the variable names occur as primed versions.
	 *
	 * @return the primed version of this Decision.
	 */
	public abstract T prime(Set<String> ignoredIds);

	/**
	 * Create a Decision where primed variable names occur as unprimed versions.
	 *
	 * @return the unprimed version of this Decision.
	 */
	public abstract T unprime(Set<String> ignoredIds);

	public abstract String toString(int child);

	public abstract String toSmtString(int child);

	public abstract String toTexString(int child);

	public abstract String toUppaalString(int child);

	public abstract String toBoogieString(int child);

	public abstract String toUppaalStringDOM(int child);

	public abstract String getVar(); // sr 2010-07-29

	@Override
	public abstract boolean equals(Object obj);

	@Override
	public abstract int hashCode();

	public String getSafeVar() {
		return "var_h_" + Math.abs(getVar().hashCode());
	}

	/**
	 * Called by the {@link DecisionComparator}.
	 *
	 * @param other
	 *            guaranteed to be non-null and of the same type as the current class
	 * @return
	 */
	public abstract int compareToSimilar(Decision<?> other);

	public static Comparator<Decision<?>> getComparator() {
		return new DecisionComparator();
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class DecisionComparator implements Comparator<Decision<?>> {
		private static final Map<Class<?>, Integer> ORDER = new HashMap<>();
		static {
			ORDER.put(EventDecision.class, 10);
			ORDER.put(RangeDecision.class, 9);
			ORDER.put(BooleanDecision.class, 8);
			ORDER.put(RelationDecision.class, 7);
			ORDER.put(ZDecision.class, 6);
			ORDER.put(BoogieBooleanExpressionDecision.class, 5);
		}

		@Override
		public int compare(final Decision<?> o1, final Decision<?> o2) {
			if (o1 == null && o2 == null) {
				return 0;
			} else if (o1 == null) {
				return 1;
			} else if (o2 == null) {
				return -1;
			} else {
				final Class<?> o1class = o1.getClass();
				final Class<?> o2class = o2.getClass();
				if (o1class != o2class) {
					final Integer o1prio = ORDER.get(o1class);
					final Integer o2prio = ORDER.get(o2class);
					if (o1prio == null || o2prio == null) {
						throw new UnsupportedOperationException(
								"Unknown subclass of Decision: " + o1class + " or " + o2class);
					}
					return o1prio.compareTo(o2prio);
				}
				// alternative: use lexicographic comparison
				return o1.compareToSimilar(o2);
			}
		}
	}
}
