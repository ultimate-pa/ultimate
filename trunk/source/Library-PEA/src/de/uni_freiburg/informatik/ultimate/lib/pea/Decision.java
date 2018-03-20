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

import java.util.HashMap;
import java.util.Map;

/**
 * TODO : Documentation hoenicke.
 *
 * @author hoenicke
 *
 */
public abstract class Decision {

	public boolean implies(final Decision other, final CDD[] childs, final CDD[] ochilds) {
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

	public CDD and(final Decision other, final CDD[] childs, final CDD[] ochilds) {
		return and(other, childs, ochilds, new HashMap<CDD, Map<CDD, CDD>>());
	}

	public CDD and(final Decision other, final CDD[] childs, final CDD[] ochilds, final Map<CDD, Map<CDD, CDD>> cache) {
		/* default implementation for boolean decisions */
		final CDD[] nchilds = new CDD[childs.length];

		for (int i = 0; i < childs.length; i++) {
			nchilds[i] = childs[i].and(ochilds[i], cache);
		}
		return simplify(nchilds);
	}

	public CDD or(final Decision other, final CDD[] childs, final CDD[] ochilds) {
		/* default implementation for boolean decisions */
		final CDD[] nchilds = new CDD[childs.length];

		for (int i = 0; i < childs.length; i++) {
			nchilds[i] = childs[i].or(ochilds[i]);
		}
		return simplify(nchilds);
	}

	public CDD assume(final Decision other, final CDD[] childs, final CDD[] ochilds) {
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
	public abstract Decision prime();

	public abstract Decision prime(String ignore);

	/**
	 * Create a Decision where primed variable names occur as unprimed versions.
	 *
	 * @return the unprimed version of this Decision.
	 */
	public abstract Decision unprime();

	public abstract Decision unprime(String ignore);

	public abstract String toString(int child);

	public abstract String toSmtString(int child);

	public abstract String toTexString(int child);

	public abstract String toUppaalString(int child);

	public abstract String toUppaalStringDOM(int child);

	public abstract String getVar(); // sr 2010-07-29

	public String getSafeVar() {
		return "var_h_" + Math.abs(getVar().hashCode());
	}

	public String toSmtString(final int child, final int index) {
		return toSmtString(child);
	}

}
