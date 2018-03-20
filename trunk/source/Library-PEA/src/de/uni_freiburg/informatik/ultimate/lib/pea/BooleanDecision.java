/*
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

import java.util.Vector;

/**
 * BooleanDecision represents a simple boolean statement. It shall not be used for arithmetical expressions like a < b +
 * c anymore. In those cases use RelationDecision instead.
 *
 * @author hoenicke
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.RelationDecision
 */
public class BooleanDecision extends Decision {

	public static final String PRIME_SUFFIX = "'";

	private static Vector<String> allVars = new Vector<>();

	private final String mVar;
	private int mGlobalIdx = -1;

	public BooleanDecision(final String v) {
		mGlobalIdx = allVars.indexOf(v);

		if (mGlobalIdx < 0) {
			allVars.add(v);
			mGlobalIdx = allVars.indexOf(v);
		}

		mVar = v;
	}

	/**
	 * Create an boolean constraint.
	 *
	 * @param var
	 *            the condition that must hold.
	 */
	public static CDD create(final String var) {
		return CDD.create(new BooleanDecision(var), CDD.TRUE_CHILDS);
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof BooleanDecision)) {
			return false;
		}

		return mVar.equals(((BooleanDecision) o).mVar);
	}

	@Override
	public int hashCode() {
		return mVar.hashCode();
	}

	/**
	 * @return Returns the var.
	 */
	@Override
	public String getVar() {
		return mVar;
	}

	@Override
	public String toString(final int child) {
		return (child == 0) ? mVar : ("!" + mVar);
	}

	@Override
	public String toSmtString(final int child) {
		return toSmtString(child, -1);
	}

	@Override
	public String toSmtString(final int child, final int index) {
		if (index < 0) {
			return (child == 0) ? ("(var_h_" + Math.abs(mVar.hashCode()) + ")")
					: ("(not var_h_" + Math.abs(mVar.hashCode()) + ")");
		}
		return (child == 0) ? ("(var_h_" + Math.abs(mVar.hashCode()) + "_" + index + ")")
				: ("(not var_h_" + Math.abs(mVar.hashCode()) + "_" + index + ")");
	}

	@Override
	public String toTexString(final int child) {
		return (child == 0) ? mVar : (" \\neg " + mVar);
	}

	@Override
	public String toUppaalString(final int child) {
		// return child == 0 ? var : " \\neg " + var;
		return "true";
	}

	@Override
	public String toUppaalStringDOM(final int child) {
		return "true";
	}

	private Decision primeCache;

	@Override
	public Decision prime() {
		return this.prime(null);
	}

	@Override
	public Decision prime(final String ignore) {
		if (mVar.equals(ignore)) {
			return this;
		}
		if (primeCache != null) {
			return primeCache;
		}
		final String decision = mVar.replaceAll("([a-zA-Z_])(\\w*)", "$1$2" + BooleanDecision.PRIME_SUFFIX);

		primeCache = new BooleanDecision(decision);
		return primeCache;
	}

	// by Ami
	@Override
	public Decision unprime() {
		return this.unprime(null);
	}

	@Override
	public Decision unprime(final String ignore) {
		if (mVar.equals(ignore)) {
			return this;
		}
		final String result = mVar.replaceAll("([a-zA-Z_])(\\w*)" + BooleanDecision.PRIME_SUFFIX, "$1$2"); // SR
																											// 2010-08-02

		return (new BooleanDecision(result));
	}
}
