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

import java.util.HashMap;

public class RangeDecision extends Decision {
	public static final int OP_LT = -2;
	public static final int OP_LTEQ = -1;
	public static final int OP_EQ = 0;
	public static final int OP_GTEQ = 1;
	public static final int OP_GT = 2;
	public static final int OP_NEQ = 4;
	public static final int OP_INVALID = 5;
	public static final String PRIME = BooleanDecision.PRIME;
	private static final CDD[] FTF = new CDD[] { CDD.FALSE, CDD.TRUE, CDD.FALSE };
	private static final CDD[] TFT = new CDD[] { CDD.TRUE, CDD.FALSE, CDD.TRUE };
	String var;
	int[] limits;

	public RangeDecision(final String var, final int[] limits) {
		this.var = var;
		this.limits = limits;
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof RangeDecision)) {
			return false;
		}

		final RangeDecision rd = (RangeDecision) o;

		if (!var.equals(rd.var)) {
			return false;
		}

		for (int i = 0; i < limits.length; i++) {
			if (limits[i] != rd.limits[i]) {
				return false;
			}
		}

		return true;
	}

	@Override
	public int hashCode() {
		int hash = var.hashCode();

		for (int i = 0; i < limits.length; i++) {
			hash = (hash * (i + 13)) ^ limits[i];
		}

		return hash;
	}

	@Override
	public CDD simplify(final CDD[] childs) {
		int elems = 0;

		for (int i = 0; i < limits.length; i++) {
			if (childs[i] != childs[i + 1]) {
				elems++;
			}
		}

		if (elems == 0) {
			return childs[0];
		}

		if (elems < limits.length) {
			final int[] nlimits = new int[elems++];
			final CDD[] nchilds = new CDD[elems];
			elems = 0;

			for (int i = 0; i < limits.length; i++) {
				if (childs[i] != childs[i + 1]) {
					nchilds[elems] = childs[i];
					nlimits[elems] = limits[i];
					elems++;
				}
			}

			nchilds[elems] = childs[limits.length];

			return CDD.create(new RangeDecision(var, nlimits), nchilds);
		}

		return CDD.create(this, childs);
	}

	public static CDD create(final String var, final int op, final int value) {
		CDD cdd;

		switch (op) {
		case OP_EQ:
			cdd = CDD.create(new RangeDecision(var, new int[] { 2 * value, (2 * value) + 1 }), FTF);

			break;

		case OP_NEQ:
			cdd = CDD.create(new RangeDecision(var, new int[] { 2 * value, (2 * value) + 1 }), TFT);

			break;

		case OP_LT:
			cdd = CDD.create(new RangeDecision(var, new int[] { 2 * value }), CDD.trueChilds);

			break;

		case OP_LTEQ:
			cdd = CDD.create(new RangeDecision(var, new int[] { (2 * value) + 1 }), CDD.trueChilds);

			break;

		case OP_GT:
			cdd = CDD.create(new RangeDecision(var, new int[] { (2 * value) + 1 }), CDD.falseChilds);

			break;

		case OP_GTEQ:
			cdd = CDD.create(new RangeDecision(var, new int[] { 2 * value }), CDD.falseChilds);

			break;

		default:
			throw new IllegalArgumentException("op = " + op);
		}

		return cdd;
	}

	@Override
	public int compareTo(final Object o) {
		if (o instanceof EventDecision) {
			return 1;
		}

		if (!(o instanceof RangeDecision)) {
			return -1;
		}

		return var.compareTo(((RangeDecision) o).var);
	}

	@Override
	public CDD and(final Decision other, CDD[] childs, final CDD[] ochilds,
			final HashMap<CDD, HashMap<CDD, CDD>> cache) {
		final int[] olimits = ((RangeDecision) other).limits;

		if (childs.length == 1) // SR2010-08-03
		{
			final CDD[] t = childs;
			childs = new CDD[2];
			childs[0] = t[0];
			childs[1] = CDD.FALSE;
		}

		/* intersect all intervals */
		CDD[] nchilds = new CDD[(childs.length + ochilds.length) - 1];
		int[] nlimits = new int[limits.length + olimits.length];

		int nptr = 0;
		int optr = 0;
		int tptr = 0;

		while ((optr < olimits.length) || (tptr < limits.length)) {
			nchilds[nptr] = childs[tptr].and(ochilds[optr], cache);

			if ((nptr > 0) && (nchilds[nptr] == nchilds[nptr - 1])) {
				nptr--;
			}

			if ((optr == olimits.length) || ((tptr < limits.length) && (limits[tptr] < olimits[optr]))) {
				nlimits[nptr++] = limits[tptr++];
			} else {
				if ((tptr < limits.length) && (limits[tptr] == olimits[optr])) {
					tptr++;
				}

				nlimits[nptr++] = olimits[optr++];
			}
		}

		nchilds[nptr] = childs[tptr].and(ochilds[optr], cache);

		if ((nptr > 0) && (nchilds[nptr] == nchilds[nptr - 1])) {
			nptr--;
		}

		if (nptr == 0) {
			return nchilds[0];
		}

		if (nptr != nlimits.length) {
			final int[] nnlimits = new int[nptr];
			System.arraycopy(nlimits, 0, nnlimits, 0, nptr);
			nlimits = nnlimits;

			final CDD[] nnchilds = new CDD[nptr + 1];
			System.arraycopy(nchilds, 0, nnchilds, 0, nptr + 1);
			nchilds = nnchilds;
		}

		return CDD.create(new RangeDecision(var, nlimits), nchilds);
	}

	@Override
	public CDD or(final Decision other, final CDD[] childs, final CDD[] ochilds) {
		final int[] olimits = ((RangeDecision) other).limits;

		/* intersect all intervals */
		CDD[] nchilds = new CDD[(childs.length + ochilds.length) - 1];
		int[] nlimits = new int[limits.length + olimits.length];

		int nptr = 0;
		int optr = 0;
		int tptr = 0;

		while ((optr < olimits.length) || (tptr < limits.length)) {
			nchilds[nptr] = childs[tptr].or(ochilds[optr]);

			if ((nptr > 0) && (nchilds[nptr] == nchilds[nptr - 1])) {
				nptr--;
			}

			if ((optr == olimits.length) || ((tptr < limits.length) && (limits[tptr] < olimits[optr]))) {
				nlimits[nptr++] = limits[tptr++];
			} else {
				if ((tptr < limits.length) && (limits[tptr] == olimits[optr])) {
					tptr++;
				}

				nlimits[nptr++] = olimits[optr++];
			}
		}

		nchilds[nptr] = childs[tptr].or(ochilds[optr]);

		if ((nptr > 0) && (nchilds[nptr] == nchilds[nptr - 1])) {
			nptr--;
		}

		if (nptr == 0) {
			return nchilds[0];
		}

		if (nptr != nlimits.length) {
			final int[] nnlimits = new int[nptr];
			System.arraycopy(nlimits, 0, nnlimits, 0, nptr);
			nlimits = nnlimits;

			final CDD[] nnchilds = new CDD[nptr + 1];
			System.arraycopy(nchilds, 0, nnchilds, 0, nptr + 1);
			nchilds = nnchilds;
		}

		return CDD.create(new RangeDecision(var, nlimits), nchilds);
	}

	@Override
	public CDD assume(final Decision other, final CDD[] childs, final CDD[] ochilds) {
		final int[] olimits = ((RangeDecision) other).limits;

		/* intersect all intervals */
		CDD[] nchilds = new CDD[(childs.length + ochilds.length) - 1];
		int[] nlimits = new int[limits.length + olimits.length];

		int nptr = 0;
		int optr = 0;
		int tptr = 0;
		CDD lastass = null;

		while ((optr < olimits.length) || (tptr < limits.length)) {
			nchilds[nptr] = childs[tptr].assume(ochilds[optr]);

			// System.err.println(""+tptr+","+optr+","+nptr+": "+nchilds[nptr]+
			// " - "+(nptr > 0 ? ""+nlimits[nptr-1] : "-oo")+ " :
			// "+childs[tptr]+".assume."+ochilds[optr]);
			if ((nptr > 0) && nchilds[nptr].and(ochilds[optr]).implies(nchilds[nptr - 1])
					&& nchilds[nptr - 1].and(lastass).implies(nchilds[nptr])) {
				nchilds[nptr - 1] = nchilds[nptr].and(nchilds[nptr - 1]);
				nptr--;
			}

			lastass = ochilds[optr];

			if ((optr == olimits.length) || ((tptr < limits.length) && (limits[tptr] < olimits[optr]))) {
				nlimits[nptr++] = limits[tptr++];
			} else {
				if ((tptr < limits.length) && (limits[tptr] == olimits[optr])) {
					tptr++;
				}

				nlimits[nptr++] = olimits[optr++];
			}
		}

		nchilds[nptr] = childs[tptr].assume(ochilds[optr]);

		// System.err.println(""+tptr+","+optr+","+nptr+": "+nchilds[nptr]+ " -
		// "+(nptr > 0 ? ""+nlimits[nptr-1] : "-oo"));
		if ((nptr > 0) && nchilds[nptr].and(ochilds[optr]).implies(nchilds[nptr - 1])
				&& nchilds[nptr - 1].and(lastass).implies(nchilds[nptr])) {
			nchilds[nptr - 1] = nchilds[nptr].and(nchilds[nptr - 1]);
			nptr--;
		}

		if (nptr == 0) {
			return nchilds[0];
		}

		if (nptr != nlimits.length) {
			final int[] nnlimits = new int[nptr];
			System.arraycopy(nlimits, 0, nnlimits, 0, nptr);
			nlimits = nnlimits;

			final CDD[] nnchilds = new CDD[nptr + 1];
			System.arraycopy(nchilds, 0, nnchilds, 0, nptr + 1);
			nchilds = nnchilds;
		}

		return CDD.create(new RangeDecision(var, nlimits), nchilds);
	}

	@Override
	public boolean implies(final Decision other, final CDD[] childs, final CDD[] ochilds) {
		final int[] olimits = ((RangeDecision) other).limits;

		int tptr = 0;
		int optr = 0;

		while ((optr < olimits.length) || (tptr < limits.length)) {
			if (!childs[tptr].implies(ochilds[optr])) {
				return false;
			}

			if ((optr == olimits.length) || ((tptr < limits.length) && (limits[tptr] < olimits[optr]))) {
				tptr++;
			} else {
				if ((tptr < limits.length) && (limits[tptr] == olimits[optr])) {
					tptr++;
				}

				optr++;
			}
		}

		return childs[tptr].implies(ochilds[optr]);
	}

	@Override
	public String toString(final int childs) {
		if (childs == 0) {
			return var + (((limits[0] & 1) == 0) ? " < " : " \u2264 ") + (limits[0] / 2);
		}

		if (childs == limits.length) {
			return var + (((limits[limits.length - 1] & 1) == 1) ? " > " : " \u2265 ")
					+ (limits[limits.length - 1] / 2);
		}

		if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
			return var + " == " + (limits[childs] / 2);
		}

		return (limits[childs - 1] / 2) + (((limits[childs - 1] & 1) == 1) ? " < " : " \u2264 ") + var
				+ (((limits[childs] & 1) == 0) ? " < " : " \u2264 ") + (limits[childs] / 2);
	}

	@Override
	public String toSmtString(final int childs) {
		return toSmtString(childs, 0);
	}

	@Override
	public String toSmtString(final int childs, final int index) {
		final String var = "(- T_" + index + " " + this.var + "_" + index + ")";

		if (childs == 0) {
			return "( " + (((limits[0] & 1) == 0) ? " < " : " <= ") + var + " " + (limits[0] / 2) + ".0)";
		}

		if (childs == limits.length) {
			return "( " + (((limits[limits.length - 1] & 1) == 1) ? " > " : " >= ") + var + " "
					+ (limits[limits.length - 1] / 2) + ".0)";
		}

		if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
			return " (= " + var + " " + (limits[childs] / 2) + ".0)";
		}

		return "(and (" + (((limits[childs - 1] & 1) == 1) ? " < " : " <= ") + (limits[childs - 1] / 2) + ".0 " + var
				+ ") (" + (((limits[childs] & 1) == 0) ? " < " : ".0 <= ") + var + " " + (limits[childs] / 2) + "0. ))";
	}

	public int getVal(final int childs) {
		if ((childs == 0) || (childs == 1)) {
			return (limits[0] / 2);
		}

		return -1;
	}

	public int getOp(final int childs) {
		if (childs == 0) {
			return (((limits[0] & 1) == 0) ? OP_LT : OP_LTEQ);
		}

		if (childs == limits.length) { // expects 1

			return (((limits[limits.length - 1] & 1) == 1) ? OP_GT : OP_GTEQ);
		}

		if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
			return OP_EQ;
		}

		return OP_INVALID;
	}

	@Override
	public String toUppaalString(final int childs) {
		String var = this.var;

		if (var.charAt(var.length() - 1) == '\'') {
			var = var.substring(0, var.length() - 1);
		}

		if (childs == 0) {
			return var + (((limits[0] & 1) == 0) ? " &lt; " : " &lt;= ") + (limits[0] / 2);
		}

		if (childs == limits.length) {
			return var + (((limits[limits.length - 1] & 1) == 1) ? " &gt; " : " &gt;= ")
					+ (limits[limits.length - 1] / 2);
		}

		if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
			return var + " == " + (limits[childs] / 2);
		}

		return var + (((limits[childs - 1] & 1) == 1) ? " &gt; " : " &gt;= ") + (limits[childs - 1] / 2)
				+ " &amp;&amp; " + var + (((limits[childs] & 1) == 0) ? " &lt; " : " &lt;= ") + (limits[childs] / 2);
	}

	@Override
	public String toUppaalStringDOM(final int childs) {
		String var = this.var;

		if (var.charAt(var.length() - 1) == '\'') {
			var = var.substring(0, var.length() - 1);
		}

		if (childs == 0) {
			return var + (((limits[0] & 1) == 0) ? " < " : " <= ") + (limits[0] / 2);
		}

		if (childs == limits.length) {
			return var + (((limits[limits.length - 1] & 1) == 1) ? " > " : " >= ") + (limits[limits.length - 1] / 2);
		}

		if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
			return var + " == " + (limits[childs] / 2);
		}

		return var + (((limits[childs - 1] & 1) == 1) ? " > " : " >= ") + (limits[childs - 1] / 2) + " && " + var
				+ (((limits[childs] & 1) == 0) ? " < " : " <= ") + (limits[childs] / 2);
	}

	public static void main(final String[] param) {
		final CDD[] a = new CDD[] { RangeDecision.create("x", OP_EQ, 5), RangeDecision.create("x", OP_LTEQ, 7),
				RangeDecision.create("x", OP_LT, 3), RangeDecision.create("x", OP_GT, 0),
				RangeDecision.create("x", OP_GTEQ, 5) };

		for (int i = 0; i < a.length; i++) {
			for (int j = 0; j < a.length; j++) {
				System.err.println("Taking " + a[i] + " assume " + a[j]);
				System.err.println(a[i].assume(a[j]));
				System.err.println(a[i].assume(a[j].negate()));
				System.err.println(a[i].negate().assume(a[j]));
				System.err.println(a[i].negate().assume(a[j].negate()));

				// System.err.println(a[i].negate().and(a[j].negate()).negate());
				// System.err.println(a[i].or(a[j]));
			}
		}
	}

	/**
	 * @return Returns the var.
	 */
	@Override
	public String getVar() {
		return var;
	}

	/**
	 * @return Returns the limits.
	 */
	public int[] getLimits() {
		return limits;
	}

	@Override
	public Decision prime(final String ignore) {
		if (ignore != null && var.equals(ignore)) {
			return this;
		}
		final String primed = var + RangeDecision.PRIME;
		final int[] limits = this.limits.clone();

		return new RangeDecision(primed, limits);
	}

	// by Ami
	@Override
	public Decision unprime(final String ignore) {
		if (ignore != null && var.equals(ignore)) {
			return this;
		}
		String unprimed = var;

		if (var.endsWith(PRIME)) {
			unprimed = var.substring(0, var.length() - 1);
		}

		final int[] limits = this.limits.clone();

		return new RangeDecision(unprimed, limits);
	}

	@Override
	public String toTexString(final int childs) {
		if (childs == 0) {
			return var + (((limits[0] & 1) == 0) ? " < " : " \\leq ") + (limits[0] / 2);
		}

		if (childs == limits.length) {
			return var + (((limits[limits.length - 1] & 1) == 1) ? " > " : " \\geq ") + (limits[limits.length - 1] / 2);
		}

		if ((limits[childs - 1] / 2) == (limits[childs] / 2)) {
			return var + " == " + (limits[childs] / 2);
		}

		return (limits[childs - 1] / 2) + (((limits[childs - 1] & 1) == 1) ? " < " : " \\leq ") + var
				+ (((limits[childs] & 1) == 0) ? " < " : " \\leq ") + (limits[childs] / 2);
	}

	@Override
	public Decision unprime() {
		return this.unprime(null);
	}

	@Override
	public Decision prime() {
		return this.prime(null);
	}
}
