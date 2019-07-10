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

import java.util.Map;
import java.util.Set;

public class RangeDecision extends Decision<RangeDecision> {
	public static final int OP_LT = -2;
	public static final int OP_LTEQ = -1;
	public static final int OP_EQ = 0;
	public static final int OP_GTEQ = 1;
	public static final int OP_GT = 2;
	public static final int OP_NEQ = 4;
	public static final int OP_INVALID = 5;
	private static final CDD[] FTF = new CDD[] { CDD.FALSE, CDD.TRUE, CDD.FALSE };
	private static final CDD[] TFT = new CDD[] { CDD.TRUE, CDD.FALSE, CDD.TRUE };

	private final String mVar;
	private final int[] mLimits;

	public RangeDecision(final String var, final int[] limits) {
		mVar = var;
		mLimits = limits;
	}

	@Override
	public boolean equals(final Object o) {
		if (o == null || o.getClass() != getClass()) {
			return false;
		}

		final RangeDecision rd = (RangeDecision) o;

		if (!mVar.equals(rd.mVar)) {
			return false;
		}

		for (int i = 0; i < mLimits.length; i++) {
			if (mLimits[i] != rd.mLimits[i]) {
				return false;
			}
		}

		return true;
	}

	@Override
	public int hashCode() {
		int hash = mVar.hashCode();

		for (int i = 0; i < mLimits.length; i++) {
			hash = (hash * (i + 13)) ^ mLimits[i];
		}

		return hash;
	}

	@Override
	public CDD simplify(final CDD[] childs) {
		int elems = 0;

		for (int i = 0; i < mLimits.length; i++) {
			if (childs[i] != childs[i + 1]) {
				elems++;
			}
		}

		if (elems == 0) {
			return childs[0];
		}

		if (elems < mLimits.length) {
			final int[] nlimits = new int[elems++];
			final CDD[] nchilds = new CDD[elems];
			elems = 0;

			for (int i = 0; i < mLimits.length; i++) {
				if (childs[i] != childs[i + 1]) {
					nchilds[elems] = childs[i];
					nlimits[elems] = mLimits[i];
					elems++;
				}
			}

			nchilds[elems] = childs[mLimits.length];

			return CDD.create(new RangeDecision(mVar, nlimits), nchilds);
		}

		return CDD.create(this, childs);
	}

	public static CDD create(final String var, final int op, final int value) {
		switch (op) {
		case OP_EQ:
			return CDD.create(new RangeDecision(var, new int[] { 2 * value, (2 * value) + 1 }), FTF);
		case OP_NEQ:
			return CDD.create(new RangeDecision(var, new int[] { 2 * value, (2 * value) + 1 }), TFT);
		case OP_LT:
			return CDD.create(new RangeDecision(var, new int[] { 2 * value }), CDD.TRUE_CHILDS);
		case OP_LTEQ:
			return CDD.create(new RangeDecision(var, new int[] { (2 * value) + 1 }), CDD.TRUE_CHILDS);
		case OP_GT:
			return CDD.create(new RangeDecision(var, new int[] { (2 * value) + 1 }), CDD.FALSE_CHILDS);
		case OP_GTEQ:
			return CDD.create(new RangeDecision(var, new int[] { 2 * value }), CDD.FALSE_CHILDS);
		default:
			throw new IllegalArgumentException("op = " + op);
		}
	}

	@Override
	public CDD and(final Decision<?> other, final CDD[] childs, final CDD[] ochilds,
			final Map<CDD, Map<CDD, CDD>> cache) {
		final int[] olimits = ((RangeDecision) other).mLimits;

		/* intersect all intervals */
		CDD[] nchilds = new CDD[(childs.length + ochilds.length) - 1];
		int[] nlimits = new int[mLimits.length + olimits.length];

		int nptr = 0;
		int optr = 0;
		int tptr = 0;

		while ((optr < olimits.length) || (tptr < mLimits.length)) {
			nchilds[nptr] = childs[tptr].and(ochilds[optr], cache);

			if ((nptr > 0) && (nchilds[nptr] == nchilds[nptr - 1])) {
				nptr--;
			}

			if ((optr == olimits.length) || ((tptr < mLimits.length) && (mLimits[tptr] < olimits[optr]))) {
				nlimits[nptr++] = mLimits[tptr++];
			} else {
				if ((tptr < mLimits.length) && (mLimits[tptr] == olimits[optr])) {
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

		return CDD.create(new RangeDecision(mVar, nlimits), nchilds);
	}

	@Override
	public CDD or(final Decision<?> other, final CDD[] childs, final CDD[] ochilds,
			final Map<CDD, Map<CDD, CDD>> cache) {
		final int[] olimits = ((RangeDecision) other).mLimits;

		/* intersect all intervals */
		CDD[] nchilds = new CDD[(childs.length + ochilds.length) - 1];
		int[] nlimits = new int[mLimits.length + olimits.length];

		int nptr = 0;
		int optr = 0;
		int tptr = 0;

		while ((optr < olimits.length) || (tptr < mLimits.length)) {
			nchilds[nptr] = childs[tptr].or(ochilds[optr], cache);

			if ((nptr > 0) && (nchilds[nptr] == nchilds[nptr - 1])) {
				nptr--;
			}

			if ((optr == olimits.length) || ((tptr < mLimits.length) && (mLimits[tptr] < olimits[optr]))) {
				nlimits[nptr++] = mLimits[tptr++];
			} else {
				if ((tptr < mLimits.length) && (mLimits[tptr] == olimits[optr])) {
					tptr++;
				}

				nlimits[nptr++] = olimits[optr++];
			}
		}

		nchilds[nptr] = childs[tptr].or(ochilds[optr], cache);

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

		return CDD.create(new RangeDecision(mVar, nlimits), nchilds);
	}

	@Override
	public CDD assume(final Decision<?> other, final CDD[] childs, final CDD[] ochilds) {
		final int[] olimits = ((RangeDecision) other).mLimits;

		/* intersect all intervals */
		CDD[] nchilds = new CDD[(childs.length + ochilds.length) - 1];
		int[] nlimits = new int[mLimits.length + olimits.length];

		int nptr = 0;
		int optr = 0;
		int tptr = 0;
		CDD lastass = null;

		while ((optr < olimits.length) || (tptr < mLimits.length)) {
			nchilds[nptr] = childs[tptr].assume(ochilds[optr]);

			if ((nptr > 0) && nchilds[nptr].and(ochilds[optr]).implies(nchilds[nptr - 1])
					&& nchilds[nptr - 1].and(lastass).implies(nchilds[nptr])) {
				nchilds[nptr - 1] = nchilds[nptr].and(nchilds[nptr - 1]);
				nptr--;
			}

			lastass = ochilds[optr];

			if ((optr == olimits.length) || ((tptr < mLimits.length) && (mLimits[tptr] < olimits[optr]))) {
				nlimits[nptr++] = mLimits[tptr++];
			} else {
				if ((tptr < mLimits.length) && (mLimits[tptr] == olimits[optr])) {
					tptr++;
				}

				nlimits[nptr++] = olimits[optr++];
			}
		}

		nchilds[nptr] = childs[tptr].assume(ochilds[optr]);

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

		return CDD.create(new RangeDecision(mVar, nlimits), nchilds);
	}

	@Override
	public boolean implies(final Decision<?> other, final CDD[] childs, final CDD[] ochilds) {
		final int[] olimits = ((RangeDecision) other).mLimits;

		int tptr = 0;
		int optr = 0;

		while ((optr < olimits.length) || (tptr < mLimits.length)) {
			if (!childs[tptr].implies(ochilds[optr])) {
				return false;
			}

			if ((optr == olimits.length) || ((tptr < mLimits.length) && (mLimits[tptr] < olimits[optr]))) {
				tptr++;
			} else {
				if ((tptr < mLimits.length) && (mLimits[tptr] == olimits[optr])) {
					tptr++;
				}

				optr++;
			}
		}

		return childs[tptr].implies(ochilds[optr]);
	}

	@Override
	public String toString(final int childs) {
		return getInfixString(mVar, " \u2264 ", " < ", " \u2265 ", " > ", " == ", " \u02C4 ", childs);
	}

	@Override
	public String toBoogieString(final int child) {
		return getInfixString(mVar, " <= ", " < ", " >= ", " > ", " == ", " && ", child);
	}

	@Override
	public String toUppaalString(final int childs) {
		String var = mVar;

		if (var.charAt(var.length() - 1) == '\'') {
			var = var.substring(0, var.length() - 1);
		}

		return getInfixString(var, " &lt;= ", " &lt; ", " &gt;= ", " &gt; ", " == ", " &amp;&amp;", childs);
	}

	@Override
	public String toUppaalStringDOM(final int childs) {
		String var = mVar;

		if (var.charAt(var.length() - 1) == '\'') {
			var = var.substring(0, var.length() - 1);
		}

		return getInfixString(var, " <= ", " < ", " >= ", " > ", " == ", " && ", childs);
	}

	@Override
	public String toTexString(final int childs) {
		return getInfixString(mVar, " \\leq ", " < ", " \\geq ", " > ", " == ", " \\land ", childs);
	}

	private String getInfixString(final String var, final String leqOp, final String leOp, final String geqOp,
			final String geOp, final String eqOp, final String andOp, final int childs) {
		if (childs == 0) {
			return var + (((mLimits[0] & 1) == 0) ? leOp : leqOp) + (mLimits[0] / 2);
		}

		if (childs == mLimits.length) {
			return var + (((mLimits[mLimits.length - 1] & 1) == 1) ? geOp : geqOp) + (mLimits[mLimits.length - 1] / 2);
		}

		if ((mLimits[childs - 1] / 2) == (mLimits[childs] / 2)) {
			return var + eqOp + (mLimits[childs] / 2);
		}

		return var + (((mLimits[childs - 1] & 1) == 1) ? geOp : geqOp) + (mLimits[childs - 1] / 2) + andOp + var
				+ (((mLimits[childs] & 1) == 0) ? leOp : leqOp) + (mLimits[childs] / 2);
	}

	@Override
	public String toSmtString(final int childs) {
		final String var = "(- T_" + " " + mVar + ")";

		if (childs == 0) {
			return "( " + (((mLimits[0] & 1) == 0) ? " < " : " <= ") + var + " " + (mLimits[0] / 2) + ".0)";
		}

		if (childs == mLimits.length) {
			return "( " + (((mLimits[mLimits.length - 1] & 1) == 1) ? " > " : " >= ") + var + " "
					+ (mLimits[mLimits.length - 1] / 2) + ".0)";
		}

		if ((mLimits[childs - 1] / 2) == (mLimits[childs] / 2)) {
			return " (= " + var + " " + (mLimits[childs] / 2) + ".0)";
		}

		return "(and (" + (((mLimits[childs - 1] & 1) == 1) ? " < " : " <= ") + (mLimits[childs - 1] / 2) + ".0 " + var
				+ ") (" + (((mLimits[childs] & 1) == 0) ? " < " : ".0 <= ") + var + " " + (mLimits[childs] / 2)
				+ "0. ))";
	}

	public int getVal(final int childs) {
		if ((childs == 0) || (childs == 1)) {
			return (mLimits[0] / 2);
		}

		return -1;
	}

	public int getOp(final int childs) {
		if (childs == 0) {
			return (((mLimits[0] & 1) == 0) ? OP_LT : OP_LTEQ);
		}

		if (childs == mLimits.length) {
			// expects 1
			return (((mLimits[mLimits.length - 1] & 1) == 1) ? OP_GT : OP_GTEQ);
		}

		if ((mLimits[childs - 1] / 2) == (mLimits[childs] / 2)) {
			return OP_EQ;
		}

		return OP_INVALID;
	}

	/**
	 * @return Returns the var.
	 */
	@Override
	public String getVar() {
		return mVar;
	}

	/**
	 * @return Returns the limits.
	 */
	public int[] getLimits() {
		return mLimits;
	}

	@Override
	public RangeDecision prime(final Set<String> ignoreIds) {
		if (ignoreIds.contains(mVar)) {
			return this;
		}
		final String primed = mVar + BooleanDecision.PRIME_SUFFIX;
		final int[] limits = mLimits.clone();

		return new RangeDecision(primed, limits);
	}

	@Override
	public RangeDecision unprime(final Set<String> ignoreIds) {
		if (ignoreIds.contains(mVar)) {
			return this;
		}

		String unprimed = mVar;
		if (mVar.endsWith(BooleanDecision.PRIME_SUFFIX)) {
			unprimed = mVar.substring(0, mVar.length() - 1);
		}

		final int[] limits = mLimits.clone();

		return new RangeDecision(unprimed, limits);
	}

	@Override
	public int compareToSimilar(final Decision<?> other) {
		return mVar.compareTo(((RangeDecision) other).mVar);
	}

}
