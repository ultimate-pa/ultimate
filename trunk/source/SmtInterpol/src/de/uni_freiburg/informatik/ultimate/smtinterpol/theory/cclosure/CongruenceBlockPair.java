/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.util.UnifyHash;

public class CongruenceBlockPair {
	private static UnifyHash<CongruenceBlockPair> g_unifier;
	public static CongruenceBlockPair getRootPair(CCAppTerm t) {
		return getPair(t.func.repStar, t.arg.repStar);
	}
	public static CongruenceBlockPair getPair(CCAppTerm t) {
		return getPair(t.func, t.arg);
	}
	public static CongruenceBlockPair getPair(CCTerm func, CCTerm arg) {
		int hash = hash(func,arg);
		if (g_unifier == null)
			g_unifier = new UnifyHash<CongruenceBlockPair>();
		else {
			for (CongruenceBlockPair p : g_unifier.iterateHashCode(hash)) {
				if (p.equals(func, arg)) {
					return p;
				}
			}
		}
		CongruenceBlockPair res = new CongruenceBlockPair(func, arg);
		g_unifier.put(hash, res);
		return res;
	}
	private static int hash(CCTerm t1,CCTerm t2) {
		return t1.hashCode() + 9337 * t2.hashCode();
	}
	private CCTerm m_Func,m_Arg;
	private CongruenceBlockPair(CCTerm func, CCTerm arg) {
		m_Func = func;
		m_Arg = arg;
	}
	public int hashCode() {
		return hash(m_Func,m_Arg);
	}
	public boolean equals(Object o) {
		if (o instanceof CongruenceBlockPair) {
			CongruenceBlockPair p = (CongruenceBlockPair) o;
			return p.equals(p.m_Func,p.m_Arg);
		}
		return false;
	}
	public boolean equals(CCTerm func, CCTerm arg) {
		return m_Func == func && m_Arg == arg;
	}
	public CongruenceBlockPair getRoot() {
		return getPair(m_Func.repStar, m_Arg.repStar);
	}
}
