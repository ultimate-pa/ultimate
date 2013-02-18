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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;

/**
 * Helper to unify instantiations of a quantifier over different YieldTrigger.
 * @author Juergen Christ
 */
public class InstantiationUnifier {
	
//	static long unificationTime = 0;
//	static int preventedInsts = 0;
	
	private static class Signature {
		private CCTerm[] m_sig;
		private int m_hash;
		public Signature(CCTerm[] sig) {
			assert(sig != null);
			m_sig = sig;
			m_hash = Arrays.hashCode(m_sig);
		}
		public int hashCode() {
			return m_hash;
		}
		public boolean equals(Object o) {
			if (o instanceof Signature) {
				Signature other = (Signature)o;
				return m_hash == o.hashCode() && Arrays.equals(m_sig, other.m_sig);
			}
			return false;
		}
		public String toString() {
			return Arrays.toString(m_sig);
		}
	}
	
	private HashSet<Signature> m_knownSigs = new HashSet<Signature>();
	protected TermVariable[] m_vars;
	public InstantiationUnifier(TermVariable... vars) {
		m_vars = vars;
		// FIXME Remove this stuff once we are sure about multiple instantiations.
//		Runtime.getRuntime().addShutdownHook(new Thread() {
//			public void run() {
//				System.err.println("Unification Time: " + unificationTime);
//				System.err.println("Prevented Insts: " + preventedInsts);
//			}
//		});
	}
	public InstantiationUnifier(Set<TermVariable> vars) {
		this(vars.toArray(new TermVariable[vars.size()]));
	}
	protected CCTerm[] buildSignature(CCTerm[] regs,
			Map<TermVariable,Integer> subst) {
		CCTerm[] sig = new CCTerm[m_vars.length];
		for (int i = 0; i < m_vars.length; ++i) {
			sig[i] = regs[subst.get(m_vars[i])];
		}
		return sig;
	}
	/**
	 * Check whether a new instantiation should be created.
	 * @param regs		The registers for the Yield instruction.
	 * @param subst		The substitution map of the yield instruction.
	 * @param logger	Logger to debug known signatures.
	 * @param sub		Quantifier subformula used to print debug message.
	 * @return <code>true</code> if a new instantiation should be produced.
	 */
	public boolean createInstantiation(CCTerm[] regs,
			Map<TermVariable,Integer> subst,Logger logger,Term sub) {
		Signature sig = new Signature(buildSignature(regs, subst));
//		long time = System.nasnoTime();
		if (!m_knownSigs.add(sig)) {
//			unificationTime += System.nanoTime() - time;
//			++preventedInsts;
			if (logger.isDebugEnabled())
				logger.debug("Instantiation already known: " + sig);
			return false;
		}
//		unificationTime += System.nanoTime() - time;
		if (logger.isDebugEnabled())
			logger.debug("Instantiating " + sub + " with " + sig);
//		System.err.println("Instantiating " + sub + " with " + sig);
		return true;
	}
}
