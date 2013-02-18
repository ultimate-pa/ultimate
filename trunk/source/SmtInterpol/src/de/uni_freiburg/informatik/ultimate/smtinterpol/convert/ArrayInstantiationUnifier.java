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

import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;


/**
 * Special unifier for array axiom instantiations. This class should prevent a
 * match of <code>i!=j ==> select(store(a,i,v),j)=select(a,j)</code> after a
 * match of <code>select(store(a,i,v),i)</code> since this unnecessarily blows
 * up the clause set.
 * @author Juergen Christ
 */
public class ArrayInstantiationUnifier extends InstantiationUnifier {

	public ArrayInstantiationUnifier(TermVariable array,TermVariable i1,
			TermVariable i2,TermVariable elem) {
		// Just be sure about the order...
		super(array,i1,i2,elem);
	}
	
	@Override
	protected CCTerm[] buildSignature(CCTerm[] regs,
			Map<TermVariable, Integer> subst) {
		CCTerm[] sig = new CCTerm[4];
		sig[0] = regs[subst.get(m_vars[0])];
		int i1 = subst.get(m_vars[1]);
		sig[1] = regs[i1];
		Integer i2 = subst.get(m_vars[2]);
		// Put i1 in the signature for select(store(a,i,v),i)
		sig[2] = i2 == null ? regs[i1] : regs[i2];
		sig[3] = regs[subst.get(m_vars[3])];
		return sig;
	}

	@Override
	public boolean createInstantiation(CCTerm[] regs,
			Map<TermVariable, Integer> subst, Logger logger, Term sub) {
		// Prevent instantiation of i!=j => select(store(a,i,v),j)=select(a,j) with i=j
		Integer i2 = subst.get(m_vars[2]);
		if (i2 != null) {
			int i1 = subst.get(m_vars[1]);
			if (regs[i1] == regs[i2])
				return false;
		}
		return super.createInstantiation(regs, subst, logger, sub);
	}

}
