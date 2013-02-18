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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


/**
 * Node in the proof tree representing a hyper resolution step.
 * @author Juergen Christ
 */
public class ResolutionNode extends ProofNode {
	/**
	 * This is actually a pair of pivot and antecedent.
	 * @author Juergen Christ
	 */
	public static class Antecedent {
		public final Literal pivot;
		public final Clause antecedent;
		
		/**
		 * Create an pivot/antecedent entry for a resolution node.
		 * The pivot must occur with the same polarity in the antecedent clause.
		 * @param pivot
		 * @param antecedent
		 */
		public Antecedent(Literal pivot, Clause antecedent) {
			assert(pivot != null);
			assert(antecedent != null);
			assert(antecedent.contains(pivot));
			this.pivot = pivot;
			this.antecedent = antecedent;
		}
		public String toString() {
			return pivot.toString() + " => " + antecedent;
		}
	}
	/// Primary conflict target
	private Clause m_primary;
	/// Our antecedents of the hyper resolution.
	private Antecedent[] m_antecedents;
	
	public ResolutionNode(Clause primary, Antecedent[] antecedents) {
		assert(primary != null);
		m_primary = primary;
		m_antecedents = antecedents;
	}
	
	@Override
	public boolean isLeaf() {
		return false;
	}
	public Clause getPrimary() {
		return m_primary;
	}
	/**
	 * Get the antecedents of this proof node. Result will be <code>null</code>
	 * if this node corresponds to a leaf in the proof tree.
	 * @return Antecedents or <code>null</code>.
	 */
	public Antecedent[] getAntecedents() {
		return m_antecedents;
	}
	
	public String toString() {
		return m_primary + " => " + Arrays.toString(m_antecedents);
	}

}
