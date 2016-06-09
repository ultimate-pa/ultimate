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

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

/**
 * Collection of proof tree transformations.  The algorithms are taken from 
 * Fontaine, Merz, Woltzenlogel Paleo, "Compression of Propositional Resolution
 * Proofs via Partial Regularization"
 * @author Juergen Christ
 */
public final class Transformations {
    
    private Transformations() {
        // Hide constructor
    }
    
	public static enum AvailableTransformations {
		NONE {

			@Override
			public Clause transform(Clause proof) {
				return proof;
			}
			
		},
		LU {

			@Override
			public Clause transform(Clause proof) {
				return Transformations.lowerUnits(proof);
			}
			
		},
		RPI {

			@Override
			public Clause transform(Clause proof) {
				return Transformations.recycleUnits(proof);
			}
			
		},
		RPILU {

			@Override
			public Clause transform(Clause proof) {
				return Transformations.lowerUnits(
						Transformations.recycleUnits(proof));
			}
			
		},
		LURPI {

			@Override
			public Clause transform(Clause proof) {
				return Transformations.recycleUnits(
						Transformations.lowerUnits(proof));
			}
			
		};
		public abstract Clause transform(Clause proof);
	}
	/**
	 * Lower the unit resolutions.
	 * @param proof The proof tree.
	 * @return New proof tree with units lowered.
	 */
	public static Clause lowerUnits(Clause proof) {
		assert proof.getSize() == 0;
		OccurrenceCounter occ = new OccurrenceCounter();
		Map<Clause, Integer> counts = occ.count(proof);
		occ = null; // done with it
		UnitCollector uc = new UnitCollector();
		Queue<Antecedent> units = uc.collectUnits(proof, counts);
		Map<Clause, Set<Literal>> deletedNodes = uc.getDeletedNodes();
		uc = null; // done with it
		FixProofDAG fix = new FixProofDAG();
		final Clause tmpproof = fix.fix(proof, deletedNodes);
		final ArrayDeque<Antecedent> fixedUnits =
			new ArrayDeque<Antecedent>(units.size());
		while (!units.isEmpty()) {
			final Antecedent a = units.remove();
			fixedUnits.add(new Antecedent(a.mPivot,
					fix.fix(a.mAntecedent, deletedNodes)));
		}
		// Clear space
		counts = null;
		units = null;
		deletedNodes = null;
		fix = null;
		// Track literals in the hyper-resolution
		final HashSet<Literal> lits = new HashSet<Literal>();
		for (int i = 0; i < tmpproof.getSize(); ++i) {
			lits.add(tmpproof.getLiteral(i));
		}
		if (lits.isEmpty()) {
			return tmpproof;
		}
		// Reinsert unit literals
		Antecedent[] antes = new Antecedent[fixedUnits.size()];
		int antepos = 0;
		while (!fixedUnits.isEmpty()) {
			final Antecedent unit = fixedUnits.remove();
			if (lits.contains(unit.mPivot.negate())) {
				antes[antepos++] = unit;
				lits.remove(unit.mPivot.negate());
				for (int i = 0; i < unit.mAntecedent.getSize(); ++i) {
					final Literal l = unit.mAntecedent.getLiteral(i);
					if (l != unit.mPivot) {
						lits.add(l);
					}
				}
			}
		}
		if (antepos < antes.length) {
			final Antecedent[] tmp = new Antecedent[antepos];
			System.arraycopy(antes, 0, tmp, 0, antepos);
			antes = tmp;
		}
		assert lits.isEmpty();
		return new Clause(new Literal[0], new ResolutionNode(tmpproof, antes));
	}
	/**
	 * Recycle resolution pivots.
	 * @param proof The proof tree.
	 * @return New proof tree.
	 */
	public static Clause recycleUnits(Clause proof) {
		assert proof.getSize() == 0;
		OccurrenceCounter occ = new OccurrenceCounter();
		final Map<Clause, Integer> counts = occ.count(proof);
		occ = null; // done with it
		RecyclePivots rp = new RecyclePivots();
		final Map<Clause, Set<Literal>> deleted = rp.regularize(proof, counts);
		rp = null; // done with it
		final FixProofDAG fix = new FixProofDAG();
		return fix.fix(proof, deleted);
	}
}
