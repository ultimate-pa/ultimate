/*
 * Copyright (C) 2012-2013 University of Freiburg
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
import java.util.Queue;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.Transformations.AvailableTransformations;

@RunWith(JUnit4.class)
public class RPITest {

	private static class DummyAtom extends DPLLAtom {
		private final String mName;

		public DummyAtom(final String name) {
			super(name.hashCode(), 0);
			mName = name;
		}

		@Override
		public Term getSMTFormula(final Theory smtTheory, final boolean quoted) {
			throw new InternalError("Bug in testcase");
		}

		@Override
		public String toString() {
			return mName;
		}
	}

	private static class ProofDAGCheck {
		private static final boolean clauseEqual(final Clause c1, final Clause c2) {
			if (c1.getSize() != c2.getSize()) {
				return false;
			}
			final HashSet<Literal> l1 = new HashSet<>();
			for (int i = 0; i < c1.getSize(); ++i) {
				l1.add(c1.getLiteral(i));
			}
			for (int i = 0; i < c2.getSize(); ++i) {
				if (!l1.remove(c2.getLiteral(i))) {
					return false;
				}
			}
			return l1.isEmpty();
		}

		private final ArrayDeque<Clause> mTodo = new ArrayDeque<>();
		private HashSet<Clause> mSeen;

		public boolean check(final Queue<Clause> expected, final Clause proof) {
			mSeen = new HashSet<>();
			mTodo.add(proof);
			while (!mTodo.isEmpty()) {
				final Clause tmp = mTodo.pop();
				final Clause exp = expected.poll();
				if (!clauseEqual(tmp, exp)) {
					System.err.println("Expected " + exp);
					System.err.println("Got " + tmp);
					return false;
				}
				if (mSeen.add(tmp)) {
					final ProofNode pn = tmp.getProof();
					if (!pn.isLeaf()) {
						final ResolutionNode rn = (ResolutionNode) pn;
						mTodo.push(rn.getPrimary());
						for (final Antecedent a : rn.getAntecedents()) {
							mTodo.push(a.mAntecedent);
						}
					}
				}
			}
			return true;
		}
	}

	DPLLAtom mA, mB, mC, mD;
	Clause[] mEtas;

	public RPITest() {
		mA = new DummyAtom("a");
		mB = new DummyAtom("b");
		mC = new DummyAtom("c");
		mD = new DummyAtom("d");
		mEtas = new Clause[] { new Clause(new Literal[] { mA.negate() }),
				new Clause(new Literal[] { mA, mC, mB.negate() }), new Clause(new Literal[] { mA, mB }),
				new Clause(new Literal[] { mB }), new Clause(new Literal[] { mA, mC }),
				new Clause(new Literal[] { mC }), new Clause(new Literal[] { mA, mB.negate(), mC.negate() }),
				new Clause(new Literal[] { mA, mC.negate() }), new Clause(new Literal[] { mC.negate() }) };
	}

	@Test
	public void testNewExample() {
		final Clause nega = new Clause(new Literal[] { mA.negate() },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("nega", null)));
		final Clause negb = new Clause(new Literal[] { mB.negate() },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("negb", null)));
		final Clause ab = new Clause(new Literal[] { mA, mB },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("ab", null)));
		final Clause negbc = new Clause(new Literal[] { mB.negate(), mC },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("negbc", null)));
		final Clause bnegc = new Clause(new Literal[] { mB, mC.negate() },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("bnegc", null)));
		final Clause ac = new Clause(new Literal[] { mA, mC },
				new ResolutionNode(ab, new Antecedent[] { new Antecedent(mB.negate(), negbc) }));
		final Clause empty = new Clause(new Literal[0], new ResolutionNode(bnegc, new Antecedent[] {
				new Antecedent(mC, ac), new Antecedent(mB.negate(), negb), new Antecedent(mA.negate(), nega) }));
		final Clause transformed = AvailableTransformations.RPI.transform(empty);
		final ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		final Queue<Clause> input = new ArrayDeque<>();
		input.add(empty);
		input.add(nega);
		input.add(negb);
		input.add(ac);
		input.add(negbc);
		input.add(ab);
		input.add(bnegc);
		final boolean checkDAGCheck = pdc.check(input, empty);
		Assert.assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(nega);
		input.add(negb);
		input.add(ab);
		final boolean check = new ProofDAGCheck().check(input, transformed);
		Assert.assertTrue(check);
	}

	@Test
	public void testNewExample2() {
		final Clause nega = new Clause(new Literal[] { mA.negate() },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("nega", null)));
		final Clause negb = new Clause(new Literal[] { mB.negate() },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("negb", null)));
		final Clause ab = new Clause(new Literal[] { mA, mB },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("ab", null)));
		final Clause negbc = new Clause(new Literal[] { mB.negate(), mC },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("negbc", null)));
		final Clause bnegc = new Clause(new Literal[] { mB, mC.negate() },
				new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("bnegc", null)));
		final Clause ac = new Clause(new Literal[] { mA, mC },
				new ResolutionNode(ab, new Antecedent[] { new Antecedent(mB.negate(), negbc) }));
		final Clause empty =
				new Clause(new Literal[0], new ResolutionNode(ac, new Antecedent[] { new Antecedent(mC.negate(), bnegc),
						new Antecedent(mB.negate(), negb), new Antecedent(mA.negate(), nega) }));
		final Clause transformed = AvailableTransformations.RPI.transform(empty);
		final ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		final Queue<Clause> input = new ArrayDeque<>();
		input.add(empty);
		input.add(nega);
		input.add(negb);
		input.add(bnegc);
		input.add(ac);
		input.add(negbc);
		input.add(ab);
		final boolean checkDAGCheck = pdc.check(input, empty);
		Assert.assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(nega);
		input.add(negb);
		input.add(ab);
		final boolean check = new ProofDAGCheck().check(input, transformed);
		Assert.assertTrue(check);
	}

	@Test
	public void testRPIPaperExample() {
		// Build proof
		mEtas[0].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta1", null)));
		mEtas[1].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta2", null)));
		mEtas[2].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta3", null)));
		mEtas[6].setProof(new LeafNode(LeafNode.NO_THEORY, // NOCHECKSTYLE
				new SourceAnnotation("eta7", null)));
		mEtas[3].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[0], new Antecedent[] { new Antecedent(mA, mEtas[2]) }));// NOCHECKSTYLE
		mEtas[4].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[1], new Antecedent[] { new Antecedent(mB, mEtas[3]) }));// NOCHECKSTYLE
		mEtas[5].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[0], new Antecedent[] { new Antecedent(mA, mEtas[4]) }));// NOCHECKSTYLE
		// Spare etas[7] by proof compression
		mEtas[8].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[3], new Antecedent[] { // NOCHECKSTYLE
						new Antecedent(mB.negate(), mEtas[6]), // NOCHECKSTYLE
						new Antecedent(mA.negate(), mEtas[0]) }));
		final Clause empty = new Clause(new Literal[0], new ResolutionNode(mEtas[5], // NOCHECKSTYLE
				new Antecedent[] { new Antecedent(mC.negate(), mEtas[8]) }));// NOCHECKSTYLE
		final Clause transformed = AvailableTransformations.RPI.transform(empty);
		final ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		final Queue<Clause> input = new ArrayDeque<>();
		input.add(empty);
		input.add(mEtas[8]);// NOCHECKSTYLE
		input.add(mEtas[0]);
		input.add(mEtas[6]);// NOCHECKSTYLE
		input.add(mEtas[3]);// NOCHECKSTYLE
		input.add(mEtas[2]);
		input.add(mEtas[0]);
		input.add(mEtas[5]);// NOCHECKSTYLE
		input.add(mEtas[4]);// NOCHECKSTYLE
		input.add(mEtas[3]);// NOCHECKSTYLE
		input.add(mEtas[1]);
		input.add(mEtas[0]);
		final boolean checkDAGCheck = pdc.check(input, empty);
		Assert.assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(mEtas[8]);// NOCHECKSTYLE
		input.add(mEtas[0]);
		input.add(mEtas[6]);// NOCHECKSTYLE
		input.add(mEtas[2]);
		input.add(mEtas[5]);// NOCHECKSTYLE
		input.add(mEtas[4]);// NOCHECKSTYLE
		input.add(mEtas[2]);
		input.add(mEtas[1]);
		input.add(mEtas[0]);
		final boolean check = new ProofDAGCheck().check(input, transformed);
		Assert.assertTrue(check);
	}

	@Test
	public void testRPIPaperMod() {
		// Build proof
		mEtas[0].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta1", null)));
		mEtas[1].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta2", null)));
		mEtas[2].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta3", null)));
		mEtas[6].setProof(new LeafNode(LeafNode.NO_THEORY, // NOCHECKSTYLE
				new SourceAnnotation("eta7", null)));
		mEtas[3].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[0], new Antecedent[] { new Antecedent(mA, mEtas[2]) }));
		mEtas[4].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[0], new Antecedent[] { new Antecedent(mA, mEtas[2]), new Antecedent(mB.negate(), mEtas[1]) }));
		// etas[5].setProof(new ResolutionNode(
		// etas[0], new Antecedent[] {new Antecedent(a, etas[4])}));
		// Spare etas[7] by proof compression
		mEtas[8].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[3], new Antecedent[] { // NOCHECKSTYLE
						new Antecedent(mB.negate(), mEtas[6]), // NOCHECKSTYLE
						new Antecedent(mA.negate(), mEtas[0]) }));
		final Antecedent[] antes =
				new Antecedent[] { new Antecedent(mA.negate(), mEtas[0]), new Antecedent(mC.negate(), mEtas[8])// NOCHECKSTYLE
				};
		final Clause empty = new Clause(new Literal[0], new ResolutionNode(mEtas[4], // NOCHECKSTYLE
				antes));
		final Clause transformed = AvailableTransformations.RPI.transform(empty);
		final ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		final Queue<Clause> input = new ArrayDeque<>();
		input.add(empty);
		input.add(mEtas[8]);// NOCHECKSTYLE
		input.add(mEtas[0]);
		input.add(mEtas[6]);// NOCHECKSTYLE
		input.add(mEtas[3]);// NOCHECKSTYLE
		input.add(mEtas[2]);
		input.add(mEtas[0]);
		input.add(mEtas[0]);
		input.add(mEtas[4]);// NOCHECKSTYLE
		input.add(mEtas[1]);
		input.add(mEtas[2]);
		input.add(mEtas[0]);
		final boolean checkDAGCheck = pdc.check(input, empty);
		Assert.assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(mEtas[8]);// NOCHECKSTYLE
		input.add(mEtas[0]);
		input.add(mEtas[6]);// NOCHECKSTYLE
		input.add(mEtas[2]);
		input.add(mEtas[0]);
		input.add(mEtas[4]);// NOCHECKSTYLE
		input.add(mEtas[1]);
		input.add(mEtas[2]);
		final boolean check = new ProofDAGCheck().check(input, transformed);
		Assert.assertTrue(check);
	}

	@Test
	public void testRPIPaperModElimEta4() {
		// Build proof
		mEtas[0].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta1", null)));
		mEtas[1].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta2", null)));
		mEtas[2].setProof(new LeafNode(LeafNode.NO_THEORY, new SourceAnnotation("eta3", null)));
		mEtas[6].setProof(new LeafNode(LeafNode.NO_THEORY, // NOCHECKSTYLE
				new SourceAnnotation("eta7", null)));
		// etas[3].setProof(new ResolutionNode(
		// etas[0], new Antecedent[] {new Antecedent(a, etas[2])}));
		mEtas[4].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[0], new Antecedent[] { new Antecedent(mA, mEtas[2]), new Antecedent(mB.negate(), mEtas[1]) }));
		// etas[5].setProof(new ResolutionNode(
		// etas[0], new Antecedent[] {new Antecedent(a, etas[4])}));
		mEtas[7].setProof(new ResolutionNode(mEtas[0], new Antecedent[] { // NOCHECKSTYLE
				new Antecedent(mA, mEtas[2]), new Antecedent(mB.negate(), mEtas[6])// NOCHECKSTYLE
		}));
		mEtas[8].setProof(new ResolutionNode(// NOCHECKSTYLE
				mEtas[7], new Antecedent[] { // NOCHECKSTYLE
						new Antecedent(mA.negate(), mEtas[0]) }));
		final Antecedent[] antes =
				new Antecedent[] { new Antecedent(mA.negate(), mEtas[0]), new Antecedent(mC.negate(), mEtas[8])// NOCHECKSTYLE
				};
		final Clause empty = new Clause(new Literal[0], new ResolutionNode(mEtas[4], // NOCHECKSTYLE
				antes));
		final Clause transformed = AvailableTransformations.RPI.transform(empty);
		final ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		final Queue<Clause> input = new ArrayDeque<>();
		input.add(empty);
		input.add(mEtas[8]);// NOCHECKSTYLE
		input.add(mEtas[0]);
		input.add(mEtas[7]);// NOCHECKSTYLE
		input.add(mEtas[6]);// NOCHECKSTYLE
		input.add(mEtas[2]);
		input.add(mEtas[0]);
		input.add(mEtas[0]);
		input.add(mEtas[4]);// NOCHECKSTYLE
		input.add(mEtas[1]);
		input.add(mEtas[2]);
		input.add(mEtas[0]);
		final boolean checkDAGCheck = pdc.check(input, empty);
		Assert.assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(mEtas[8]);// NOCHECKSTYLE
		input.add(mEtas[0]);
		input.add(mEtas[7]);// NOCHECKSTYLE
		input.add(mEtas[6]);// NOCHECKSTYLE
		input.add(mEtas[2]);
		input.add(mEtas[0]);
		input.add(mEtas[4]);// NOCHECKSTYLE
		input.add(mEtas[1]);
		input.add(mEtas[2]);
		final boolean check = new ProofDAGCheck().check(input, transformed);
		Assert.assertTrue(check);
	}

}
