package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.Transformations.AvailableTransformations;
import junit.framework.TestCase;

public class RPITest extends TestCase {
	
	private static class ProofDAGCheck {
		private ArrayDeque<Clause> m_Todo = new ArrayDeque<Clause>();
		private HashSet<Clause> m_Seen;
		public boolean check(Queue<Clause> expected, Clause proof) {
			m_Seen = new HashSet<Clause>();
			m_Todo.add(proof);
			while (!m_Todo.isEmpty()) {
				Clause tmp = m_Todo.pop();
				Clause exp = expected.poll();
				if (!clauseEqual(tmp, exp)) {
					System.err.println("Expected " + exp);
					System.err.println("Got " + tmp);
					return false;
				}
				if (m_Seen.add(tmp)) {
					ProofNode pn = tmp.getProof();
					if (!pn.isLeaf()) {
						ResolutionNode rn = (ResolutionNode) pn;
						m_Todo.push(rn.getPrimary());
						for (Antecedent a : rn.getAntecedents())
							m_Todo.push(a.antecedent);
					}
				}
			}
			return true;
		}
		private static final boolean clauseEqual(Clause c1, Clause c2) {
			if (c1.getSize() != c2.getSize())
				return false;
			HashSet<Literal> l1 = new HashSet<Literal>();
			for (int i = 0; i < c1.getSize(); ++i)
				l1.add(c1.getLiteral(i));
			for (int i = 0; i < c2.getSize(); ++i)
				if (!l1.remove(c2.getLiteral(i)))
					return false;
			return l1.isEmpty();
		}
	}
	
	private static class DummyAtom extends DPLLAtom {
		private String m_Name;
		public DummyAtom(String name) {
			super(name.hashCode(), 0);
			m_Name = name;
		}

		@Override
		public Term getSMTFormula(Theory smtTheory, boolean quoted) {
			throw new InternalError("Bug in testcase");
		}
		public String toString() {
			return m_Name;
		}
	}
	
	DPLLAtom a,b,c,d;
	Clause[] etas;
	
	public RPITest() {
		a = new DummyAtom("a");
		b = new DummyAtom("b");
		c = new DummyAtom("c");
		d = new DummyAtom("d");
		etas = new Clause[] {
				new Clause(new Literal[] {a.negate()}),
				new Clause(new Literal[] {a,c,b.negate()}),
				new Clause(new Literal[] {a,b}),
				new Clause(new Literal[] {b}),
				new Clause(new Literal[] {a,c}),
				new Clause(new Literal[] {c}),
				new Clause(new Literal[] {a,b.negate(),c.negate()}),
				new Clause(new Literal[] {a,c.negate()}),
				new Clause(new Literal[] {c.negate()})
		};
	}
	
	public void testRPIPaperExample() {
		// Build proof
		etas[0].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta1", null)));
		etas[1].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta2", null)));
		etas[2].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta3", null)));
		etas[6].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta7", null)));
		etas[3].setProof(new ResolutionNode(
				etas[0], new Antecedent[] {new Antecedent(a, etas[2])}));
		etas[4].setProof(new ResolutionNode(
				etas[1], new Antecedent[] {new Antecedent(b, etas[3])}));
		etas[5].setProof(new ResolutionNode(
				etas[0], new Antecedent[] {new Antecedent(a, etas[4])}));
		// Spare etas[7] by proof compression
		etas[8].setProof(new ResolutionNode(
				etas[3], new Antecedent[] {new Antecedent(b.negate(), etas[6]),
						new Antecedent(a.negate(), etas[0])}));
		Clause empty = new Clause(new Literal[0], new ResolutionNode(etas[5],
				new Antecedent[] { new Antecedent(c.negate(), etas[8])}));
		Clause transformed = AvailableTransformations.RPI.transform(empty);
		ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		Queue<Clause> input = new ArrayDeque<Clause>();
		input.add(empty);
		input.add(etas[8]);
		input.add(etas[0]);
		input.add(etas[6]);
		input.add(etas[3]);
		input.add(etas[2]);
		input.add(etas[0]);
		input.add(etas[5]);
		input.add(etas[4]);
		input.add(etas[3]);
		input.add(etas[1]);
		input.add(etas[0]);
		boolean checkDAGCheck = pdc.check(input, empty);
		assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(etas[8]);
		input.add(etas[0]);
		input.add(etas[6]);
		input.add(etas[2]);
		input.add(etas[5]);
		input.add(etas[4]);
		input.add(etas[2]);
		input.add(etas[1]);
		input.add(etas[0]);
		boolean check = new ProofDAGCheck().check(input, transformed);
		assertTrue(check);
	}
	
	public void testRPIPaperMod() {
		// Build proof
		etas[0].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta1", null)));
		etas[1].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta2", null)));
		etas[2].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta3", null)));
		etas[6].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta7", null)));
		etas[3].setProof(new ResolutionNode(
				etas[0], new Antecedent[] {new Antecedent(a, etas[2])}));
		etas[4].setProof(new ResolutionNode(
				etas[0], new Antecedent[] {new Antecedent(a, etas[2]),
						new Antecedent(b.negate(), etas[1])}));
//		etas[5].setProof(new ResolutionNode(
//				etas[0], new Antecedent[] {new Antecedent(a, etas[4])}));
		// Spare etas[7] by proof compression
		etas[8].setProof(new ResolutionNode(
				etas[3], new Antecedent[] {new Antecedent(b.negate(), etas[6]),
						new Antecedent(a.negate(), etas[0])}));
		Antecedent[] antes = new Antecedent[] {
				new Antecedent(a.negate(), etas[0]),
				new Antecedent(c.negate(), etas[8])
		};
		Clause empty = new Clause(new Literal[0], new ResolutionNode(etas[4],
				antes));
		Clause transformed = AvailableTransformations.RPI.transform(empty);
		ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		Queue<Clause> input = new ArrayDeque<Clause>();
		input.add(empty);
		input.add(etas[8]);
		input.add(etas[0]);
		input.add(etas[6]);
		input.add(etas[3]);
		input.add(etas[2]);
		input.add(etas[0]);
		input.add(etas[0]);
		input.add(etas[4]);
		input.add(etas[1]);
		input.add(etas[2]);
		input.add(etas[0]);
		boolean checkDAGCheck = pdc.check(input, empty);
		assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(etas[8]);
		input.add(etas[0]);
		input.add(etas[6]);
		input.add(etas[2]);
		input.add(etas[0]);
		input.add(etas[4]);
		input.add(etas[1]);
		input.add(etas[2]);
		boolean check = new ProofDAGCheck().check(input, transformed);
		assertTrue(check);
	}
	
	public void testRPIPaperModElimEta4() {
		// Build proof
		etas[0].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta1", null)));
		etas[1].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta2", null)));
		etas[2].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta3", null)));
		etas[6].setProof(new LeafNode(LeafNode.NO_THEORY,
				new SourceAnnotation("eta7", null)));
//		etas[3].setProof(new ResolutionNode(
//				etas[0], new Antecedent[] {new Antecedent(a, etas[2])}));
		etas[4].setProof(new ResolutionNode(
				etas[0], new Antecedent[] {new Antecedent(a, etas[2]),
						new Antecedent(b.negate(), etas[1])}));
//		etas[5].setProof(new ResolutionNode(
//				etas[0], new Antecedent[] {new Antecedent(a, etas[4])}));
		etas[7].setProof(new ResolutionNode(etas[0], new Antecedent[] {
				new Antecedent(a, etas[2]),
				new Antecedent(b.negate(), etas[6])
		}));
		etas[8].setProof(new ResolutionNode(
				etas[7], new Antecedent[] {
						new Antecedent(a.negate(), etas[0])
				}));
		Antecedent[] antes = new Antecedent[] {
				new Antecedent(a.negate(), etas[0]),
				new Antecedent(c.negate(), etas[8])
		};
		Clause empty = new Clause(new Literal[0], new ResolutionNode(etas[4],
				antes));
		Clause transformed = AvailableTransformations.RPI.transform(empty);
		ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		Queue<Clause> input = new ArrayDeque<Clause>();
		input.add(empty);
		input.add(etas[8]);
		input.add(etas[0]);
		input.add(etas[7]);
		input.add(etas[6]);
		input.add(etas[2]);
		input.add(etas[0]);
		input.add(etas[0]);
		input.add(etas[4]);
		input.add(etas[1]);
		input.add(etas[2]);
		input.add(etas[0]);
		boolean checkDAGCheck = pdc.check(input, empty);
		assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(etas[8]);
		input.add(etas[0]);
		input.add(etas[7]);
		input.add(etas[6]);
		input.add(etas[2]);
		input.add(etas[0]);
		input.add(etas[4]);
		input.add(etas[1]);
		input.add(etas[2]);
		boolean check = new ProofDAGCheck().check(input, transformed);
		assertTrue(check);
	}
	
	public void testNewExample() {
		Clause nega = new Clause(new Literal[]{a.negate()},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("nega", null)));
		Clause negb = new Clause(new Literal[]{b.negate()},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("negb", null)));
		Clause ab = new Clause(new Literal[]{a, b},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("ab", null)));
		Clause negbc = new Clause(new Literal[]{b.negate(), c},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("negbc", null)));
		Clause bnegc = new Clause(new Literal[]{b, c.negate()},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("bnegc", null)));
		Clause ac = new Clause(new Literal[]{a, c},
				new ResolutionNode(ab, new Antecedent[] {
						new Antecedent(b.negate(), negbc)
				}));
		Clause empty = new Clause(new Literal[0],
				new ResolutionNode(bnegc, new Antecedent[] {
					new Antecedent(c, ac),
					new Antecedent(b.negate(), negb),
					new Antecedent(a.negate(), nega)
				}));
		Clause transformed = AvailableTransformations.RPI.transform(empty);
		ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		Queue<Clause> input = new ArrayDeque<Clause>();
		input.add(empty);
		input.add(nega);
		input.add(negb);
		input.add(ac);
		input.add(negbc);
		input.add(ab);
		input.add(bnegc);
		boolean checkDAGCheck = pdc.check(input, empty);
		assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(nega);
		input.add(negb);
		input.add(ab);
		boolean check = new ProofDAGCheck().check(input, transformed);
		assertTrue(check);
	}

	public void testNewExample2() {
		Clause nega = new Clause(new Literal[]{a.negate()},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("nega", null)));
		Clause negb = new Clause(new Literal[]{b.negate()},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("negb", null)));
		Clause ab = new Clause(new Literal[]{a, b},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("ab", null)));
		Clause negbc = new Clause(new Literal[]{b.negate(), c},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("negbc", null)));
		Clause bnegc = new Clause(new Literal[]{b, c.negate()},
				new LeafNode(LeafNode.NO_THEORY,
						new SourceAnnotation("bnegc", null)));
		Clause ac = new Clause(new Literal[]{a, c},
				new ResolutionNode(ab, new Antecedent[] {
						new Antecedent(b.negate(), negbc)
				}));
		Clause empty = new Clause(new Literal[0],
				new ResolutionNode(ac, new Antecedent[] {
					new Antecedent(c.negate(), bnegc),
					new Antecedent(b.negate(), negb),
					new Antecedent(a.negate(), nega)
				}));
		Clause transformed = AvailableTransformations.RPI.transform(empty);
		ProofDAGCheck pdc = new ProofDAGCheck();
		// Sanity check
		Queue<Clause> input = new ArrayDeque<Clause>();
		input.add(empty);
		input.add(nega);
		input.add(negb);
		input.add(bnegc);
		input.add(ac);
		input.add(negbc);
		input.add(ab);
		boolean checkDAGCheck = pdc.check(input, empty);
		assertTrue(checkDAGCheck);
		input.clear();
		input.add(empty);
		input.add(nega);
		input.add(negb);
		input.add(ab);
		boolean check = new ProofDAGCheck().check(input, transformed);
		assertTrue(check);
	}
	
}
