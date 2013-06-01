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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.BoundConstraint;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;


public class Interpolator {

	class Occurrence {
		BitSet m_inA;
		BitSet m_inB;

		public Occurrence() {
			m_inA = new BitSet(m_NumInterpolants+1);
			m_inB = new BitSet(m_NumInterpolants+1);
		}

		public Occurrence(BitSet inA, BitSet inB) {
			m_inA = inA;
			m_inB = inB;
		}

		public void occursIn(int partition) {
			for (int i = 0; i <= m_NumInterpolants; i++) {
				if (i < partition || m_startOfSubtrees[i] > partition)
					m_inB.set(i);
				else
					m_inA.set(i);
			}
		}

		public boolean isALocalInSomeChild(int partition) {
			for (int i = partition - 1; i >= m_startOfSubtrees[partition]; ) {
				if (m_inA.get(i))
					return true;
				i = m_startOfSubtrees[i] - 1;
			}
			return false;
		}

		public boolean contains(int partition) {
			if (!m_inA.get(partition))
				return false;
			if (m_inB.get(partition))
				return true;
			for (int i = partition - 1; i >= m_startOfSubtrees[partition]; ) {
				if (!m_inB.get(i))
					return false;
				i = m_startOfSubtrees[i] - 1;
			}
			return true;
		}

		public boolean isAorShared(int partition) {
			return m_inA.get(partition);
		}
		public boolean isBorShared(int partition) {
			return m_inB.get(partition);
		}
		public boolean isALocal(int partition) {
			return m_inA.get(partition) && !m_inB.get(partition);
		}
		public boolean isBLocal(int partition) {
			return m_inB.get(partition) && !m_inA.get(partition);
		}
		public boolean isAB(int partition) {
			return m_inA.get(partition) && m_inB.get(partition);
		}
		public boolean isMixed(int partition) {
			return !m_inA.get(partition) && !m_inB.get(partition);
		}

		public String toString() {
			return "[" + m_inA + "|" + m_inB + "]";
		}

		/**
		 * Find the first A-local colored node.  Every occurrence
		 * has a A-local chain from such a node to the root
		 * node and all other nodes are not A-local.
		 * @return the first A-local colored node.
		 */
		public int getALocalColor() {
			int color = m_inA.nextSetBit(0);
			if (m_inB.get(color)) {
				color = m_inB.nextClearBit(color);
			}
			return color;
		}
	}

	class LitInfo extends Occurrence {
		TermVariable m_MixedVar;
		/** Tells for an equality whether the A part is the Lhs or
		 * the Rhs.
		 */
		Occurrence m_lhsOccur;
		/** 
		 * Gives for an inequality the A part.
		 */
		MutableAffinTerm[] m_APart;

		public LitInfo() {
			super();
		}

		public LitInfo(BitSet inA, BitSet inB) {
			super(inA, inB);
		}

		public TermVariable getMixedVar() {
			return m_MixedVar;
		}

		public Occurrence getLhsOccur() {
			return m_lhsOccur;
		}

		public MutableAffinTerm getAPart(int p) {
			return m_APart[p];
		}
	}

	private static final boolean DEEP_CHECK_INTERPOLANTS = true;
	SMTInterpol m_SmtSolver;

	Logger m_Logger;
	Theory m_Theory;
	int m_NumInterpolants;
	/**
	 * Array encoding the tree-structure for tree interpolants.
	 * The interpolants are always required to be in post-order
	 * tree traversal.
	 * The i-th element of this array contains the lowest index
	 * occuring in the sub-tree with the i-th element as root node.
	 * This is the index of the lower left-most node in the sub-tree.
	 * The nodes between m_startOfSubtrees[i] and i form the sub-tree
	 * with the root i.
	 * 
	 * To traverse the children of a node the following pattern can
	 * be used:
	 * <pre>
	 * for (int child = node-1; child >= m_startOfSubtrees[node];
	 *      child = m_startOfSubtrees[child] - 1) {
	 *      ...
	 * }
	 * </pre>
	 * To find the parent of a node do:
	 * <pre>
	 * int parent = node + 1; 
	 * while (m_startOfSubtrees[parent] > node) parent++;
	 * </pre>
	 */
	int[] m_startOfSubtrees;
	HashMap<SharedTerm, Occurrence> m_SymbolPartition;
	HashMap<DPLLAtom, LitInfo> m_LiteralInfos;
	HashMap<String, Integer> m_Partitions;
	HashMap<Clause, Interpolant[]> m_Interpolants;
	
	

	public Interpolator(Logger logger, SMTInterpol smtSolver, Theory theory, 
			Set<String>[] partitions, int[] startOfSubTrees) {
		m_Partitions = new HashMap<String, Integer>();
		for (int i = 0; i < partitions.length; i++) {
			Integer part = i;
			for (String name: partitions[i]) {
				m_Partitions.put(name, part);
			}
		}
		m_Logger = logger;
		m_SmtSolver = smtSolver;
		m_Theory = theory;
		m_NumInterpolants = partitions.length - 1;

		m_startOfSubtrees = startOfSubTrees;
		m_SymbolPartition = new HashMap<SharedTerm, Occurrence>();
		m_LiteralInfos = new HashMap<DPLLAtom, LitInfo>();
		m_Interpolants = new HashMap<Clause,Interpolant[]>();
	}

	public Interpolator(Logger logger, Theory theory, 
			Set<String>[] partitions, Clausifier clausifier) {
		this(logger, null, theory, partitions, new int[partitions.length]);
	}

	private Term unfoldLAs(Interpolant interpolant) {
		TermTransformer substitutor = new TermTransformer() {
			public void convert(Term term) {
				if (term instanceof LATerm)
					term = ((LATerm) term).m_F;
				super.convert(term);
			}
		};
		return substitutor.transform(interpolant.m_term);
	}

	public Term[] getInterpolants(Clause refutation) {
		colorLiterals(refutation, new HashSet<Clause>());
		Interpolant[] eqitps = interpolate(refutation);
		Term[] itpTerms = new Term[eqitps.length];
		for (int i = 0; i < eqitps.length; i++) 
			itpTerms[i] = unfoldLAs(eqitps[i]);
		return itpTerms;
	}
	
	private void checkInductivity(Collection<Literal> clause, Interpolant[] ipls) {
		Level old = m_Logger.getLevel();
		m_Logger.setLevel(Level.ERROR);

		m_SmtSolver.push(1);
		
		/* initialize auxMaps, which maps for each partition the auxiliary
		 * variables for mixed literals to a new fresh constant.
		 */
		@SuppressWarnings("unchecked") // because Java Generics are broken :(
		HashMap<TermVariable, Term>[] auxMaps = new HashMap[ipls.length];
		
		for (Literal lit : clause) {
			LitInfo info = getLiteralInfo(lit.getAtom());
			for (int part = 0; part < ipls.length; part++) {
				if (info.isMixed(part)) {
					TermVariable tv = info.m_MixedVar;
					String name = ".check"+part+"."+tv.getName();
					m_SmtSolver.declareFun(name, new Sort[0], tv.getSort());
					Term term = m_SmtSolver.term(name);
					if (auxMaps[part] == null)
						auxMaps[part] = new HashMap<TermVariable, Term>();
					auxMaps[part].put(tv, term);
				}
			}
		}
		Term[] interpolants = new Term[ipls.length];
		for (int part = 0; part < ipls.length; part++) {
			Term ipl = unfoldLAs(ipls[part]);
			if (auxMaps[part] != null) {
				TermVariable[] tvs = new TermVariable[auxMaps[part].size()];
				Term[] values = new Term[auxMaps[part].size()];
				int i = 0;
				for (Entry<TermVariable, Term> entry : auxMaps[part].entrySet()) {
					tvs[i] = entry.getKey();
					values[i] = entry.getValue();
					i++;
				}
				interpolants[part] = m_Theory.let(tvs, values, ipl);
			} else {
				interpolants[part] = ipl;
			}
		}
		
		
		for (int part = 0; part < ipls.length; part++) {
			m_SmtSolver.push(1);
			for (Entry<String, Integer> entry: m_Partitions.entrySet()) {
				if (entry.getValue() == part)
					m_SmtSolver.assertTerm(m_Theory.term(entry.getKey()));
			}
			for (Literal lit : clause) {
				lit = lit.negate();
				LitInfo info = m_LiteralInfos.get(lit.getAtom());
				if (info.contains(part)) {
					m_SmtSolver.assertTerm(lit.getSMTFormula(m_Theory));
				} else if (info.isBLocal(part)) {
					// nothing to do, literal cannot be mixed in sub-tree.
				} else if (info.isALocalInSomeChild(part)) {
					// nothing to do, literal cannot be mixed in node
					// or some direct children
				} else if (lit.getAtom() instanceof CCEquality) {
					// handle mixed (dis)equalities.
					CCEquality cceq = (CCEquality) lit.getAtom();
					Term lhs = cceq.getLhs().toSMTTerm(m_Theory);
					Term rhs = cceq.getRhs().toSMTTerm(m_Theory);
					for (int child = part - 1;	child >= m_startOfSubtrees[part]; 
							child = m_startOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							if (info.getLhsOccur().isALocal(child)) {
								lhs = auxMaps[child].get(info.m_MixedVar);
							} else {
								assert info.getLhsOccur().isBLocal(child);
								rhs = auxMaps[child].get(info.m_MixedVar);
							}
						}
					}
					if (info.isMixed(part)) {
						if (info.getLhsOccur().isALocal(part)) {
							rhs = auxMaps[part].get(info.m_MixedVar);
						} else {
							assert info.getLhsOccur().isBLocal(part);
							lhs = auxMaps[part].get(info.m_MixedVar);
						}
						m_SmtSolver.assertTerm(m_Theory.term("=", lhs, rhs));
					} else {
						m_SmtSolver.assertTerm(m_Theory.term(lit.getSign() < 0 ? "distinct" : "=", lhs, rhs));
					}
				} else if (lit.negate() instanceof LAEquality) {
					// handle mixed LA disequalities.
					InterpolatorAffineTerm at = new InterpolatorAffineTerm();
					LAEquality eq = (LAEquality) lit.negate();
					for (int child = part - 1;	child >= m_startOfSubtrees[part]; 
							child = m_startOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							// child and node are A-local.
							at.add(Rational.MONE, info.getAPart(child));
							at.add(Rational.ONE, auxMaps[child].get(info.m_MixedVar));
						}
					}
					if (info.isMixed(part)) {
						assert (info.m_MixedVar != null);
						at.add(Rational.ONE, info.getAPart(part));
						at.add(Rational.MONE, auxMaps[part].get(info.m_MixedVar));
						Term t = at.toSMTLib(m_Theory, eq.getVar().isInt());
						Term zero = eq.getVar().isInt() 
								? m_Theory.numeral(BigInteger.ZERO)
								: m_Theory.decimal(BigDecimal.ZERO);
						m_SmtSolver.assertTerm(m_Theory.term("=", t, zero));
					} else {
						assert !at.isConstant();
						at.add(Rational.ONE, eq.getVar());
						at.add(eq.getBound().negate());
						Term t = at.toSMTLib(m_Theory, eq.getVar().isInt());
						Term zero = eq.getVar().isInt() 
								? m_Theory.numeral(BigInteger.ZERO)
								: m_Theory.decimal(BigDecimal.ZERO);
						m_SmtSolver.assertTerm(m_Theory.term("distinct", t, zero));
					}
				} else {
					// handle mixed LA inequalities and equalities.
					LinVar lv;
					InfinitNumber bound;
					if (lit.getAtom() instanceof BoundConstraint) {
						BoundConstraint bc = (BoundConstraint) lit.getAtom();
						bound =	lit.getSign() > 0 ? bc.getBound() : bc.getInverseBound();
						lv = bc.getVar();
					} else  {
						assert lit.getAtom() instanceof LAEquality;
						LAEquality eq = (LAEquality) lit;
						lv = eq.getVar();
						bound = new InfinitNumber(eq.getBound(), 0);
					}

					// check if literal is mixed in part or some child partiton.
					InterpolatorAffineTerm at = new InterpolatorAffineTerm();
					for (int child = part - 1;	child >= m_startOfSubtrees[part]; 
							child = m_startOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							// child and node are A-local.
							at.add(Rational.MONE, info.getAPart(child));
							at.add(Rational.ONE, auxMaps[child].get(info.m_MixedVar));
						}
					}
					if (info.isMixed(part)) {
						assert (info.m_MixedVar != null);
						at.add(Rational.ONE, info.getAPart(part));
						at.add(Rational.MONE, auxMaps[part].get(info.m_MixedVar));
					} else {
						assert !at.isConstant();
						at.add(Rational.ONE, lv);
						at.add(bound.negate());
					}
					if (lit.getAtom() instanceof BoundConstraint) {
						if (lit.getSign() < 0)
							at.negate();
						m_SmtSolver.assertTerm(at.toLeq0(m_Theory));
					} else {
						boolean isInt = at.isInt();
						Term t = at.toSMTLib(m_Theory, isInt);
						Term zero = isInt 
								? m_Theory.numeral(BigInteger.ZERO)
								: m_Theory.decimal(BigDecimal.ZERO);
						Term eqTerm = m_Theory.term("=", t, zero);
						if (!info.isMixed(part)
							&& lit.getSign() < 0)
							eqTerm = m_Theory.term("not", eqTerm);
						m_SmtSolver.assertTerm(eqTerm);
					}
				}
			}
			for (int child = part - 1;	child >= m_startOfSubtrees[part]; 
					child = m_startOfSubtrees[child] - 1) {
				m_SmtSolver.assertTerm(interpolants[child]);
			}
			m_SmtSolver.assertTerm(m_Theory.term("not", interpolants[part]));
			if (m_SmtSolver.checkSat() != LBool.UNSAT)
				throw new AssertionError();
			m_SmtSolver.pop(1);
		}
		m_SmtSolver.pop(1);
		m_Logger.setLevel(old);
	}

	public Interpolant[] interpolate(Clause cl) {
		if (m_Interpolants.containsKey(cl))
			return m_Interpolants.get(cl);

		Interpolant[] interpolants = null;
		ProofNode proof = cl.getProof();
		if (!proof.isLeaf()) {
			ResolutionNode resNode = (ResolutionNode) proof;
			Clause prim = resNode.getPrimary();
			Interpolant[] primInterpolants = interpolate(prim);
			interpolants = new Interpolant[m_NumInterpolants];
			HashSet<Literal> lits = null;
			if (DEEP_CHECK_INTERPOLANTS && m_SmtSolver != null) {
				lits = new HashSet<Literal>();
				for (int i = 0; i < prim.getSize(); i++)
					lits.add(prim.getLiteral(i));
			}

			for (int i = 0; i < m_NumInterpolants; i++) {
				interpolants[i] = new Interpolant(primInterpolants[i].m_term);
			}
			
			m_Logger.debug(new DebugMessage("Resolution Primary: {0}", prim));

			for (Antecedent assump : resNode.getAntecedents()) {
				Interpolant[] assInterp = interpolate(assump.antecedent);
				Literal pivot = assump.pivot;
				LitInfo pivInfo = m_LiteralInfos.get(pivot.getAtom());

				m_Logger.debug(new DebugMessage("Interpolating for {0}", assump));

				for (int i = 0; i < m_NumInterpolants; i++) {
					m_Logger.debug(new DebugMessage
							("Pivot {2}{3} on interpolants {0} and {1} gives...", 
									interpolants[i], assInterp[i], 
									pivot.getSMTFormula(m_Theory), pivInfo));
					if (pivInfo.isALocal(i)) {
						interpolants[i].m_term = 
								m_Theory.or(interpolants[i].m_term, assInterp[i].m_term);
					} else if (pivInfo.isBLocal(i)) {
						interpolants[i].m_term = 
								m_Theory.and(interpolants[i].m_term, assInterp[i].m_term);
					} else if (pivInfo.isAB(i)) {
						interpolants[i].m_term = 
								m_Theory.ifthenelse(pivot.getSMTFormula(m_Theory), 
										interpolants[i].m_term, assInterp[i].m_term);
					} else {
						if (pivot.getAtom() instanceof CCEquality ||
								pivot.getAtom() instanceof LAEquality) {
							Interpolant eqIpol, neqIpol;
							if (pivot.getSign() > 0) {
								eqIpol = assInterp[i];
								neqIpol = interpolants[i];
							} else {
								eqIpol = interpolants[i];
								neqIpol = assInterp[i];
							}
							interpolants[i] = mixedEqInterpolate(
									eqIpol, neqIpol, pivInfo.m_MixedVar);
						} else if (pivot.getAtom() instanceof BoundConstraint) {
							interpolants[i] = mixedPivotLA(
									assInterp[i], interpolants[i], pivInfo.m_MixedVar);
						} else {
							throw new UnsupportedOperationException
							("Cannot handle mixed literal "+pivot);
						}
					}
					m_Logger.debug(interpolants[i]);
				}
				if (DEEP_CHECK_INTERPOLANTS && m_SmtSolver != null) {
					lits.remove(pivot.negate());
					for (int i = 0; i < assump.antecedent.getSize(); i++) {
						if (assump.antecedent.getLiteral(i) != pivot)
							lits.add(assump.antecedent.getLiteral(i));
					}
					checkInductivity(lits, interpolants);
				}
			}
		} else {
			LeafNode leaf = (LeafNode) proof;
			if  (leaf.getLeafKind() == LeafNode.EQ) {
				assert cl.getSize() == 2;
				Literal l1 = cl.getLiteral(0);
				Literal l2 = cl.getLiteral(1);
				assert l1.getSign() != l2.getSign();
				if (l1.getAtom() instanceof LAEquality) {
					l1 = cl.getLiteral(1);
					l2 = cl.getLiteral(0);
				}
				interpolants = computeEQInterpolant
					((CCEquality) l1.getAtom(),	(LAEquality) l2.getAtom(),
					l1.getSign());
			} else if (leaf.isTautology() || leaf.getLeafKind() == LeafNode.NO_THEORY) {
				SourceAnnotation annot = 
						(SourceAnnotation) leaf.getTheoryAnnotation();
				int partition = m_Partitions.containsKey(annot.getAnnotation())
						? m_Partitions.get(annot.getAnnotation()) : 0;
				interpolants = new Interpolant[m_NumInterpolants];
				for (int i = 0; i < m_NumInterpolants; i++) {
					interpolants[i] = new Interpolant(
						m_startOfSubtrees[i] <= partition && partition <= i
						? m_Theory.FALSE : m_Theory.TRUE); 
				}
			} else if  (leaf.getLeafKind() == LeafNode.THEORY_CC) {
				CCInterpolator ipolator = new CCInterpolator(this);
				Term[] interpolantTerms = ipolator.computeInterpolants
						((CCAnnotation) leaf.getTheoryAnnotation());
				interpolants = new Interpolant[m_NumInterpolants];
				for (int j = 0; j < m_NumInterpolants; j++) { 
					interpolants[j] = new Interpolant(interpolantTerms[j]);
				}
			} else if  (leaf.getLeafKind() == LeafNode.THEORY_LA) {
				LAInterpolator ipolator =
						new LAInterpolator(this,
								(LAAnnotation) leaf.getTheoryAnnotation());
				interpolants = ipolator.computeInterpolants();
			} else {
				throw new UnsupportedOperationException("Cannot interpolate "+proof);
			}
		}
		if (DEEP_CHECK_INTERPOLANTS && m_SmtSolver != null) {
			HashSet<Literal> lits = new HashSet<Literal>();
			for (int i = 0; i < cl.getSize(); i++)
				lits.add(cl.getLiteral(i));
			checkInductivity(lits, interpolants);
		}
		m_Interpolants.put(cl, interpolants);
		return interpolants;
	}

	/**
	 * Compute the interpolant for a Nelson-Oppen equality clause. This is a
	 * theory lemma of the form equality implies equality, where one equality
	 * is congruence closure and one is linear arithmetic.
	 * @param ccEq  the congruence closure equality atom 
	 * @param laEq  the linear arithmetic equality atom
	 * @param sign the sign of l1 in the conflict clause. This is -1 if
	 * 	l1 implies l2, and +1 if l2 implies l1. 
	 */
	private Interpolant[] computeEQInterpolant(CCEquality ccEq, LAEquality laEq,
			int sign) {
		Interpolant[] interpolants = null;
		LitInfo ccInfo = getLiteralInfo(ccEq);
		LitInfo laInfo = getLiteralInfo(laEq);
		
		interpolants = new Interpolant[m_NumInterpolants];
		for (int p = 0; p < m_NumInterpolants; p++) {
			Term interpolant; 
			if (ccInfo.isAorShared(p) && laInfo.isAorShared(p))
				interpolant = m_Theory.FALSE; // both literals in A.
			else if (ccInfo.isBorShared(p) && laInfo.isBorShared(p))
				interpolant = m_Theory.TRUE; // both literals in B.
			else {
				InterpolatorAffineTerm iat = new InterpolatorAffineTerm();
				Rational factor = ccEq.getLAFactor();
				TermVariable mixed = null;
				boolean negate = false;
				// Get A part of ccEq:
				if (ccInfo.isALocal(p)) {
					iat.add(factor, ccEq.getLhs().getFlatTerm());
					iat.add(factor.negate(), ccEq.getRhs().getSharedTerm());
					if (sign == 1)
						negate = true;
				} else if (ccInfo.isMixed(p)) {
					// mixed;
					if (sign == 1)
						mixed = ccInfo.getMixedVar();
					if (ccInfo.m_lhsOccur.isALocal(p)) {
						iat.add(factor, ccEq.getLhs().getFlatTerm());
						iat.add(factor.negate(), ccInfo.getMixedVar());
					} else {
						iat.add(factor, ccInfo.getMixedVar());
						iat.add(factor.negate(), ccEq.getRhs().getFlatTerm());
					}
				} else {
					// both sides in B, A part is empty
				}
				
				// Get A part of laEq:
				if (laInfo.isALocal(p)) {
					iat.add(Rational.MONE, laEq.getVar());
					iat.add(laEq.getBound());
					if (sign == -1)
						negate = true;
				} else if (laInfo.isMixed(p)) {
					if (sign == -1)
						mixed = laInfo.getMixedVar();
					iat.add(Rational.MONE, laInfo.getAPart(p));
					iat.add(Rational.ONE, laInfo.getMixedVar());
				} else {
					// both sides in B, A part is empty
				}
				iat.mul(iat.getGCD().inverse());
				
				// Now solve it.
				if (mixed != null) {
					Rational mixedFactor = iat.getSummands().remove(mixed);
					assert(mixedFactor.isIntegral());
					boolean isInt = mixed.getSort().getName().equals("Int");
					if (isInt && mixedFactor.abs() != Rational.ONE) {
						if (mixedFactor.signum() > 0)
							iat.negate();
						Term sharedTerm = iat.toSMTLib(m_Theory, isInt);
						interpolant =
							m_Theory.equals(mixed, 
								m_Theory.term("div", sharedTerm, m_Theory.numeral(mixedFactor.numerator())));
						FunctionSymbol divisible = m_Theory.getFunctionWithResult("divisible", 
								new BigInteger[] {mixedFactor.numerator()},
								null, m_Theory.getSort("Int"));
						interpolant = m_Theory.and(interpolant, m_Theory.term(divisible, sharedTerm));
					} else {
						iat.mul(mixedFactor.negate().inverse());
						Term sharedTerm = iat.toSMTLib(m_Theory, isInt);
						interpolant =
								m_Theory.equals(mixed, sharedTerm);
					}
				} else {
					if (iat.isConstant()) {
						if (iat.getConstant() != InfinitNumber.ZERO)
							negate = !negate;
						interpolant = negate ? m_Theory.FALSE : m_Theory.TRUE;
					} else {
						boolean isInt = iat.isInt();
						Term term = iat.toSMTLib(m_Theory, isInt);
						Term zero = iat.isInt()
							? m_Theory.numeral(BigInteger.ZERO)
							: m_Theory.decimal(BigDecimal.ZERO);
						interpolant = negate ? m_Theory.distinct(term, zero)
									: m_Theory.equals(term, zero);
					}
				}
			}
			interpolants[p] = new Interpolant(interpolant);
		}
		return interpolants;
	}
	
	public void colorLiterals(Clause root, HashSet<Clause> visited) {
		if (visited.contains(root))
			return;
		visited.add(root);
		ProofNode pn = root.getProof();
		if (pn.isLeaf()) {
			LeafNode ln = (LeafNode) pn;
			if (ln.isColorable()) {
				SourceAnnotation annot = 
						(SourceAnnotation) ln.getTheoryAnnotation();
				int partition = m_Partitions.containsKey(annot.getAnnotation())
						? m_Partitions.get(annot.getAnnotation()) : 0;
				for (int i = 0; i < root.getSize(); i++) {
					Literal lit = root.getLiteral(i);
					DPLLAtom atom = lit.getAtom();
					LitInfo info = m_LiteralInfos.get(atom);
					if (info == null) {
						info = new LitInfo();
						m_LiteralInfos.put(atom, info);
					}
					if (!info.contains(partition)) {
						info.occursIn(partition);
						if (atom instanceof CCEquality) {
							CCEquality eq = (CCEquality)atom;
							addOccurrence(eq.getLhs().getFlatTerm(), partition);
							addOccurrence(eq.getRhs().getFlatTerm(), partition);
						} else if (atom instanceof BoundConstraint) {
							LinVar lv = ((BoundConstraint) atom).getVar();
							addOccurrence(lv, partition);
						} else if (atom instanceof LAEquality) {
							LinVar lv = ((LAEquality) atom).getVar();
							addOccurrence(lv, partition);
						}
					}
				}
			}
		} else {
			ResolutionNode rn = (ResolutionNode) pn;
			colorLiterals(rn.getPrimary(), visited);
			for (Antecedent a : rn.getAntecedents()) {
				colorLiterals(a.antecedent, visited);
			}
		}
	}


	Occurrence getOccurrence(SharedTerm shared) {
		Occurrence result = m_SymbolPartition.get(shared);
		if (result == null) {
			result = new Occurrence();
			IAnnotation annot = shared.getAnnotation();
			// TODO Here we need to change something if we have quantifiers.
			if (annot instanceof SourceAnnotation) {
				Integer partition = m_Partitions.get(
						((SourceAnnotation) annot).getAnnotation());
				if (partition == null) {
					for (int p = 0; p<m_NumInterpolants;p++)
						result.occursIn(p);
				} else
					result.occursIn(partition);
			}
			m_SymbolPartition.put(shared, result);
		}
		return result;
	}

	void addOccurrence(SharedTerm term, int part) {
		getOccurrence(term).occursIn(part);
		if (term.getTerm() instanceof SMTAffineTerm
			&& term.getLinVar() != null) {
			addOccurrence(term.getLinVar(), part);
		} else {
			if (term.getTerm() instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) term.getTerm();
				if (!at.getFunction().isInterpreted()) {
					Clausifier c = term.getClausifier();
					for (Term p : at.getParameters())
						addOccurrence(c.getSharedTerm(p), part);
				}
			}
		}
	}

	void addOccurrence(LinVar var, int part) {
		if (var.isInitiallyBasic()) {
			for (LinVar c : var.getLinTerm().keySet())
				addOccurrence(c.getSharedTerm(), part);
		} else {
			addOccurrence(var.getSharedTerm(), part);
		}
	}

	LitInfo getLiteralInfo(DPLLAtom lit) {
		LitInfo result = m_LiteralInfos.get(lit);
		if (result == null)
			result = colorMixedLiteral(lit);
		return result;
	}

	/**
	 * Compute the LitInfo for a mixed Literal.
	 */
	public LitInfo colorMixedLiteral(DPLLAtom atom) {
		LitInfo info = m_LiteralInfos.get(atom);

		assert info == null;

		ArrayList<SharedTerm> subterms = new ArrayList<SharedTerm>();
		if (atom instanceof CCEquality) {
			CCEquality eq = (CCEquality)atom;
			subterms.add(eq.getLhs().getFlatTerm());
			subterms.add(eq.getRhs().getFlatTerm());
		} else {
			LinVar lv = null;
			if (atom instanceof BoundConstraint) {
				lv = ((BoundConstraint) atom).getVar();
			} else if (atom instanceof LAEquality) {
				lv = ((LAEquality) atom).getVar();
			}
			Collection<LinVar> components;
			if (lv.isInitiallyBasic()) {
				components = lv.getLinTerm().keySet();
			} else {
				components = Collections.singleton(lv);
			}
			for (LinVar c : components) {
				subterms.add(c.getSharedTerm());
			}
		}
		info = computeMixedOccurrence(subterms);
		this.m_LiteralInfos.put(atom, info);
		
		BitSet shared = new BitSet();
		shared.or(info.m_inA);
		shared.or(info.m_inB);
		if (shared.nextClearBit(0) >= m_NumInterpolants)
			return info;

		info.m_MixedVar = m_Theory.createFreshTermVariable("litaux",
				subterms.get(0).getSort());
		
		if (atom instanceof CCEquality) {
			CCEquality eq = (CCEquality)atom;
			info.m_lhsOccur = getOccurrence(eq.getLhs().getFlatTerm());
		} else if (atom instanceof BoundConstraint || atom instanceof LAEquality) {
			LinVar lv = null;
			if(atom instanceof BoundConstraint) 
				lv = ((BoundConstraint) atom).getVar();
			else
				lv = ((LAEquality) atom).getVar();
			assert lv.isInitiallyBasic() : "Not initially basic: " + lv + " atom: " + atom;

			info.m_APart = new MutableAffinTerm[m_NumInterpolants];
			for (int part = 0; part < m_NumInterpolants; part++) {
				if (!info.isMixed(part))
					continue;
			
				MutableAffinTerm sumApart = new MutableAffinTerm();	
				for(Entry<LinVar, BigInteger> en : lv.getLinTerm().entrySet()) {
					LinVar var = en.getKey();
					Occurrence occ = 
						m_SymbolPartition.get(en.getKey().getSharedTerm());
					if (occ.isALocal(part)) {
						Rational coeff = 
								Rational.valueOf(en.getValue(), BigInteger.ONE);
						sumApart.add(coeff, var);
					}
				}
				
				info.m_APart[part] = sumApart;				
			}
		}
		return info;
	}

	private LitInfo computeMixedOccurrence(ArrayList<SharedTerm> subterms) {
		LitInfo info;
		BitSet inA = null, inB = null;
		for(SharedTerm st : subterms) {
			Occurrence occInfo = getOccurrence(st);
			if (inA == null) {
				inA = (BitSet) occInfo.m_inA.clone(); 
				inB = (BitSet) occInfo.m_inB.clone(); 
			} else {
				inA.and(occInfo.m_inA);
				inB.and(occInfo.m_inB);
			}
		}
		info = new LitInfo(inA, inB);
		return info;
	}

	/**
	 * This term transformer substitutes an auxiliary variable by an 
	 * arbitrary term.  This is used for the LA and UF resolution rule.
	 * For the UF resolution rule, it will replace the auxiliary variable
	 * by the term that must be equal to it due to an EQ(x,s) term in the
	 * other interpolant.  For the LA resolution rule, this will replace
	 * the auxiliary variable by -s1/c1 - i in F1/F2 (see paper).
	 * 
	 * The replacement term may contain other auxiliary variables
	 * that will be replaced later.  It may only contain auxiliary variables
	 * for equalities with the negated equality in the clause or auxiliary 
	 * variables for LA literals that are bound by a surrounding LATerm.
	 *  
	 * @author hoenicke
	 */
	public static class Substitutor extends TermTransformer {
		TermVariable m_TermVar;
		Term m_Replacement;
		
		public Substitutor(TermVariable termVar, Term replacement) {
			this.m_TermVar = termVar;
			this.m_Replacement = replacement;
		}
		
		public void convert(Term term) {
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				final Term[] oldTerms = laTerm.m_s.getSummands().keySet()
						.toArray(new Term[laTerm.m_s.getSummands().size()]);
				/* recurse into LA term */ 
				enqueueWalker(new Walker() {
					@Override
					public void walk(NonRecursive engine) {
						Substitutor me = (Substitutor) engine;
						Term result = me.getConverted();
						Term[] newTerms = me.getConverted(oldTerms);
						if (result == laTerm.m_F && newTerms == oldTerms) {
							me.setResult(laTerm);
							return;
						}
						InterpolatorAffineTerm newS = 
								new InterpolatorAffineTerm();
						for (int i = 0; i< oldTerms.length; i++) {
							newS.add(laTerm.m_s.getSummands().get(oldTerms[i]), 
									newTerms[i]);
						}
						newS.add(laTerm.m_s.getConstant());
						me.setResult(new LATerm(newS, laTerm.m_k, result));
					}
				});
				pushTerm(laTerm.m_F);
				pushTerms(oldTerms);
				return;
			} else if (term.equals(m_TermVar))
				setResult(m_Replacement);
			else
				super.convert(term);
		}
	}

	/**
	 * Substitute termVar by replacement in mainTerm.  This will also work
	 * correctly with LATerms.
	 * @param mainTerm the term where the replacement is done.
	 * @param termVar the variable to replace.
	 * @param replacement the replacement term. 
	 * @return the substituted term.
	 */
	Term substitute(Term mainTerm, 
			final TermVariable termVar, final Term replacement) {
		return new Substitutor(termVar, replacement).transform(mainTerm);
	}

	class EQInterpolator extends TermTransformer {
		Interpolant m_I2;
		TermVariable m_AuxVar;
		
		EQInterpolator (Interpolant i2, TermVariable auxVar) {
			m_I2 = i2;
			m_AuxVar = auxVar;
		}
		
		public void convert(Term term) {
			assert term != m_AuxVar;
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				/* recurse into LA term */ 
				enqueueWalker(new Walker() {
					@Override
					public void walk(NonRecursive engine) {
						EQInterpolator me = (EQInterpolator) engine;
						Term result = me.getConverted();  
						if (result == laTerm.m_F)
							me.setResult(laTerm);
						else
							me.setResult(new LATerm(laTerm.m_s, laTerm.m_k, result));
					}
				});
				pushTerm(laTerm.m_F);
				return;
			} else if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getParameters().length == 2 && 
					(appTerm.getParameters()[0] == m_AuxVar
					 || appTerm.getParameters()[1] == m_AuxVar)) {
					assert appTerm.getFunction().isIntern()
						&& appTerm.getFunction().getName().equals("=")
						&& appTerm.getParameters().length == 2;
					
					Term s = appTerm.getParameters()[1];
					if (s == m_AuxVar)
						s = appTerm.getParameters()[0];
					setResult(substitute(m_I2.m_term, m_AuxVar, s));
					return;
				}
			}
			super.convert(term);
		}
	}

	/**
	 * Compute the interpolant for the resolution rule with a mixed equality
	 * as pivot.  This is I1[I2(s_i)] for I1[x=s_i] and I2(x).
	 * @param eqIpol the interpolant I1[x=s_i].
	 * @param neqIpol the interpolant I2(x).
	 * @param mixedVar the auxiliary variable x. 
	 * @return the resulting interpolant.
	 */
	private Interpolant mixedEqInterpolate(Interpolant eqIpol,
			Interpolant neqIpol, TermVariable mixedVar) {
		TermTransformer ipolator = new EQInterpolator(neqIpol, mixedVar);
		return new Interpolant(ipolator.transform(eqIpol.m_term));
	}
	
	static abstract class MixedLAInterpolator extends TermTransformer {
		TermVariable m_MixedVar;
		Term m_I2;
		LATerm m_LA1;
		
		public MixedLAInterpolator(Term i2, TermVariable mixed) {
			m_MixedVar = mixed;
			m_LA1 = null;
			m_I2 = i2;
		}

		abstract Term interpolate(LATerm la1, LATerm la2);
		
		public void convert(Term term) {
			assert term != m_MixedVar;
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				if (laTerm.m_s.getSummands().get(m_MixedVar) != null) {
					if (m_LA1 == null) {
						/* We are inside I1. Remember the lainfo and push I2 
						 * on the convert stack.  Also enqueue a walker that
						 * will remove m_LA1 once we are finished with I2.
						 */
						beginScope();
						m_LA1 = laTerm;
						enqueueWalker(new Walker() {
							@Override
							public void walk(NonRecursive engine) {
								((MixedLAInterpolator) engine).m_LA1 = null;
								((MixedLAInterpolator) engine).endScope();
							}
						});
						pushTerm(m_I2);
						return;
					} else {
						/* We are inside I2. Interpolate the LAInfos.
						 */
						setResult(interpolate(m_LA1, (LATerm) term));
						return;
					}
				} else {
					/* this is a LA term not involving the mixed variable */ 
					enqueueWalker(new Walker() {
						@Override
						public void walk(NonRecursive engine) {
							MixedLAInterpolator me = (MixedLAInterpolator) engine;
							Term result = me.getConverted();
							if (result == laTerm.m_F)
								me.setResult(laTerm);
							else
								me.setResult(new LATerm(laTerm.m_s, laTerm.m_k, result));
						}
					});
					pushTerm(laTerm.m_F);
					return;
				}
			} else
				super.convert(term);
		}
	}
	
	class RealInterpolator extends MixedLAInterpolator {
		public RealInterpolator(Term i2, TermVariable mixedVar) {
			super(i2, mixedVar);
		}
		
		public Term interpolate(LATerm la1, LATerm la2) {
			//retrieve c1,c2,s2,s2
			InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(la1.m_s);
			Rational               c1 = s1.getSummands().remove(m_MixedVar);
			InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(la2.m_s);
			Rational               c2 = s2.getSummands().remove(m_MixedVar);
			assert (c1.signum() * c2.signum() == -1);
			InfinitNumber newK = la1.m_k.mul(c2.abs())
					.add(la2.m_k.mul(c1.abs()));

			//compute c1s2 + c2s1
			InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(c1.abs(), s2);
			c1s2c2s1.add(c2.abs(), s1);

			Term newF;
			if (s1.getConstant().meps > 0
				|| s2.getConstant().meps > 0) {
				// One of the inequalities is strict.  In this case
				// c1s2c2s1 must also be a strict inequality and it is not
				// possible that c1s2c2s1 == 0 holds. Hence, we do not need
				// to substitute a shared term.
				newF = c1s2c2s1.toLeq0(m_Theory);
				newK = InfinitNumber.EPSILON.negate();
			} else if (la1.m_k.less(InfinitNumber.ZERO)) {
				//compute -s1/c1
				InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.mul(c1.inverse().negate());
				Term s1DivByc1 = s1divc1.toSMTLib(m_Theory, false);
				newF = substitute(la2.m_F, m_MixedVar, s1DivByc1);
				newK = la2.m_k;
			} else {
				assert (la2.m_k.less(InfinitNumber.ZERO));
				//compute s2/c2
				InterpolatorAffineTerm s2divc2 = new InterpolatorAffineTerm(s2);
				s2divc2.mul(c2.inverse().negate());
				Term s2DivByc2 = s2divc2.toSMTLib(m_Theory, false);
				newF = substitute(la1.m_F, m_MixedVar, s2DivByc2);
				newK = la1.m_k;
			}
			LATerm la3 = new LATerm(c1s2c2s1, newK, newF);
			return la3;
		}
	}

	class IntegerInterpolator extends MixedLAInterpolator {
		
		public IntegerInterpolator(Term i2, TermVariable mixedVar) {
			super (i2, mixedVar);
		}
		
		public Term interpolate(LATerm la1, LATerm la2) {
			//retrieve c1,c2,s1,s2
			InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(la1.m_s);
			Rational               c1 = s1.getSummands().remove(m_MixedVar);
			InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(la2.m_s);
			Rational               c2 = s2.getSummands().remove(m_MixedVar);
			assert (c1.isIntegral() && c2.isIntegral());
			assert (c1.signum() * c2.signum() == -1);
			Rational absc1 = c1.abs();
			Rational absc2 = c2.abs();

			//compute c1s2 + c2s1
			InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(absc1, s2);
			c1s2c2s1.add(absc2, s1);

			//compute newk = c2k1 + c1k2 + c1c2;
			Rational c1c2 = absc1.mul(absc2);
			InfinitNumber newK = la1.m_k.mul(absc2).add(la2.m_k.mul(absc1))
					.add(new InfinitNumber(c1c2, 0));
			assert (newK.isIntegral());
			
			Rational k1c1 = la1.m_k.ma.add(Rational.ONE).div(absc1).floor();
			Rational k2c2 = la2.m_k.ma.add(Rational.ONE).div(absc2).floor();
			Rational kc;
			Rational theC;
			InterpolatorAffineTerm theS;
			if (k1c1.compareTo(k2c2) < 0) {
				theC = c1;
				theS = s1;
				kc = k1c1;
			} else {
				theC = c2;
				theS = s2;
				kc = k2c2;
			}
			BigInteger cNum = theC.numerator().abs(); 
			Term newF = m_Theory.FALSE;
			// Use -s/c as start value.
			InterpolatorAffineTerm sPlusOffset = new InterpolatorAffineTerm();
			sPlusOffset.add(theC.signum() > 0 ? Rational.MONE : Rational.ONE, theS);
			Rational offset = Rational.ZERO;
			if (theC.signum() < 0)
				sPlusOffset.add(theC.abs().add(Rational.MONE));
			while (offset.compareTo(kc) <= 0) {
				Term x;
				x = sPlusOffset.toSMTLib(m_Theory, true);
				if (!cNum.equals(BigInteger.ONE))
					x = m_Theory.term("div", x, m_Theory.numeral(cNum));
				Term F1 = substitute(la1.m_F, m_MixedVar, x);
				Term F2 = substitute(la2.m_F, m_MixedVar, x);
				
				if (offset.compareTo(kc) == 0) {
					if (theS == s1)
						F1 = m_Theory.TRUE;
					else
						F2 = m_Theory.TRUE;
				}
				newF = m_Theory.or(newF, m_Theory.and(F1, F2));
				sPlusOffset = sPlusOffset.add(theC.negate());
				offset = offset.add(c1c2);
			}
			LATerm la3 = new LATerm(c1s2c2s1, newK, newF);
			return la3;
		}
	}

	/**
	 * Compute the interpolant for the resolution rule with a mixed inequality
	 * as pivot.  This is I1[I2(LA3)] for I1[LA1] and I2[LA2].
	 * Note that we use only one auxiliary variable, which corresponds to
	 * x_1 and -x_2 in the paper.
	 * @param leqItp the interpolant I1[LA1].
	 * @param sgItp the interpolant I2[LA2].
	 * @param mixedVar the auxiliary variable x used in the la term. 
	 * @return the resulting interpolant.
	 */
	public Interpolant mixedPivotLA(Interpolant leqItp,
			Interpolant sgItp, TermVariable mixedVar) {
		final MixedLAInterpolator ipolator;

		if (mixedVar.getSort().getName().equals("Real"))
			ipolator = new RealInterpolator(sgItp.m_term, mixedVar);
		else
			ipolator = new IntegerInterpolator(sgItp.m_term, mixedVar);
		Interpolant newI = new Interpolant(ipolator.transform(leqItp.m_term));
		return newI;
	}
}


