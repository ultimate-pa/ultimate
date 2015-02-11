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
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
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
		BitSet mInA;
		BitSet mInB;

		public Occurrence() {
			mInA = new BitSet(mNumInterpolants + 1);
			mInB = new BitSet(mNumInterpolants + 1);
		}

		public Occurrence(BitSet inA, BitSet inB) {
			mInA = inA;
			mInB = inB;
		}

		public void occursIn(int partition) {
			for (int i = 0; i <= mNumInterpolants; i++) {
				if (i < partition || mStartOfSubtrees[i] > partition)
					mInB.set(i);
				else
					mInA.set(i);
			}
		}

		public boolean isALocalInSomeChild(int partition) {
			for (int i = partition - 1; i >= mStartOfSubtrees[partition]; ) {
				if (mInA.get(i))
					return true;
				i = mStartOfSubtrees[i] - 1;
			}
			return false;
		}

		public boolean contains(int partition) {
			if (!mInA.get(partition))
				return false;
			if (mInB.get(partition))
				return true;
			for (int i = partition - 1; i >= mStartOfSubtrees[partition]; ) {
				if (!mInB.get(i))
					return false;
				i = mStartOfSubtrees[i] - 1;
			}
			return true;
		}

		public boolean isAorShared(int partition) {
			return mInA.get(partition);
		}
		public boolean isBorShared(int partition) {
			return mInB.get(partition);
		}
		public boolean isALocal(int partition) {
			return mInA.get(partition) && !mInB.get(partition);
		}
		public boolean isBLocal(int partition) {
			return mInB.get(partition) && !mInA.get(partition);
		}
		public boolean isAB(int partition) {
			return mInA.get(partition) && mInB.get(partition);
		}
		public boolean isMixed(int partition) {
			return !mInA.get(partition) && !mInB.get(partition);
		}

		public String toString() {
			return "[" + mInA + "|" + mInB + "]";
		}

		/**
		 * Find the first A-local colored node.  Every occurrence
		 * has a A-local chain from such a node to the root
		 * node and all other nodes are not A-local.
		 * @return the first A-local colored node.
		 */
		public int getALocalColor() {
			int color = mInA.nextSetBit(0);
			if (mInB.get(color)) {
				color = mInB.nextClearBit(color);
			}
			return color;
		}
	}

	class LitInfo extends Occurrence {
		TermVariable mMixedVar;
		/** Tells for an equality whether the A part is the Lhs or
		 * the Rhs.
		 */
		Occurrence mLhsOccur;
		/** 
		 * Gives for an inequality the A part.
		 */
		MutableAffinTerm[] mAPart;

		public LitInfo() {
			super();
		}

		public LitInfo(BitSet inA, BitSet inB) {
			super(inA, inB);
		}

		public TermVariable getMixedVar() {
			return mMixedVar;
		}

		public Occurrence getLhsOccur() {
			return mLhsOccur;
		}

		public MutableAffinTerm getAPart(int p) {
			return mAPart[p];
		}
	}

	SMTInterpol mSmtSolver;

	Logger mLogger;
	Theory mTheory;
	int mNumInterpolants;
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
	int[] mStartOfSubtrees;
	HashMap<SharedTerm, Occurrence> mSymbolPartition;
	HashMap<DPLLAtom, LitInfo> mLiteralInfos;
	HashMap<String, Integer> mPartitions;
	HashMap<Clause, Interpolant[]> mInterpolants;
	
	

	public Interpolator(Logger logger, SMTInterpol smtSolver, Theory theory, 
			Set<String>[] partitions, int[] startOfSubTrees) {
		mPartitions = new HashMap<String, Integer>();
		for (int i = 0; i < partitions.length; i++) {
			Integer part = i;
			for (String name: partitions[i]) {
				mPartitions.put(name, part);
			}
		}
		mLogger = logger;
		mSmtSolver = smtSolver;
		mTheory = theory;
		mNumInterpolants = partitions.length - 1;

		mStartOfSubtrees = startOfSubTrees;
		mSymbolPartition = new HashMap<SharedTerm, Occurrence>();
		mLiteralInfos = new HashMap<DPLLAtom, LitInfo>();
		mInterpolants = new HashMap<Clause,Interpolant[]>();
	}

	public Interpolator(Logger logger, Theory theory, 
			Set<String>[] partitions, Clausifier clausifier) {
		this(logger, null, theory, partitions, new int[partitions.length]);
	}

	private Term unfoldLAs(Interpolant interpolant) {
		TermTransformer substitutor = new TermTransformer() {
			public void convert(Term term) {
				if (term instanceof LATerm)
					term = ((LATerm) term).mF;
				super.convert(term);
			}
		};
		return substitutor.transform(interpolant.mTerm);
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
		Level old = mLogger.getLevel();// NOPMD
		mLogger.setLevel(Level.ERROR);

		mSmtSolver.push(1);
		
		/* initialize auxMaps, which maps for each partition the auxiliary
		 * variables for mixed literals to a new fresh constant.
		 */
		@SuppressWarnings("unchecked") // because Java Generics are broken :(
		HashMap<TermVariable, Term>[] auxMaps = new HashMap[ipls.length];
		
		for (Literal lit : clause) {
			LitInfo info = getLiteralInfo(lit.getAtom());
			for (int part = 0; part < ipls.length; part++) {
				if (info.isMixed(part)) {
					TermVariable tv = info.mMixedVar;
					String name = ".check" + part + "." + tv.getName();
					mSmtSolver.declareFun(name, new Sort[0], tv.getSort());
					Term term = mSmtSolver.term(name);
					if (auxMaps[part] == null)
						auxMaps[part] = new HashMap<TermVariable, Term>();
					auxMaps[part].put(tv, term);
				}
			}
		}
		Term[] interpolants = new Term[ipls.length];
		for (int part = 0; part < ipls.length; part++) {
			Term ipl = unfoldLAs(ipls[part]);
			if (auxMaps[part] == null) {
				interpolants[part] = ipl;
			} else {
				TermVariable[] tvs = new TermVariable[auxMaps[part].size()];
				Term[] values = new Term[auxMaps[part].size()];
				int i = 0;
				for (Entry<TermVariable, Term> entry : auxMaps[part].entrySet()) {
					tvs[i] = entry.getKey();
					values[i] = entry.getValue();
					i++;
				}
				interpolants[part] = mTheory.let(tvs, values, ipl);
			}
		}
		
		
		for (int part = 0; part < ipls.length; part++) {
			mSmtSolver.push(1);
			for (Entry<String, Integer> entry: mPartitions.entrySet()) {
				if (entry.getValue() == part)
					mSmtSolver.assertTerm(mTheory.term(entry.getKey()));
			}
			for (Literal lit : clause) {
				lit = lit.negate();
				LitInfo info = mLiteralInfos.get(lit.getAtom());
				if (info.contains(part)) {
					mSmtSolver.assertTerm(lit.getSMTFormula(mTheory));
				} else if (info.isBLocal(part)) {
					// nothing to do, literal cannot be mixed in sub-tree.
				} else if (info.isALocalInSomeChild(part)) {
					// nothing to do, literal cannot be mixed in node
					// or some direct children
				} else if (lit.getAtom() instanceof CCEquality) {
					// handle mixed (dis)equalities.
					CCEquality cceq = (CCEquality) lit.getAtom();
					Term lhs = cceq.getLhs().toSMTTerm(mTheory);
					Term rhs = cceq.getRhs().toSMTTerm(mTheory);
					for (int child = part - 1;	child >= mStartOfSubtrees[part]; 
							child = mStartOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							if (info.getLhsOccur().isALocal(child)) {
								lhs = auxMaps[child].get(info.mMixedVar);
							} else {
								assert info.getLhsOccur().isBLocal(child);
								rhs = auxMaps[child].get(info.mMixedVar);
							}
						}
					}
					if (info.isMixed(part)) {
						if (info.getLhsOccur().isALocal(part)) {
							rhs = auxMaps[part].get(info.mMixedVar);
						} else {
							assert info.getLhsOccur().isBLocal(part);
							lhs = auxMaps[part].get(info.mMixedVar);
						}
						mSmtSolver.assertTerm(mTheory.term("=", lhs, rhs));
					} else {
						mSmtSolver.assertTerm(mTheory.term(lit.getSign() < 0 ? "distinct" : "=", lhs, rhs));
					}
				} else if (lit.negate() instanceof LAEquality) {
					// handle mixed LA disequalities.
					InterpolatorAffineTerm at = new InterpolatorAffineTerm();
					LAEquality eq = (LAEquality) lit.negate();
					for (int child = part - 1;	child >= mStartOfSubtrees[part]; 
							child = mStartOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							// child and node are A-local.
							at.add(Rational.MONE, info.getAPart(child));
							at.add(Rational.ONE, auxMaps[child].get(info.mMixedVar));
						}
					}
					if (info.isMixed(part)) {
						assert (info.mMixedVar != null);
						at.add(Rational.ONE, info.getAPart(part));
						at.add(Rational.MONE, auxMaps[part].get(info.mMixedVar));
						Term t = at.toSMTLib(mTheory, eq.getVar().isInt());
						Term zero = eq.getVar().isInt() 
								? mTheory.numeral(BigInteger.ZERO)
								: mTheory.decimal(BigDecimal.ZERO);
						mSmtSolver.assertTerm(mTheory.term("=", t, zero));
					} else {
						assert !at.isConstant();
						at.add(Rational.ONE, eq.getVar());
						at.add(eq.getBound().negate());
						Term t = at.toSMTLib(mTheory, eq.getVar().isInt());
						Term zero = eq.getVar().isInt() 
								? mTheory.numeral(BigInteger.ZERO)
								: mTheory.decimal(BigDecimal.ZERO);
						mSmtSolver.assertTerm(mTheory.term("distinct", t, zero));
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
					for (int child = part - 1;	child >= mStartOfSubtrees[part]; 
							child = mStartOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							// child and node are A-local.
							at.add(Rational.MONE, info.getAPart(child));
							at.add(Rational.ONE, auxMaps[child].get(info.mMixedVar));
						}
					}
					if (info.isMixed(part)) {
						assert (info.mMixedVar != null);
						at.add(Rational.ONE, info.getAPart(part));
						at.add(Rational.MONE, auxMaps[part].get(info.mMixedVar));
					} else {
						assert !at.isConstant();
						at.add(Rational.ONE, lv);
						at.add(bound.negate());
					}
					if (lit.getAtom() instanceof BoundConstraint) {
						if (lit.getSign() < 0)
							at.negate();
						mSmtSolver.assertTerm(at.toLeq0(mTheory));
					} else {
						boolean isInt = at.isInt();
						Term t = at.toSMTLib(mTheory, isInt);
						Term zero = isInt 
								? mTheory.numeral(BigInteger.ZERO)
								: mTheory.decimal(BigDecimal.ZERO);
						Term eqTerm = mTheory.term("=", t, zero);
						if (!info.isMixed(part)
							&& lit.getSign() < 0)
							eqTerm = mTheory.term("not", eqTerm);
						mSmtSolver.assertTerm(eqTerm);
					}
				}
			}
			for (int child = part - 1;	child >= mStartOfSubtrees[part]; 
					child = mStartOfSubtrees[child] - 1) {
				mSmtSolver.assertTerm(interpolants[child]);
			}
			mSmtSolver.assertTerm(mTheory.term("not", interpolants[part]));
			if (mSmtSolver.checkSat() != LBool.UNSAT)
				throw new AssertionError();
			mSmtSolver.pop(1);
		}
		mSmtSolver.pop(1);
		mLogger.setLevel(old);
	}

	public Interpolant[] interpolate(Clause cl) {
		if (mInterpolants.containsKey(cl))
			return mInterpolants.get(cl);

		Interpolant[] interpolants = null;
		ProofNode proof = cl.getProof();
		if (!proof.isLeaf()) { // NOPMD
			ResolutionNode resNode = (ResolutionNode) proof;
			Clause prim = resNode.getPrimary();
			Interpolant[] primInterpolants = interpolate(prim);
			interpolants = new Interpolant[mNumInterpolants];
			HashSet<Literal> lits = null;
			if (Config.DEEP_CHECK_INTERPOLANTS && mSmtSolver != null) {
				lits = new HashSet<Literal>();
				for (int i = 0; i < prim.getSize(); i++)
					lits.add(prim.getLiteral(i));
			}

			for (int i = 0; i < mNumInterpolants; i++) {
				interpolants[i] = new Interpolant(primInterpolants[i].mTerm);
			}
			
			mLogger.debug(new DebugMessage("Resolution Primary: {0}", prim));

			for (Antecedent assump : resNode.getAntecedents()) {
				Interpolant[] assInterp = interpolate(assump.mAntecedent);
				Literal pivot = assump.mPivot;
				LitInfo pivInfo = mLiteralInfos.get(pivot.getAtom());

				mLogger.debug(new DebugMessage("Interpolating for {0}", assump));

				for (int i = 0; i < mNumInterpolants; i++) {
					mLogger.debug(new DebugMessage(
					        "Pivot {2}{3} on interpolants {0} and {1} gives...",
									interpolants[i], assInterp[i], 
									pivot.getSMTFormula(mTheory), pivInfo));
					if (pivInfo.isALocal(i)) {
						interpolants[i].mTerm = mTheory.or(
						        interpolants[i].mTerm, assInterp[i].mTerm);
					} else if (pivInfo.isBLocal(i)) {
						interpolants[i].mTerm = mTheory.and(
						        interpolants[i].mTerm, assInterp[i].mTerm);
					} else if (pivInfo.isAB(i)) {
						interpolants[i].mTerm = 
								mTheory.ifthenelse(pivot.getSMTFormula(mTheory),
								     interpolants[i].mTerm, assInterp[i].mTerm);
					} else {
						if (pivot.getAtom() instanceof CCEquality
								|| pivot.getAtom() instanceof LAEquality) {
							Interpolant eqIpol, neqIpol;
							if (pivot.getSign() > 0) {
								eqIpol = assInterp[i];
								neqIpol = interpolants[i];
							} else {
								eqIpol = interpolants[i];
								neqIpol = assInterp[i];
							}
							interpolants[i] = mixedEqInterpolate(
									eqIpol, neqIpol, pivInfo.mMixedVar);
						} else if (pivot.getAtom() instanceof BoundConstraint) {
							interpolants[i] = mixedPivotLA(
									assInterp[i], interpolants[i], pivInfo.mMixedVar);
						} else {
							throw new UnsupportedOperationException(
							        "Cannot handle mixed literal " + pivot);
						}
					}
					mLogger.debug(interpolants[i]);
				}
				if (Config.DEEP_CHECK_INTERPOLANTS && mSmtSolver != null) {
					lits.remove(pivot.negate());
					for (int i = 0; i < assump.mAntecedent.getSize(); i++) {
						if (assump.mAntecedent.getLiteral(i) != pivot)
							lits.add(assump.mAntecedent.getLiteral(i));
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
				interpolants = computeEQInterpolant(
				        (CCEquality) l1.getAtom(),	(LAEquality) l2.getAtom(),
				            l1.getSign());
			} else if (leaf.hasSourceAnnotation()) {
				SourceAnnotation annot = 
						(SourceAnnotation) leaf.getTheoryAnnotation();
				int partition = mPartitions.containsKey(annot.getAnnotation())
						? mPartitions.get(annot.getAnnotation()) : 0;
				interpolants = new Interpolant[mNumInterpolants];
				for (int i = 0; i < mNumInterpolants; i++) {
					interpolants[i] = new Interpolant(
						mStartOfSubtrees[i] <= partition && partition <= i
						? mTheory.mFalse : mTheory.mTrue); 
				}
			} else if  (leaf.getLeafKind() == LeafNode.THEORY_CC) {
				CCInterpolator ipolator = new CCInterpolator(this);
				Term[] interpolantTerms = ipolator.computeInterpolants(
						cl, (CCAnnotation) leaf.getTheoryAnnotation());
				interpolants = new Interpolant[mNumInterpolants];
				for (int j = 0; j < mNumInterpolants; j++) { 
					interpolants[j] = new Interpolant(interpolantTerms[j]);
				}
			} else if  (leaf.getLeafKind() == LeafNode.THEORY_LA) {
				LAInterpolator ipolator =
						new LAInterpolator(this,
								(LAAnnotation) leaf.getTheoryAnnotation());
				interpolants = ipolator.computeInterpolants();
			} else {
				throw new UnsupportedOperationException("Cannot interpolate " + proof);
			}
		}
		if (Config.DEEP_CHECK_INTERPOLANTS && mSmtSolver != null) {
			HashSet<Literal> lits = new HashSet<Literal>();
			for (int i = 0; i < cl.getSize(); i++)
				lits.add(cl.getLiteral(i));
			checkInductivity(lits, interpolants);
		}
		mInterpolants.put(cl, interpolants);
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
		
		interpolants = new Interpolant[mNumInterpolants];
		for (int p = 0; p < mNumInterpolants; p++) {
			Term interpolant; 
			if (ccInfo.isAorShared(p) && laInfo.isAorShared(p))
				interpolant = mTheory.mFalse; // both literals in A.
			else if (ccInfo.isBorShared(p) && laInfo.isBorShared(p))
				interpolant = mTheory.mTrue; // both literals in B.
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
					if (ccInfo.mLhsOccur.isALocal(p)) {
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
				if (mixed != null) { // NOPMD
					Rational mixedFactor = iat.getSummands().remove(mixed);
					assert mixedFactor.isIntegral();
					boolean isInt = mixed.getSort().getName().equals("Int");
					if (isInt && mixedFactor.abs() != Rational.ONE) { // NOPMD
						if (mixedFactor.signum() > 0)
							iat.negate();
						Term sharedTerm = iat.toSMTLib(mTheory, isInt);
						interpolant =
							mTheory.equals(mixed, mTheory.term(
							        "div", sharedTerm,
							        mTheory.numeral(mixedFactor.numerator())));
						FunctionSymbol divisible = mTheory.getFunctionWithResult(
						        "divisible", 
								new BigInteger[] {mixedFactor.numerator().abs()},
								null, mTheory.getSort("Int"));
						interpolant = mTheory.and(
						        interpolant, mTheory.term(divisible, sharedTerm));
					} else {
						iat.mul(mixedFactor.negate().inverse());
						Term sharedTerm = iat.toSMTLib(mTheory, isInt);
						interpolant =
								mTheory.equals(mixed, sharedTerm);
					}
				} else {
					if (iat.isConstant()) {
						if (iat.getConstant() != InfinitNumber.ZERO)
							negate ^= true;
						interpolant = negate ? mTheory.mFalse : mTheory.mTrue;
					} else {
						boolean isInt = iat.isInt();
						Term term = iat.toSMTLib(mTheory, isInt);
						Term zero = iat.isInt()
							? mTheory.numeral(BigInteger.ZERO)
							: mTheory.decimal(BigDecimal.ZERO);
						interpolant = negate ? mTheory.distinct(term, zero)
									: mTheory.equals(term, zero);
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
			if (ln.hasSourceAnnotation()) {
				SourceAnnotation annot = 
						(SourceAnnotation) ln.getTheoryAnnotation();
				int partition = mPartitions.containsKey(annot.getAnnotation())
						? mPartitions.get(annot.getAnnotation()) : 0;
				for (int i = 0; i < root.getSize(); i++) {
					Literal lit = root.getLiteral(i);
					DPLLAtom atom = lit.getAtom();
					LitInfo info = mLiteralInfos.get(atom);
					if (info == null) {
						info = new LitInfo();
						mLiteralInfos.put(atom, info);
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
				colorLiterals(a.mAntecedent, visited);
			}
		}
	}


	Occurrence getOccurrence(SharedTerm shared) {
		Occurrence result = mSymbolPartition.get(shared);
		if (result == null) {
			result = new Occurrence();
			IAnnotation annot = shared.getAnnotation();
			// TODO Here we need to change something if we have quantifiers.
			if (annot instanceof SourceAnnotation) {
				Integer partition = mPartitions.get(
						((SourceAnnotation) annot).getAnnotation());
				if (partition == null) {
					for (int p = 0; p < mNumInterpolants;p++)
						result.occursIn(p);
				} else
					result.occursIn(partition);
			}
			mSymbolPartition.put(shared, result);
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
		LitInfo result = mLiteralInfos.get(lit);
		if (result == null)
			result = colorMixedLiteral(lit);
		return result;
	}
	
	/**
	 * Compute the LitInfo for a mixed Literal.
	 */
	public LitInfo colorMixedLiteral(DPLLAtom atom) {
		LitInfo info = mLiteralInfos.get(atom);

		assert info == null;

		ArrayList<SharedTerm> subterms = new ArrayList<SharedTerm>();
		/* The sort of the auxiliary variable created for this atom.  We need
		 * this since we internally represent integral constants in LIRA logics
		 * as Int even if they should have sort Real. 
		 */
		Sort auxSort;
		if (atom instanceof CCEquality) {
			CCEquality eq = (CCEquality)atom;
			SharedTerm l = eq.getLhs().getFlatTerm();
			SharedTerm r = eq.getRhs().getFlatTerm();
			subterms.add(l);
			subterms.add(r);
			if (l.getSort() == r.getSort())
				auxSort = l.getSort();
			else {
				assert mTheory.getLogic().isIRA();
				// IRA-Hack
				auxSort = mTheory.getRealSort();
			}
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
			boolean allInt = true;
			for (LinVar c : components) {
				// IRA-Hack
				allInt &= c.isInt();
				subterms.add(c.getSharedTerm());
			}
			auxSort = allInt ? mTheory.getNumericSort() : mTheory.getRealSort();
		}
		info = computeMixedOccurrence(subterms);
		this.mLiteralInfos.put(atom, info);
		
		BitSet shared = new BitSet();
		shared.or(info.mInA);
		shared.or(info.mInB);
		if (shared.nextClearBit(0) >= mNumInterpolants)
			return info;

		info.mMixedVar = mTheory.createFreshTermVariable("litaux", auxSort);
		
		if (atom instanceof CCEquality) {
			CCEquality eq = (CCEquality)atom;
			info.mLhsOccur = getOccurrence(eq.getLhs().getFlatTerm());
		} else if (atom instanceof BoundConstraint
		        || atom instanceof LAEquality) {
			LinVar lv = null;
			if (atom instanceof BoundConstraint) 
				lv = ((BoundConstraint) atom).getVar();
			else
				lv = ((LAEquality) atom).getVar();
			assert lv.isInitiallyBasic() : "Not initially basic: " + lv + " atom: " + atom;

			info.mAPart = new MutableAffinTerm[mNumInterpolants];
			for (int part = 0; part < mNumInterpolants; part++) {
				if (!info.isMixed(part))
					continue;
			
				MutableAffinTerm sumApart = new MutableAffinTerm();	
				for (Entry<LinVar, BigInteger> en : lv.getLinTerm().entrySet()) {
					LinVar var = en.getKey();
					Occurrence occ = 
						mSymbolPartition.get(en.getKey().getSharedTerm());
					if (occ.isALocal(part)) {
						Rational coeff = 
								Rational.valueOf(en.getValue(), BigInteger.ONE);
						sumApart.add(coeff, var);
					}
				}
				
				info.mAPart[part] = sumApart;				
			}
		}
		return info;
	}

	private LitInfo computeMixedOccurrence(ArrayList<SharedTerm> subterms) {
		LitInfo info;
		BitSet inA = null, inB = null;
		for (SharedTerm st : subterms) {
			Occurrence occInfo = getOccurrence(st);
			if (inA == null) {
				inA = (BitSet) occInfo.mInA.clone(); 
				inB = (BitSet) occInfo.mInB.clone(); 
			} else {
				inA.and(occInfo.mInA);
				inB.and(occInfo.mInB);
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
		TermVariable mTermVar;
		Term mReplacement;
		
		public Substitutor(TermVariable termVar, Term replacement) {
			this.mTermVar = termVar;
			this.mReplacement = replacement;
		}
		
		public void convert(Term term) {
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				final Term[] oldTerms = laTerm.mS.getSummands().keySet()
						.toArray(new Term[laTerm.mS.getSummands().size()]);
				/* recurse into LA term */ 
				enqueueWalker(new Walker() {
					@Override
					public void walk(NonRecursive engine) {
						Substitutor me = (Substitutor) engine;
						Term result = me.getConverted();
						Term[] newTerms = me.getConverted(oldTerms);
						if (result == laTerm.mF && newTerms == oldTerms) {
							me.setResult(laTerm);
							return;
						}
						InterpolatorAffineTerm newS = 
								new InterpolatorAffineTerm();
						for (int i = 0; i < oldTerms.length; i++) {
							newS.add(laTerm.mS.getSummands().get(oldTerms[i]), 
									newTerms[i]);
						}
						newS.add(laTerm.mS.getConstant());
						me.setResult(new LATerm(newS, laTerm.mK, result));
					}
				});
				pushTerm(laTerm.mF);
				pushTerms(oldTerms);
				return;
			} else if (term.equals(mTermVar))
				setResult(mReplacement);
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
		Interpolant mI2;
		TermVariable mAuxVar;
		
		EQInterpolator(Interpolant i2, TermVariable auxVar) {
			mI2 = i2;
			mAuxVar = auxVar;
		}
		
		public void convert(Term term) {
			assert term != mAuxVar;
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				/* recurse into LA term */ 
				enqueueWalker(new Walker() {
					@Override
					public void walk(NonRecursive engine) {
						EQInterpolator me = (EQInterpolator) engine;
						Term result = me.getConverted();  
						if (result == laTerm.mF)
							me.setResult(laTerm);
						else
							me.setResult(new LATerm(laTerm.mS, laTerm.mK, result));
					}
				});
				pushTerm(laTerm.mF);
				return;
			} else if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getParameters().length == 2 
					&& (appTerm.getParameters()[0] == mAuxVar
					 || appTerm.getParameters()[1] == mAuxVar)) {
					assert appTerm.getFunction().isIntern()
						&& appTerm.getFunction().getName().equals("=")
						&& appTerm.getParameters().length == 2;
					
					Term s = appTerm.getParameters()[1];
					if (s == mAuxVar)
						s = appTerm.getParameters()[0];
					setResult(substitute(mI2.mTerm, mAuxVar, s));
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
		return new Interpolant(ipolator.transform(eqIpol.mTerm));
	}
	
	static abstract class MixedLAInterpolator extends TermTransformer {
		TermVariable mMixedVar;
		Term mI2;
		LATerm mLA1;
		
		public MixedLAInterpolator(Term i2, TermVariable mixed) {
			mMixedVar = mixed;
			mLA1 = null;
			mI2 = i2;
		}

		abstract Term interpolate(LATerm la1, LATerm la2);
		
		public void convert(Term term) {
			assert term != mMixedVar;
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				if (laTerm.mS.getSummands().get(mMixedVar) != null) { // NOPMD
					if (mLA1 == null) {
						/* We are inside I1. Remember the lainfo and push I2 
						 * on the convert stack.  Also enqueue a walker that
						 * will remove m_LA1 once we are finished with I2.
						 */
						beginScope();
						mLA1 = laTerm;
						enqueueWalker(new Walker() {
							@Override
							public void walk(NonRecursive engine) {
								((MixedLAInterpolator) engine).mLA1 = null;
								((MixedLAInterpolator) engine).endScope();
							}
						});
						pushTerm(mI2);
						return;
					} else {
						/* We are inside I2. Interpolate the LAInfos.
						 */
						setResult(interpolate(mLA1, (LATerm) term));
						return;
					}
				} else {
					/* this is a LA term not involving the mixed variable */ 
					enqueueWalker(new Walker() {
						@Override
						public void walk(NonRecursive engine) {
							MixedLAInterpolator me = (MixedLAInterpolator) engine;
							Term result = me.getConverted();
							if (result == laTerm.mF)
								me.setResult(laTerm);
							else
								me.setResult(
								        new LATerm(laTerm.mS, laTerm.mK, result));
						}
					});
					pushTerm(laTerm.mF);
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
			InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(la1.mS);
			Rational               c1 = s1.getSummands().remove(mMixedVar);
			InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(la2.mS);
			Rational               c2 = s2.getSummands().remove(mMixedVar);
			assert (c1.signum() * c2.signum() == -1);
			InfinitNumber newK = la1.mK.mul(c2.abs())
					.add(la2.mK.mul(c1.abs()));

			//compute c1s2 + c2s1
			InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(c1.abs(), s2);
			c1s2c2s1.add(c2.abs(), s1);

			Term newF;
			if (s1.getConstant().mEps > 0
				|| s2.getConstant().mEps > 0) {
				// One of the inequalities is strict.  In this case
				// c1s2c2s1 must also be a strict inequality and it is not
				// possible that c1s2c2s1 == 0 holds. Hence, we do not need
				// to substitute a shared term.
				newF = c1s2c2s1.toLeq0(mTheory);
				newK = InfinitNumber.EPSILON.negate();
			} else if (la1.mK.less(InfinitNumber.ZERO)) {
				//compute -s1/c1
				InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.mul(c1.inverse().negate());
				Term s1DivByc1 = s1divc1.toSMTLib(mTheory, false);
				newF = substitute(la2.mF, mMixedVar, s1DivByc1);
				newK = la2.mK;
			} else if (la2.mK.less(InfinitNumber.ZERO)) {
				//compute s2/c2
				InterpolatorAffineTerm s2divc2 = new InterpolatorAffineTerm(s2);
				s2divc2.mul(c2.inverse().negate());
				Term s2DivByc2 = s2divc2.toSMTLib(mTheory, false);
				newF = substitute(la1.mF, mMixedVar, s2DivByc2);
				newK = la1.mK;
			} else {
				InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.mul(c1.inverse().negate());
				Term s1DivByc1 = s1divc1.toSMTLib(mTheory, false);
				Term f1 = substitute(la1.mF, mMixedVar, s1DivByc1);
				Term f2 = substitute(la2.mF, mMixedVar, s1DivByc1);
				newF = mTheory.and(f1, f2);
				if (c1s2c2s1.isConstant()) {
					if (c1s2c2s1.getConstant().less(InfinitNumber.ZERO))
						newF = mTheory.mTrue;
				} else {
					InterpolatorAffineTerm s3 =
							new InterpolatorAffineTerm(c1s2c2s1);
					s3.add(InfinitNumber.EPSILON);
					newF = mTheory.or(s3.toLeq0(mTheory), newF);
				}
				newK = InfinitNumber.ZERO;
			}
			LATerm la3 = new LATerm(c1s2c2s1, newK, newF);
			return la3;
		}
	}

	class IntegerInterpolator extends MixedLAInterpolator {
		
		public IntegerInterpolator(Term i2, TermVariable mixedVar) {
			super(i2, mixedVar);
		}
		
		public Term interpolate(LATerm la1, LATerm la2) {
			//retrieve c1,c2,s1,s2
			InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(la1.mS);
			Rational               c1 = s1.getSummands().remove(mMixedVar);
			InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(la2.mS);
			Rational               c2 = s2.getSummands().remove(mMixedVar);
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
			InfinitNumber newK = la1.mK.mul(absc2).add(la2.mK.mul(absc1))
					.add(new InfinitNumber(c1c2, 0));
			assert newK.isIntegral();
			
			Rational k1c1 = la1.mK.mA.add(Rational.ONE).div(absc1).floor();
			Rational k2c2 = la2.mK.mA.add(Rational.ONE).div(absc2).floor();
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
			Term newF = mTheory.mFalse;
			// Use -s/c as start value.
			InterpolatorAffineTerm sPlusOffset = new InterpolatorAffineTerm();
			sPlusOffset.add(theC.signum() > 0 ? Rational.MONE : Rational.ONE, theS);
			Rational offset = Rational.ZERO;
			if (theC.signum() < 0)
				sPlusOffset.add(theC.abs().add(Rational.MONE));
			while (offset.compareTo(kc) <= 0) {
				Term x;
				x = sPlusOffset.toSMTLib(mTheory, true);
				if (!cNum.equals(BigInteger.ONE))
					x = mTheory.term("div", x, mTheory.numeral(cNum));
				Term F1 = substitute(la1.mF, mMixedVar, x);
				Term F2 = substitute(la2.mF, mMixedVar, x);
				
				if (offset.compareTo(kc) == 0) {
					if (theS == s1)
						F1 = mTheory.mTrue;
					else
						F2 = mTheory.mTrue;
				}
				newF = mTheory.or(newF, mTheory.and(F1, F2));
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
			ipolator = new RealInterpolator(sgItp.mTerm, mixedVar);
		else
			ipolator = new IntegerInterpolator(sgItp.mTerm, mixedVar);
		Interpolant newI = new Interpolant(ipolator.transform(leqItp.mTerm));
		return newI;
	}
}


