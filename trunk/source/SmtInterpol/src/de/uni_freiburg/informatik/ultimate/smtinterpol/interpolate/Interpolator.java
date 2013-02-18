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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
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

	Logger m_Logger;
	Theory m_Theory;
	int m_NumInterpolants;
	int[] m_startOfSubtrees;
	HashMap<SharedTerm, Occurrence> m_SymbolPartition;
	HashMap<DPLLAtom, LitInfo> m_LiteralInfos;
	HashMap<String, Integer> m_Partitions;
	HashMap<Clause, Interpolant[]> m_Interpolants;
	
	

	public Interpolator(Logger logger, Theory theory, 
			Set<String>[] partitions, int[] startOfSubTrees) {
		m_Partitions = new HashMap<String, Integer>();
		for (int i = 0; i < partitions.length; i++) {
			Integer part = i;
			for (String name: partitions[i]) {
				m_Partitions.put(name, part);
			}
		}
		m_Logger = logger;
		m_Theory = theory;
		m_NumInterpolants = partitions.length - 1;

		m_startOfSubtrees = startOfSubTrees;
		m_SymbolPartition = new HashMap<SharedTerm, Occurrence>();
		m_LiteralInfos = new HashMap<DPLLAtom, LitInfo>();
		m_Interpolants = new HashMap<Clause,Interpolant[]>();
	}
	public Interpolator(Logger logger, Theory theory, 
			Set<String>[] partitions, Clausifier clausifier) {
		this(logger, theory, partitions, new int[partitions.length]);
	}

	private Term unfoldLAs(Interpolant interpolant) {
		FormulaSubstitutor substitutor = new FormulaSubstitutor();
		for (Entry<TermVariable, LAInfo> en : interpolant.m_VarToLA.entrySet())
			substitutor.addSubstitution(en.getKey(), en.getValue().m_F);
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
			for (int i = 0; i < m_NumInterpolants; i++) {
				interpolants[i] = new Interpolant(primInterpolants[i].m_term);
				interpolants[i].m_VarToLA = 
					new HashMap<TermVariable,LAInfo>(primInterpolants[i].m_VarToLA);
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
						mergeLAHashMaps(interpolants[i], assInterp[i]);
					} else if (pivInfo.isBLocal(i)) {
						interpolants[i].m_term = 
								m_Theory.and(interpolants[i].m_term, assInterp[i].m_term);
						mergeLAHashMaps(interpolants[i], assInterp[i]);
					} else if (pivInfo.isAB(i)) {
						interpolants[i].m_term = 
								m_Theory.ifthenelse(pivot.getSMTFormula(m_Theory), 
										interpolants[i].m_term, assInterp[i].m_term);
						mergeLAHashMaps(interpolants[i], assInterp[i]);
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

	private Interpolant mixedEqInterpolate(final Interpolant eqIpol,
			final Interpolant neqIpol, final TermVariable mixedVar) {
		final Interpolant newI = new Interpolant();
		final HashMap<TermVariable,TermVariable> tvSubst = 
				new HashMap<TermVariable,TermVariable>();
		final ArrayDeque<TermVariable> todoStack = new ArrayDeque<TermVariable>();
		TermTransformer substitutor = new TermTransformer() {

			public void convert(Term term) {
				assert term != mixedVar;
				if (term instanceof ApplicationTerm) {
					ApplicationTerm appTerm = (ApplicationTerm) term;
					if (appTerm.getParameters().length == 2 && 
						(appTerm.getParameters()[0] == mixedVar
						 || appTerm.getParameters()[1] == mixedVar)) {
						assert appTerm.getFunction().isIntern()
							&& appTerm.getFunction().getName().equals("=")
							&& appTerm.getParameters().length == 2;
						
						Term s = appTerm.getParameters()[1];
						if (s == mixedVar)
							s = appTerm.getParameters()[0];
						setResult(m_Theory.let(mixedVar, s, neqIpol.m_term));
						return;
					}
				} else if (term instanceof TermVariable) {
					TermVariable origVar = (TermVariable) term;
					TermVariable newVar = tvSubst.get(origVar);
					if (newVar == null && eqIpol.m_VarToLA.containsKey(origVar)) {
						newVar = m_Theory.createFreshTermVariable("LA4", origVar.getSort());
						tvSubst.put(origVar, newVar);
						todoStack.add(origVar);
					}
					if (newVar != null)
						term = newVar;
				} else if (term instanceof LetTerm) {
					LetTerm let = (LetTerm) term;
					for (TermVariable tv : let.getVariables()) {
						if (tv == mixedVar) {
							setResult(term);
							return;
						}
					}
				}
				super.convert(term);
			}
		};
		
		newI.m_term = substitutor.transform(eqIpol.m_term);
		newI.m_VarToLA.putAll(eqIpol.m_VarToLA);
		while (!todoStack.isEmpty()) {
			TermVariable origTV = todoStack.removeFirst();
			LAInfo la = eqIpol.m_VarToLA.get(origTV);
			LAInfo newLa = new LAInfo(la.m_s, la.m_k, substitutor.transform(la.m_F));
			newI.m_VarToLA.remove(origTV);
			newI.m_VarToLA.put(tvSubst.get(origTV), newLa);
		}
		newI.m_VarToLA.putAll(neqIpol.m_VarToLA);
		return newI;
	}
	
	/**
	 * the result of the merge is saved in ip1 (TODO vllt doch inlinen..)
	 * @param ip1
	 * @param ip2
	 */
	public void mergeLAHashMaps(Interpolant ip1, Interpolant ip2) {
		ip1.m_VarToLA.putAll(ip2.m_VarToLA);
	}

	/**
	 * Substitute termVar by replacement in mainTerm
	 * @param mainTerm
	 * @param replacement
	 * @param termVar
	 * @return substituted Term
	 */
	Term substitute(Term mainTerm, final Term replacement,
			final TermVariable termVar) {
		boolean termVarIsFree = false;
		for (TermVariable t : mainTerm.getFreeVars()) {
			if(t.equals(termVar))
				termVarIsFree = true;
		}
		if(!termVarIsFree)
			return mainTerm;

		return new TermTransformer() {
			public void convert(Term term) {
				if (term.equals(termVar))
					setResult(replacement);
				else
					super.convert(term);
			}
		}.transform(mainTerm);
	}

	public void colorLiterals(Clause root, HashSet<Clause> visited) {
		if (visited.contains(root))
			return;
		visited.add(root);
		ProofNode pn = root.getProof();
		if (pn.isLeaf()) {
			LeafNode ln = (LeafNode) pn;
			if (ln.getLeafKind() == LeafNode.NO_THEORY) {
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
				int partition = m_Partitions.get(
						((SourceAnnotation) annot).getAnnotation());
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

	Interpolant mixedPivotRuleReal(Interpolant leqItp, Interpolant sgItp,
			TermVariable mixedVar) {
		Interpolant newI = new Interpolant(leqItp.m_term);

		newI.m_VarToLA = new HashMap<TermVariable, LAInfo>(leqItp.m_VarToLA);
		newI.m_VarToLA.putAll(sgItp.m_VarToLA);

		for (Entry<TermVariable,LAInfo> entry1 : leqItp.m_VarToLA.entrySet()) {
			LAInfo la1 = entry1.getValue();
			if (!la1.m_s.getSummands().containsKey(mixedVar)) {
				newI.m_VarToLA.put(entry1.getKey(), entry1.getValue());
				continue;
			}
			Term currentI2Term = sgItp.m_term; 
			newI.m_VarToLA.remove(la1);

			for (Entry<TermVariable,LAInfo> entry2 : sgItp.m_VarToLA.entrySet()) {
				LAInfo la2 = entry2.getValue();
				if (!la2.m_s.getSummands().containsKey(mixedVar)) {
					newI.m_VarToLA.put(entry2.getKey(), entry2.getValue());
					continue;
				}
				newI.m_VarToLA.remove(la2);
				TermVariable currentLA3TV = m_Theory.createFreshTermVariable(
						"LA3", m_Theory.getBooleanSort());

				//retrieve c1,c2,s2,s2
				InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(la1.m_s);
				Rational               c1 = s1.getSummands().remove(mixedVar);
				InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(la2.m_s);
				Rational               c2 = s2.getSummands().remove(mixedVar);
				assert (c1.signum() * c2.signum() == -1);
				InfinitNumber newK = la1.m_k.mul(c2.abs())
						.add(la2.m_k.mul(c1.abs()));

				//compute c1s2 + c2s1
				InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
				c1s2c2s1.add(c1.abs(), s2);
				c1s2c2s1.add(c2.abs(), s1);

				Term newF;
				if (la1.m_k.less(InfinitNumber.ZERO)) {
					//compute -s1/c1
					InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
					s1divc1.mul(c1.inverse().negate());
					Term s1DivByc1 = s1divc1.toSMTLib(m_Theory, false);
					newF = substitute(la2.m_F, s1DivByc1, mixedVar);
					newK = la2.m_k;
				} else {
					assert (la2.m_k.less(InfinitNumber.ZERO));
					//compute s2/c2
					InterpolatorAffineTerm s2divc2 = new InterpolatorAffineTerm(s2);
					s2divc2.mul(c2.inverse().negate());
					Term s2DivByc2 = s2divc2.toSMTLib(m_Theory, false);
					newF = substitute(la1.m_F, s2DivByc2, mixedVar);
					newK = la1.m_k;
				}
				LAInfo la3 = new LAInfo(c1s2c2s1, newK, newF);
				newI.m_VarToLA.put(currentLA3TV, la3);

				currentI2Term = substitute(currentI2Term, currentLA3TV, entry2.getKey());
			}

			newI.m_term = substitute(newI.m_term, currentI2Term, entry1.getKey());
		}
		return newI;
	}

	Interpolant mixedPivotRuleInt(Interpolant leqItp, Interpolant sgItp,
			TermVariable mixedVar) {
		Interpolant newI = new Interpolant(leqItp.m_term);
		newI.m_VarToLA = new HashMap<TermVariable,LAInfo>();

		for (Entry<TermVariable,LAInfo> entry1 : leqItp.m_VarToLA.entrySet()) {
			LAInfo la1 = entry1.getValue();
			if (!la1.m_s.getSummands().containsKey(mixedVar)) {
				newI.m_VarToLA.put(entry1.getKey(), entry1.getValue());
				continue;
			}
			newI.m_VarToLA.remove(la1);
			Term currentI2Term = sgItp.m_term; 

			for (Entry<TermVariable,LAInfo> entry2 : sgItp.m_VarToLA.entrySet()) {
				LAInfo la2 = entry2.getValue();
				if (!la2.m_s.getSummands().containsKey(mixedVar)) {
					newI.m_VarToLA.put(entry2.getKey(), entry2.getValue());
					continue;
				}
				newI.m_VarToLA.remove(la2);
				TermVariable currentLA3TV = m_Theory.createFreshTermVariable(
						"LA3", m_Theory.getBooleanSort());

				//retrieve c1,c2,s1,s2
				InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(la1.m_s);
				Rational               c1 = s1.getSummands().remove(mixedVar);
				InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(la2.m_s);
				Rational               c2 = s2.getSummands().remove(mixedVar);
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
					Term F1 = substitute(la1.m_F, x, mixedVar);
					Term F2 = substitute(la2.m_F, x, mixedVar);
					
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
				
				LAInfo la3 = new LAInfo(c1s2c2s1, newK, newF);
				newI.m_VarToLA.put(currentLA3TV, la3);

				currentI2Term = substitute(currentI2Term, currentLA3TV, entry2.getKey());
			}

			newI.m_term = substitute(newI.m_term, currentI2Term, entry1.getKey());
		}
		return newI;
	}

	public Interpolant mixedPivotLA(Interpolant leqItp,
			Interpolant sgItp, TermVariable mixedVar) {
		if (mixedVar.getSort().getName().equals("Real"))
			return mixedPivotRuleReal(leqItp, sgItp, mixedVar);
		else
			return mixedPivotRuleInt(leqItp, sgItp, mixedVar);
	}
}


