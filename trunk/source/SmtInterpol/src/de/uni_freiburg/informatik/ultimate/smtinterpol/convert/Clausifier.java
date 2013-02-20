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

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.QuantifiedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.NoopProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;
import de.uni_freiburg.informatik.ultimate.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * Utility to convert an arbitrary term into CNF and insert it into SMTInterpol.
 * @author Juergen Christ
 */
public class Clausifier {

	public class CCTermBuilder {
		private class BuildCCTerm implements Operation {
			private Term m_Term;
			public BuildCCTerm(Term term) {
				m_Term = term;
			}
			public void perform() {
				SharedTerm shared = getSharedTerm(m_Term, true);
				if (shared.m_ccterm != null)
					m_Converted.push(shared.m_ccterm);
				else {
					FunctionSymbol fs = getSymbol();
					if (fs == null) {
						// We have an intern function symbol
						CCTerm res = m_CClosure.createAnonTerm(shared);
						shared.setCCTerm(res);
						m_Converted.push(res);
					} else {
						m_Ops.push(new SaveCCTerm(shared));
						ApplicationTerm at = (ApplicationTerm) m_Term;
						Term[] args = at.getParameters();
						for (int i = args.length - 1; i >= 0; --i) {
							m_Ops.push(new BuildCCAppTerm(i != args.length - 1));
							m_Ops.push(new BuildCCTerm(args[i]));
						}
						m_Converted.push(m_CClosure.getFuncTerm(fs));
					}
				}
			}
			private FunctionSymbol getSymbol() {
				if (m_Term instanceof ApplicationTerm) {
					ApplicationTerm at = (ApplicationTerm) m_Term;
					FunctionSymbol fs = at.getFunction();
					// Don't descend into interpreted function symbols
					if (!fs.isInterpreted())
						return fs;
				}
				return null;
			}
		}
		private class SaveCCTerm implements Operation {
			private SharedTerm m_Shared;
			public SaveCCTerm(SharedTerm shared) {
				m_Shared = shared;
			}
			public void perform() {
				m_Shared.setCCTerm(m_Converted.peek());
				m_CClosure.addTerm(m_Shared.m_ccterm, m_Shared);
			}
		}
		/**
		 * Helper class to build the intermediate CCAppTerms.  Note that all
		 * these terms will be func terms.
		 * @author Juergen Christ
		 */
		private class BuildCCAppTerm implements Operation {
			private boolean m_IsFunc;
			public BuildCCAppTerm(boolean isFunc) {
				m_IsFunc = isFunc;
			}
			public void perform() {
				CCTerm arg = m_Converted.pop();
				CCTerm func = m_Converted.pop();
				m_Converted.push(m_CClosure.createAppTerm(m_IsFunc, func, arg));
			}
		}
		private ArrayDeque<Operation> m_Ops = new ArrayDeque<Operation>();
		private ArrayDeque<CCTerm> m_Converted = new ArrayDeque<CCTerm>();
		
		public CCTermBuilder() {
			if (m_CClosure == null) {
				// Delayed setup for @div0, @mod0, and @/0
				setupCClosure();
			}
		}
		
		public CCTerm convert(Term t) {
			m_Ops.push(new BuildCCTerm(t));
			while (!m_Ops.isEmpty())
				m_Ops.pop().perform();
			CCTerm res = m_Converted.pop();
			assert m_Converted.isEmpty();
			return res;
		}
	}
	
	/**
	 * Basic interface used to undo certain events related to the assertion
	 * stack.
	 * 
	 * Due to our instantiation mechanism, trail objects should only be used to
	 * undo changes related to push/pop and instantiations at the same time.
	 * @author Juergen Christ
	 */
	static abstract class TrailObject {
		private TrailObject m_Prev;
		protected TrailObject() {
			m_Prev = this;
		}
		protected TrailObject(TrailObject prev) {
			m_Prev = prev;
		}
		/**
		 * Undo an action performed since the corresponding push.
		 */
		public abstract void undo();
		public TrailObject getPrevious() {
			return m_Prev;
		}
		void setPrevious(TrailObject prev) {
			m_Prev = prev;
		}
		/**
		 * Is this the end of the scope.
		 * @return <code>true</code> if this object represents the end of a
		 * scope.
		 */
		public boolean isScopeMarker() {
			return false;
		}
	}
	/**
	 * Helper class to remove a theory added at some higher scope level.  This
	 * should be used with care.  It's mainly intended to remove the cclosure
	 * that was added because of a @/0, @div0, or @mod0 function symbol in pure
	 * linear arithmetic.
	 * 
	 * It is safe to do this as a trail object since we need a cclosure for all
	 * quantified theories.
	 * @author Juergen Christ
	 */
	private class RemoveTheory extends TrailObject {
		public RemoveTheory(TrailObject prev) {
			super(prev);
		}
		public void undo() {
			m_Engine.removeTheory();
		}
	}
	/**
	 * Mark the begin/end of a scope on the assertion stack.
	 * @author Juergen Christ
	 */
	private class ScopeMarker extends TrailObject {
		public ScopeMarker(TrailObject prev) {
			super(prev);
		}
		public void undo() {
			// Nothing to do here
		}
		public boolean isScopeMarker() {
			return true;
		}
	}
	
	private class RemoveClausifierInfo extends TrailObject {
		private Term m_Term;
		public RemoveClausifierInfo(TrailObject prev, Term term) {
			super(prev);
			m_Term = term;
		}
		public void undo() {
			m_ClauseData.remove(m_Term);
		}
	}
	
	private class RemoveFlag extends TrailObject {
		private ClausifierInfo m_Ci;
		private int m_Flag;
		public RemoveFlag(TrailObject prev, ClausifierInfo ci, int flag) {
			super(prev);
			m_Ci = ci;
			m_Flag = flag;
		}
		public void undo() {
			m_Ci.clearFlag(m_Flag);
		}
	}
	
	private class RemoveLiteral extends TrailObject {
		private ClausifierInfo m_Ci;
		public RemoveLiteral(TrailObject prev, ClausifierInfo ci) {
			super(prev);
			m_Ci = ci;
		}
		public void undo() {
			m_Ci.clearLiteral();
		}
	}
	
	private class RemoveAxiomProof extends TrailObject {
		private ClausifierInfo m_Ci;
		public RemoveAxiomProof(TrailObject prev, ClausifierInfo ci) {
			super(prev);
			m_Ci = ci;
		}
		public void undo() {
			m_Ci.clearAxiomProof();
		}
	}
	
	private class RemoveAtom extends TrailObject {
		private Term m_Term;
		public RemoveAtom(TrailObject prev, Term term) {
			super(prev);
			m_Term = term;
		}
		public void undo() {
			m_LiteralData.remove(m_Term);
		}
	}
	
	/**
	 * A helper class to remember whether a formula has been added as axioms or
	 * the corresponding aux axioms have been added.  This info also contains a
	 * field to mark the aux axioms as blocked.  We use this to prevent deletion
	 * of the aux axioms if the corresponding literal has been used to simplify
	 * clausification, i.e., we did not convert a top-level formula as axiom,
	 * but added the unit clause containing only the proxy literal.  For
	 * quantifier-free logics, this feature is unused since we do not run into
	 * problems with the assertion stack management.  If however a proxy was
	 * created as a result of a quantifier instantiation, the instantiation
	 * survives a push and an assertion on the next stacklevel triggers a
	 * simplification where we only use the proxy, we have to block all
	 * clauses defining the auxiliary literal.  This will prevent the deletion
	 * of the quantifier instantiation which however is a top-level assertion
	 * now. 
	 * @author Juergen Christ
	 */
	private static class ClausifierInfo {
		private static class ProofData {
			private Term m_Term;
			private Term m_AxiomProof;
			private IAnnotation m_Annot;
			private boolean m_Negated;
			public ProofData(Term term, Term axiomProof,
					IAnnotation annot, boolean neg) {
				m_Term = term;
				m_AxiomProof = axiomProof;
				m_Annot = annot;
				m_Negated = neg;
			}
		}
		static final int POS_AXIOMS_ADDED = 1;
		static final int NEG_AXIOMS_ADDED = 2;
		static final int POS_AUX_AXIOMS_ADDED = 4;
		static final int NEG_AUX_AXIOMS_ADDED = 8;
		private Literal m_Lit;
		private int m_Flags;
		private Object m_Proof;
		
		public ClausifierInfo() {
			m_Lit = null;
			m_Flags = 0;
		}
		
		public void setFlag(int flag) {
			m_Flags |= flag;
		}
		
		public void clearFlag(int flag) {
			m_Flags &= ~flag;
		}
		
		public boolean testFlags(int flag) {
			return (m_Flags & flag) != 0;
		}
		public Literal getLiteral() {
			return m_Lit;
		}
		public void setLiteral(Literal lit) {
			m_Lit = lit;
  		}
		public void clearLiteral() {
			m_Lit = null;
		}
		public void setAxiomProof(
				Term term, Term proof, IAnnotation annot, boolean negated) {
			if (proof == null)
				m_Proof = annot;
			else
				m_Proof = new ProofData(term, proof, annot, negated);
		}
		/// Debugging only
		boolean isAxiomProofAvailable() {
			return m_Proof != null;
		}
		public ProofNode getAxiomProof(
				IProofTracker tracker, Term idx, Literal lit) {
			if (m_Proof instanceof IAnnotation)
				return new LeafNode(LeafNode.NO_THEORY, (IAnnotation) m_Proof);
			ProofData pd = (ProofData) m_Proof;
			Theory t = pd.m_Term.getTheory();
			IProofTracker sub = tracker.getDescendent();
			Term unquoted = pd.m_Term;
			if (pd.m_Negated && testFlags(ClausifierInfo.POS_AXIOMS_ADDED))
				sub.negation(t.term(t.m_Not, unquoted), unquoted,
						ProofConstants.RW_NOT_SIMP);
			sub.intern(idx, lit);
			return new LeafNode(LeafNode.NO_THEORY,
					new SourceAnnotation((SourceAnnotation) pd.m_Annot,
							sub.clause(pd.m_AxiomProof)));
		}
		public void clearAxiomProof() {
			m_Proof = null;
		}
	}
	
	private interface Operation {
		public void perform();
	}
	
	private class AddAsAxiom implements Operation {
		/**
		 * The proof so far.
		 */
		private Term m_ProofTerm;
		/**
		 * The term to add as axiom.
		 */
		private Term m_Term;
		/**
		 * The polarity (true means negated).
		 */
		private boolean m_Negated;
		
		public AddAsAxiom(Term term, Term proofTerm) {
			this(term, false, proofTerm);
		}
		
		public AddAsAxiom(Term term, boolean negated, Term proofTerm) {
			m_Term = term;
			m_Negated = negated;
			m_ProofTerm = proofTerm;
		}
		
		@Override
		public void perform() {
			Term idx = toPositive(m_Term);
			ClausifierInfo ci = getInfo(idx);
			// idx != m_Term ==> additional negation
			// idx == m_Term ==> no additional negation
			boolean positive = (idx == m_Term) ^ m_Negated;
			int flag, auxflag, negflag;
			if (positive) {
				flag = ClausifierInfo.POS_AXIOMS_ADDED;
				auxflag = ClausifierInfo.POS_AUX_AXIOMS_ADDED;
				negflag = ClausifierInfo.NEG_AXIOMS_ADDED;
				if (m_Negated)
					// Here, we have !m_Term gets rewritten into idx
					m_Tracker.negation(m_Term, idx, ProofConstants.RW_NOT_SIMP);
			} else {
				flag = ClausifierInfo.NEG_AXIOMS_ADDED;
				auxflag = ClausifierInfo.NEG_AUX_AXIOMS_ADDED;
				negflag = ClausifierInfo.POS_AXIOMS_ADDED;
			}
			if (ci.testFlags(flag))
				// We've already added this formula as axioms
				return;
			if (ci.testFlags(negflag)) {
				// We've added the negation as axiom => Create empty clause
				if (m_Engine.isProofGenerationEnabled()) {
					// (@res sourceAnnot ci.getAxiomProof)
					Clause primary;
					Antecedent ante;
					NamedAtom idxAtom = new NamedAtom(idx, m_StackLevel);
					m_Tracker.quoted(idx, idxAtom);
					if (positive) {
						primary = new Clause(new Literal[] {idxAtom},
								getClauseProof(m_ProofTerm));
						ante = new Antecedent(idxAtom.negate(),
								new Clause(
										new Literal[] {idxAtom.negate()},
										ci.getAxiomProof(
												m_Tracker, idx, idxAtom)));
					} else {
						primary = new Clause(new Literal[] {idxAtom},
								ci.getAxiomProof(m_Tracker, idx, idxAtom));
						ante = new Antecedent(idxAtom.negate(),
								new Clause(
										new Literal[] {idxAtom.negate()},
										getClauseProof(m_ProofTerm)));
					}
					ResolutionNode rn = new ResolutionNode(primary,
							new Antecedent[] {ante});
					addClause(new Literal[0], null, rn);
				} else
					addClause(new Literal[0], null, m_Proof);
				return;
			}
			assert (!ci.isAxiomProofAvailable());
			ci.setAxiomProof(m_Term, m_ProofTerm, getAnnotation(), !positive);
			m_UndoTrail = new RemoveAxiomProof(m_UndoTrail, ci);
			Literal auxlit = ci.getLiteral();
			if (auxlit != null) {
				if (!ci.testFlags(auxflag))
					(new AddAuxAxioms(idx, auxlit, positive)).perform();
				m_Tracker.quoted(idx, auxlit.getAtom());
				addClause(new Literal[] {
						positive ? auxlit : auxlit.negate()},
						null, getClauseProof(m_ProofTerm));
				ci.setFlag(flag);
				m_UndoTrail = new RemoveFlag(m_UndoTrail, ci, flag);
				return;
			}
			ci.setFlag(flag);
			m_UndoTrail = new RemoveFlag(m_UndoTrail, ci, flag);
			Theory t = m_Term.getTheory();
			if (idx instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) idx;
				if (at.getFunction() == t.m_Or) {
					if (positive) {
						BuildClause bc = new BuildClause(m_ProofTerm);
						pushOperation(bc);
						for (Term p : at.getParameters())
							pushOperation(new CollectLiterals(p, bc));
					} else {
						for (Term p : at.getParameters())
							pushOperation(new AddAsAxiom(p, true,
									m_Tracker.split(p, m_ProofTerm,
											ProofConstants.SPLIT_NEG_OR)));
					}
				} else if (!at.getFunction().isIntern() &&
						at.getFunction().getReturnSort() == t.getBooleanSort()) {
					Literal lit = createBooleanLit(at);
					IProofTracker sub = m_Tracker.getDescendent();
					sub.intern(at, lit);
					addClause(new Literal[] {positive ? lit : lit.negate()},
							null, getProofNewSource(sub.clause(m_ProofTerm)));
			    } else if (at.getFunction().getName().equals("=")) {
					Term lhs = at.getParameters()[0];
					Term rhs = at.getParameters()[1];
					if (lhs.getSort() == t.getBooleanSort()) {
						BuildClause bc1 = new BuildClause(LeafNode.NO_THEORY);
						pushOperation(bc1);
						if (positive) {
							bc1.setProofTerm(m_Tracker.split(at, m_ProofTerm,
										ProofConstants.SPLIT_POS_EQ_1));
							pushOperation(new CollectLiterals(lhs, bc1));
							pushOperation(new CollectLiterals(
									new Utils(bc1.getTracker()).createNot(rhs),
									bc1));
						} else {
							bc1.setProofTerm(m_Tracker.split(at, m_ProofTerm,
									ProofConstants.SPLIT_NEG_EQ_1));
							pushOperation(new CollectLiterals(lhs, bc1));
							pushOperation(new CollectLiterals(rhs, bc1));
						}
						BuildClause bc2 = new BuildClause(LeafNode.NO_THEORY);
						pushOperation(bc2);
						Utils tmp = new Utils(bc2.getTracker());
						if (positive) {
							bc2.setProofTerm(m_Tracker.split(at, m_ProofTerm,
									ProofConstants.SPLIT_POS_EQ_2));
							pushOperation(new CollectLiterals(
									tmp.createNot(lhs), bc2));
							pushOperation(new CollectLiterals(rhs, bc2));
						} else {
							bc2.setProofTerm(m_Tracker.split(at, m_ProofTerm,
								ProofConstants.SPLIT_NEG_EQ_2));
							pushOperation(new CollectLiterals(
									tmp.createNot(lhs), bc2));
							pushOperation(new CollectLiterals(
									tmp.createNot(rhs), bc2));
						}
					} else {
						SharedTerm slhs = getSharedTerm(lhs);
						SharedTerm srhs = getSharedTerm(rhs);
						EqualityProxy eq = createEqualityProxy(slhs, srhs);
						// eq == true and positive ==> return
						// eq == true and !positive ==> addClause({})
						// eq == false and !positive ==> return
						// eq == false and positive ==> addClause({})
						if (eq == EqualityProxy.getTrueProxy()) {
							if (!positive) {
								// eq-tracking done by createEqualityProxy
								m_Tracker.negation(m_Theory.TRUE,
										m_Theory.FALSE,
										ProofConstants.RW_NOT_SIMP);
								addClause(new Literal[0], null, 
										getClauseProof(m_ProofTerm));
							}
							return;
						}
						if (eq == EqualityProxy.getFalseProxy()) {
							if (positive) {
								// eq-tracking done by createEqualityProxy
								addClause(new Literal[0], null, 
										getClauseProof(m_ProofTerm));
							}
							return;
						}
						Literal lit = eq.getLiteral();
						IProofTracker sub = m_Tracker.getDescendent();
						sub.intern(at, lit);
						addClause(new Literal[] {
							!positive ? lit.negate() : lit}, null, 
								getProofNewSource(sub.clause(m_ProofTerm)));
					}
				} else if (at.getFunction().getName().equals("ite")) {
					assert at.getFunction().getReturnSort() == t.getBooleanSort();
					Term cond = at.getParameters()[0];
					Term thenForm = at.getParameters()[1];
					Term elseForm = at.getParameters()[2];
					int kind1 = ProofConstants.SPLIT_POS_ITE_1;
					int kind2 = ProofConstants.SPLIT_POS_ITE_2;
					BuildClause bc1, bc2;
					if (!positive) {
						kind1 = ProofConstants.SPLIT_NEG_ITE_1;
						kind2 = ProofConstants.SPLIT_NEG_ITE_2;
					}
					bc1 = new BuildClause(
							m_Tracker.split(at, m_ProofTerm, kind1));
					Utils tmp1 = new Utils(bc1.getTracker());
					pushOperation(bc1);
					pushOperation(new CollectLiterals(
							tmp1.createNot(cond), bc1));
					if (!positive)
						thenForm = tmp1.createNot(thenForm);
					tmp1 = null;
					pushOperation(new CollectLiterals(thenForm, bc1));
					bc2 = new BuildClause(
							m_Tracker.split(at, m_ProofTerm, kind2));
					Utils tmp2 = new Utils(bc2.getTracker());
					pushOperation(bc2);
					pushOperation(new CollectLiterals(cond, bc2));
					if (!positive)
						elseForm = tmp2.createNot(elseForm);
					tmp2 = null;
					pushOperation(new CollectLiterals(elseForm, bc2));
				} else if (at.getFunction().getName().equals("<=")) {
					// (<= SMTAffineTerm 0)
					Literal lit = createLeq0(at);
					IProofTracker sub = m_Tracker.getDescendent();
					sub.intern(at, lit);
					if (lit.getSign() == -1 && !positive)
						sub.negateLit(lit, m_Theory);
					addClause(new Literal[] {positive ? lit : lit.negate()},
							null, getProofNewSource(sub.clause(m_ProofTerm)));
				} else if (at == t.TRUE) {
					// Nothing to do...
				} else if (at == t.FALSE) {
					addClause(new Literal[0], null,
							getClauseProof(m_ProofTerm));
				} else {
					throw new InternalError("Not implementd: " +
							SMTAffineTerm.cleanup(at));
				}
				// TODO Fix Quantifiers once supported
//			} else if (m_Term instanceof QuantifiedFormula) {
//				QuantifiedFormula qf = (QuantifiedFormula) m_Term;
//				assert qf.getQuantifier() == QuantifiedFormula.EXISTS;
//				if (!positive) {
//					TermVariable[] vars = qf.getVariables();
//					Term[] skolems = new Term[vars.length];
//					for (int i = 0; i < skolems.length; ++i)
//						skolems[i] = t.term(t.skolemize(vars[i]));
//					Term skolem;
//					m_Unlet.beginScope();
//					try {
//						m_Unlet.addSubstitutions(
//							new ArrayMap<TermVariable, Term>(vars, skolems));
//						Term negSkolem = m_Unlet.unlet(qf.getSubformula());
//						skolem = Utils.createNot(negSkolem);
//					} finally {
//						m_Unlet.endScope();
//					}
//					skolem = m_Compiler.transform(skolem);
//					// TODO Annotation processing
//					pushOperation(new AddAsAxiom(skolem));
//				} else {
//					// TODO Quantifier optimization, pattern inference...
//				}
			} else
				throw new InternalError(
						"Don't know how to convert into axiom: " +
						SMTAffineTerm.cleanup(m_Term));
		}
		
	}
	private class AddAuxAxioms implements Operation {
		
		private Term m_Term;
		private Literal m_AuxLit;
		private boolean m_Positive;

		public AddAuxAxioms(Term term, Literal lit, boolean pos) {
			assert(term == toPositive(term));
			m_Term = term;
			m_AuxLit = lit;
			m_Positive = pos;
		}

		@Override
		public void perform() {
			ClausifierInfo ci = getInfo(m_Term);
			int auxflag, flag, negflag;
			if (m_Positive) {
				auxflag = ClausifierInfo.POS_AUX_AXIOMS_ADDED;
				flag = ClausifierInfo.POS_AXIOMS_ADDED;
				negflag = ClausifierInfo.NEG_AXIOMS_ADDED;
			} else {
				auxflag = ClausifierInfo.NEG_AUX_AXIOMS_ADDED;
				flag = ClausifierInfo.NEG_AXIOMS_ADDED;
				negflag = ClausifierInfo.POS_AXIOMS_ADDED;
			}
			if (ci.testFlags(auxflag))
				// We've already added the aux axioms
				// Nothing to do
				return;
			if (ci.testFlags(flag)) {
				/*
				 * If we know that the axiom already holds, the aux axioms
				 * trivially simplify to true.
				 * Hence, we don't need them at all.
				 */
				return;
			}
			ci.setFlag(auxflag);
			m_UndoTrail = new RemoveFlag(m_UndoTrail, ci, auxflag);
			if (ci.testFlags(negflag)) {
				// simplify by asserting the proxy as unit.
				Literal[] unit = new Literal[] {
						m_Positive ? m_AuxLit.negate() : m_AuxLit
				};
				if (m_Engine.isProofGenerationEnabled()) {
					addClause(unit, null,
							ci.getAxiomProof(m_Tracker, m_Term, m_AuxLit));
				} else {
					addClause(unit, null, m_Proof);
				}
				return;
			}
			Theory t = m_Term.getTheory();
			if (m_Term instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) m_Term;
				if (at.getFunction() == t.m_Or) {
					if (m_Positive) {
						BuildClause bc = new BuildClause(
								ProofConstants.AUX_OR_POS);
						bc.auxAxiom(m_AuxLit, at, null, null);
						bc.addLiteral(m_AuxLit.negate());
						pushOperation(bc);
						for (Term param : at.getParameters())
							pushOperation(new CollectLiterals(param, bc));
					} else {
						CreateNegClauseAuxAxioms helper =
							new CreateNegClauseAuxAxioms(m_AuxLit);
						pushOperation(helper);
						helper.init(m_Term);
					}
				} else if (at.getFunction().getName().equals("ite")) {
					Term cond = at.getParameters()[0];
					Term thenTerm = at.getParameters()[1];
					Term elseTerm = at.getParameters()[2];
					if (m_Positive) {
						BuildClause bc1 = new BuildClause(
								ProofConstants.AUX_ITE_POS_1);
						bc1.auxAxiom(m_AuxLit, at, null, null);
						bc1.addLiteral(m_AuxLit.negate());
						pushOperation(bc1);
						pushOperation(new CollectLiterals(thenTerm, bc1));
						pushOperation(new CollectLiterals(
								new Utils(bc1.getTracker()).createNot(cond),
								bc1));
						BuildClause bc2 = new BuildClause(
								ProofConstants.AUX_ITE_POS_2);
						bc2.auxAxiom(m_AuxLit, at, null, null);
						bc2.addLiteral(m_AuxLit.negate());
						pushOperation(bc2);
						pushOperation(new CollectLiterals(elseTerm, bc2));
						pushOperation(new CollectLiterals(cond, bc2));
						if (Config.REDUNDANT_ITE_CLAUSES) {
							BuildClause bc3 = new BuildClause(
									ProofConstants.AUX_ITE_POS_RED);
							bc3.auxAxiom(m_AuxLit, at, null, null);
							bc3.addLiteral(m_AuxLit.negate());
							pushOperation(bc3);
							pushOperation(new CollectLiterals(elseTerm, bc3));
							pushOperation(new CollectLiterals(thenTerm, bc3));
						}
					} else {
						BuildClause bc1 = new BuildClause(
								ProofConstants.AUX_ITE_NEG_1);
						Utils tmp1 = new Utils(bc1.getTracker());
						bc1.auxAxiom(m_AuxLit, at, null, null);
						bc1.addLiteral(m_AuxLit);
						pushOperation(bc1);
						pushOperation(new CollectLiterals(
								tmp1.createNot(thenTerm), bc1));
						pushOperation(new CollectLiterals(
								tmp1.createNot(cond), bc1));
						tmp1 = null;
						BuildClause bc2 = new BuildClause(
								ProofConstants.AUX_ITE_NEG_2);
						bc2.auxAxiom(m_AuxLit, at, null, null);
						bc2.addLiteral(m_AuxLit);
						pushOperation(bc2);
						pushOperation(new CollectLiterals(
								new Utils(bc2.getTracker()).createNot(elseTerm),
								bc2));
						pushOperation(new CollectLiterals(cond, bc2));
						if (Config.REDUNDANT_ITE_CLAUSES) {
							BuildClause bc3 = new BuildClause(
									ProofConstants.AUX_ITE_NEG_RED);
							Utils tmp3 = new Utils(bc3.getTracker());
							bc3.auxAxiom(m_AuxLit, at, null, null);
							bc3.addLiteral(m_AuxLit);
							pushOperation(bc3);
							pushOperation(new CollectLiterals(
									tmp3.createNot(elseTerm), bc3));
							pushOperation(new CollectLiterals(
									tmp3.createNot(thenTerm), bc3));
						}
					}
				} else if (at.getFunction().getName().equals("=")) {
					assert at.getParameters().length == 2;
					Term lhs = at.getParameters()[0];
					Term rhs = at.getParameters()[1];
					assert (lhs.getSort() == t.getBooleanSort());
					assert (rhs.getSort() == t.getBooleanSort());
//					Term negLhs = Utils.createNot(lhs);
//					Term negRhs = Utils.createNot(rhs);
					if (m_Positive) {
						BuildClause bc1 = new BuildClause(
								ProofConstants.AUX_EQ_POS_1);
						Utils tmp1 = new Utils(bc1.getTracker());
						bc1.auxAxiom(m_AuxLit, at, null, null);
						bc1.addLiteral(m_AuxLit.negate());
						pushOperation(bc1);
						pushOperation(
								new CollectLiterals(tmp1.createNot(rhs), bc1));
						pushOperation(new CollectLiterals(lhs, bc1));
						tmp1 = null;
						BuildClause bc2 = new BuildClause(
								ProofConstants.AUX_EQ_POS_2);
						Utils tmp2 = new Utils(bc2.getTracker());
						bc2.auxAxiom(m_AuxLit, at, null, null);
						bc2.addLiteral(m_AuxLit.negate());
						pushOperation(bc2);
						pushOperation(new CollectLiterals(rhs, bc2));
						pushOperation(
								new CollectLiterals(tmp2.createNot(lhs), bc2));
					} else {
						BuildClause bc1 = new BuildClause(
								ProofConstants.AUX_EQ_NEG_1);
						bc1.auxAxiom(m_AuxLit, at, null, null);
						bc1.addLiteral(m_AuxLit);
						pushOperation(bc1);
						pushOperation(new CollectLiterals(rhs, bc1));
						pushOperation(new CollectLiterals(lhs, bc1));
						BuildClause bc2 = new BuildClause(
								ProofConstants.AUX_EQ_NEG_2);
						Utils tmp = new Utils(bc2.getTracker());
						bc2.auxAxiom(m_AuxLit, at, null, null);
						bc2.addLiteral(m_AuxLit);
						pushOperation(bc2);
						pushOperation(
								new CollectLiterals(tmp.createNot(rhs), bc2));
						pushOperation(
								new CollectLiterals(tmp.createNot(lhs), bc2));
					}
				} else {
					throw new InternalError("AuxAxiom not implemented: " +
							SMTAffineTerm.cleanup(m_Term));
				}
			} else {
				// TODO: Correctly implement this once we support quantifiers.
//				QuantifiedFormula qf = (QuantifiedFormula) m_Term;
//				assert (qf.getQuantifier() == QuantifiedFormula.EXISTS);
//				if (!m_Positive)
//					;// TODO Nothing to do?
//				else {
//					TermVariable[] vars = qf.getVariables();
//					Term[] skolems = new Term[vars.length];
//					for (int i = 0; i < skolems.length; ++i)
//						skolems[i] = t.term(t.skolemize(vars[i]));
//					Term skolem;
//					m_Unlet.beginScope();
//					try {
//						m_Unlet.addSubstitutions(
//							new ArrayMap<TermVariable, Term>(vars, skolems));
//						Term negSkolem = m_Unlet.unlet(qf.getSubformula());
//						skolem = Utils.createNot(negSkolem);
//					} finally {
//						m_Unlet.endScope();
//					}
//					skolem = m_Compiler.transform(skolem);
//					// TODO Annotation processing
//					BuildClause bc = new BuildClause(true);
//					// FIXME Is this a tautology?  Do we need a different proof?
//					bc.addLiteral(m_AuxLit);
//					pushOperation(bc);
//					pushOperation(new CollectLiterals(skolem, bc));
//				}
			}
		}
		
	}
	
	private class CreateNegClauseAuxAxioms implements Operation {

		Set<Term> m_Disjuncts = new LinkedHashSet<Term>();
		private Literal m_AuxLit;
		
		public CreateNegClauseAuxAxioms(Literal auxLit) {
			m_AuxLit = auxLit;
		}
		
		public void init(Term term) {
			// Cannot be done in ctor since CollectDisjuncts has to be befor this.
			pushOperation(new CollectDisjuncts(term));
		}
		
		@Override
		public void perform() {
			for (Term disj : m_Disjuncts) {
				BuildClause bc = new BuildClause(ProofConstants.AUX_OR_NEG);
				bc.auxAxiom(m_AuxLit, disj, null, null);
				bc.addLiteral(m_AuxLit);
				pushOperation(bc);
				pushOperation(new CollectLiterals(
						new Utils(bc.getTracker()).createNot(disj), bc));
			}
		}
		
		private class CollectDisjuncts implements Operation {
			
			private Term m_Term;
			
			public CollectDisjuncts(Term term) {
				m_Term = term;
			}
			
			@Override
			public void perform() {
//				Term t = toPositive(m_Term);
//				// We are going to negate m_Term later
//				Literal old = getLiteralForPolarity(t, t != m_Term);
//				if (old == null || old == m_AuxLit.negate()) {
					if (m_Term instanceof ApplicationTerm) {
						ApplicationTerm at = (ApplicationTerm) m_Term;
						if (at.getFunction() == at.getTheory().m_Or) {
							for (Term disj : at.getParameters())
								pushOperation(new CollectDisjuncts(disj));
							return;
						}
					}
//				}
				m_Disjuncts.add(m_Term);
			}
			
		}
		
	}
	
	/**
	 * Collect literals to build a clause.
	 * @author Juergen Christ
	 */
	private class CollectLiterals implements Operation {
		private Term m_Term;
		private LiteralCollector m_Collector;
		public CollectLiterals(Term term, LiteralCollector collector) {
			assert term.getSort() == m_Theory.getBooleanSort();
			m_Term = term;
			m_Collector = collector;
		}
		public void perform() {
			Theory t = m_Term.getTheory();
			if (m_Term == t.FALSE)
				return;
			if (m_Term == t.TRUE) {
				m_Collector.setTrue();
				return;
			}
			Term idx = toPositive(m_Term);
			boolean positive = m_Term == idx;
			// TODO What about this optimization? It increases the number of
			// conflicts on some examples, but should be better.
//			Literal knownlit = getLiteralForPolarity(idx, positive);
//			if (knownlit != null) {
//				m_Collector.addLiteral(knownlit);
//				return;
//			}
			if (idx instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) idx;
				if (positive && at.getFunction() == t.m_Or) {
					if (m_Term.tmpCtr > Config.OCC_INLINE_THRESHOLD) {
//						m_Logger.trace("Don't inline the clause" + SMTAffineTerm.cleanup(idx));
						Literal lit = getLiteral(idx);
						m_Collector.getTracker().quoted(idx, lit.getAtom());
						m_Collector.addLiteral(lit);
					} else
						for (Term p : at.getParameters())
							pushOperation(new CollectLiterals(p, m_Collector));
				} else if (!at.getFunction().isIntern() &&
						at.getFunction().getReturnSort() == t.getBooleanSort()) {
					Literal lit = createBooleanLit(at);
					m_Collector.getTracker().intern(idx, lit);
					m_Collector.addLiteral(positive ? lit : lit.negate());
//				} else if (at.getFunction().getName().equals("ite")) {
//					Term cond = at.getParameters()[0];
//					Term tc = at.getParameters()[1];
//					Term ec = at.getParameters()[2];
//					assert tc.getSort() == t.getBooleanSort();
//					// (ite cond tc ec) ===
//					// (or (and cond tc) (and (not cond) ec))
//					/*
//					 * (= A B) === (or (and A B) (and (not A) (not B)))
//					 */
			    } else if (at.getFunction().getName().equals("=") &&
			    		at.getParameters()[0].getSort() !=
			    			m_Theory.getBooleanSort()) {
					Term lhs = at.getParameters()[0];
					Term rhs = at.getParameters()[1];
					SharedTerm slhs = getSharedTerm(lhs);
					SharedTerm srhs = getSharedTerm(rhs);
					EqualityProxy eq = createEqualityProxy(slhs, srhs);
					// eq == true and positive ==> set to true
					// eq == true and !positive ==> noop
					// eq == false and !positive ==> set to true
					// eq == false and positive ==> noop
					if (eq == EqualityProxy.getTrueProxy()) {
						if (positive)
							m_Collector.setTrue();
						m_Collector.getTracker().eq(lhs, rhs, m_Theory.TRUE);
						return;
					}
					if (eq == EqualityProxy.getFalseProxy()) {
						if (!positive)
							m_Collector.setTrue();
						m_Collector.getTracker().eq(lhs, rhs, m_Theory.FALSE);
						return;
					}
					DPLLAtom eqAtom = eq.getLiteral();
					m_Collector.getTracker().eq(lhs, rhs, eqAtom);
					m_Collector.addLiteral(positive ? eqAtom : eqAtom.negate());
				} else if (at.getFunction().getName().equals("<=")) {
					// (<= SMTAffineTerm 0)
					Literal lit = createLeq0(at);
					m_Collector.getTracker().intern(at, lit);
					m_Collector.addLiteral(positive ? lit : lit.negate());
				} else {
					Literal lit = getLiteral(m_Term);
					m_Collector.getTracker().quoted(m_Term, lit);
					m_Collector.addLiteral(lit);
				}
			} else {
				if (positive) {
					assert (idx instanceof QuantifiedFormula);
					Literal lit = getLiteral(idx);
					// TODO: Proof
					m_Collector.addLiteral(lit);
				} else {
					// TODO Skolemize and recurse
				}
			}
		}
	}
	
	private interface LiteralCollector extends Operation {
		void addLiteral(Literal lit);
		void setTrue();
		IProofTracker getTracker();
	}
	
	private class BuildClause implements LiteralCollector {
		private boolean m_IsTrue = false;
		private int m_LeafKind;
		private LinkedHashSet<Literal> m_Lits = new LinkedHashSet<Literal>();
		private Term m_ProofTerm;
		private IProofTracker m_SubTracker = m_Tracker.getDescendent();
		//@ invariant ProofProductionEnabled ==>
		//          (m_LeafKind != LeafNode.NO_THEORY) == (m_ProofTerm == null);
		public BuildClause(int leafKind) {
			m_LeafKind = leafKind;
			m_ProofTerm = null;
		}
		public void auxAxiom(Literal lit, Term res, Term base, Object auxData) {
			m_ProofTerm = m_SubTracker.auxAxiom(
					m_LeafKind, lit, res, base, auxData);
		}
		public BuildClause(Term proofTerm) {
			this(LeafNode.NO_THEORY);
			m_ProofTerm = proofTerm;
		}
		public void setProofTerm(Term proof) {
			m_ProofTerm = proof;
		}
		public void addLiteral(Literal lit) {
			if (m_Lits.add(lit)) {
				m_IsTrue |= m_Lits.contains(lit.negate());
			}
		}
		public void setTrue() {
			m_IsTrue = true;
		}
		public void perform() {
			if (!m_IsTrue) {
				addClause(m_Lits.toArray(new Literal[m_Lits.size()]),
						null,
						getProofNewSource(m_LeafKind,
								m_SubTracker.clause(m_ProofTerm)));
			}
		}
		public IProofTracker getTracker() {
			return m_SubTracker;
		}
	}
		
	private class AddDivideAxioms implements Operation {

		private Term m_DivTerm;
		private Term m_Divider;
		private Rational m_Divident;
	
		public AddDivideAxioms(Term divTerm, Term divider, Rational divident) {
			m_DivTerm = divTerm;
			m_Divider = divider;
			m_Divident = divident;
		}
		
		@Override
		public void perform() {
			IProofTracker sub = m_Tracker.getDescendent();
			Utils tmp = new Utils(sub);
			SMTAffineTerm arg = SMTAffineTerm.create(m_Divider);
			SMTAffineTerm div = SMTAffineTerm.create(m_DivTerm);
			// (<= (- (* d (div x d)) x) 0)
			SMTAffineTerm difflow = div.mul(m_Divident).add(arg.negate());
			Literal lit1 = createLeq0(
					(ApplicationTerm) tmp.createLeq0(difflow));
			Term prf = sub.auxAxiom(
					ProofConstants.AUX_DIV_LOW, null, difflow, null, null);
			sub.leq0(difflow, lit1);
			addClause(new Literal[] {lit1}, null,
					getProofNewSource(
							ProofConstants.AUX_DIV_LOW, sub.clause(prf)));
			// (not (<= (+ d (- x) (* d (div x d))) 0))
			sub = m_Tracker.getDescendent();
			tmp = new Utils(sub);
			SMTAffineTerm diffhigh = arg.negate().add(div.mul(m_Divident)).add(
					m_Divident);
			prf = sub.auxAxiom(
					ProofConstants.AUX_DIV_HIGH, null, diffhigh, null, null);
			Literal lit2 = createLeq0(
					(ApplicationTerm) tmp.createLeq0(diffhigh));
			sub.leq0(diffhigh, lit2);
			addClause(new Literal[] {lit2.negate()}, null,
					getProofNewSource(
							ProofConstants.AUX_DIV_HIGH, sub.clause(prf)));
		}
		
	}
	
	/**
	 * Helper to add the auxiliary axioms for to_int axioms.  Since the axioms
	 * for (to_int x) equal the axioms added for (div x 1), we reuse
	 * AddDivideAxioms. 
	 * @author Juergen Christ
	 */
	private class AddToIntAxioms implements Operation {
		
		private ApplicationTerm m_ToIntTerm;
		
		public AddToIntAxioms(ApplicationTerm toIntTerm) {
			m_ToIntTerm = toIntTerm;
		}
		@Override
		public void perform() {
			IProofTracker sub = m_Tracker.getDescendent();
			Utils tmp = new Utils(sub);
			SMTAffineTerm realTerm = SMTAffineTerm.create(
					m_ToIntTerm.getParameters()[0]);
			SMTAffineTerm toInt = SMTAffineTerm.create(m_ToIntTerm).toReal(
					realTerm.getSort());
			// (<= (- (to_real (to_int x)) x) 0)
			SMTAffineTerm difflow = toInt.add(realTerm.negate());
			Literal lit1 = createLeq0(
					(ApplicationTerm) tmp.createLeq0(difflow));
			Term prf = sub.auxAxiom(
					ProofConstants.AUX_TO_INT_LOW, null, difflow, null, null);
			sub.leq0(difflow, lit1);
			addClause(new Literal[] {lit1}, null,
					getProofNewSource(
							ProofConstants.AUX_TO_INT_LOW, sub.clause(prf)));
			// (not (<= (+ d (- x) (* d (div x d))) 0))
			sub = m_Tracker.getDescendent();
			tmp = new Utils(sub);
			SMTAffineTerm diffhigh =
					toInt.add(Rational.ONE).add(realTerm.negate());
			prf = sub.auxAxiom(
					ProofConstants.AUX_TO_INT_HIGH, null, diffhigh, null, null);
			Literal lit2 = createLeq0(
					(ApplicationTerm) tmp.createLeq0(diffhigh));
			sub.leq0(diffhigh, lit2);
			addClause(new Literal[] {lit2.negate()}, null,
					getProofNewSource(
							ProofConstants.AUX_TO_INT_HIGH, sub.clause(prf)));
		}
	}
	/**
	 * Add the axioms for the law of excluded middle.  This must happen if a
	 * Boolean function is used as a parameter to a non-Boolean function.
	 * @author Juergen Christ
	 */
	private class AddExcludedMiddleAxiom implements Operation {
		
		private SharedTerm m_SharedTerm;
		
		public AddExcludedMiddleAxiom(SharedTerm shared) {
			m_SharedTerm = shared;
		}
		
		@Override
		public void perform() {
			EqualityProxy thenProxy = createEqualityProxy(
					m_SharedTerm, m_SharedTrue);
			EqualityProxy elseProxy = createEqualityProxy(
					m_SharedTerm, m_SharedFalse);
			// These asserts should hold since we do not add excluded middle
			// axioms for true or false, and the equality proxies are
			// non-numeric
			assert thenProxy != EqualityProxy.getTrueProxy();
			assert thenProxy != EqualityProxy.getFalseProxy();
			assert elseProxy != EqualityProxy.getTrueProxy();
			assert elseProxy != EqualityProxy.getFalseProxy();
			// m_Term => thenForm is (not m_Term) \/ thenForm
			BuildClause bc1 = new BuildClause(
					ProofConstants.AUX_EXCLUDED_MIDDLE_1);
			Literal lit1 = thenProxy.getLiteral();
			bc1.auxAxiom(lit1, m_SharedTerm.getTerm(), null, null);
			bc1.addLiteral(lit1);
			pushOperation(bc1);
			pushOperation(new CollectLiterals(
					new Utils(bc1.getTracker()).createNot(
							m_SharedTerm.getTerm()), bc1));
			// (not m_Term) => elseForm is m_Term \/ elseForm
			BuildClause bc2 = new BuildClause(
					ProofConstants.AUX_EXCLUDED_MIDDLE_2);
			Literal lit2 = elseProxy.getLiteral();
			bc2.auxAxiom(lit2, m_SharedTerm.getTerm(), null, null);
			bc2.addLiteral(lit2);
			pushOperation(bc2);
			pushOperation(new CollectLiterals(m_SharedTerm.getTerm(), bc2));
		}
		
	}
	
	public static class ConditionChain {
		ConditionChain m_Prev;
		Term m_Cond;
		boolean m_Negated;
		public ConditionChain(ConditionChain prev, Term cond) {
			this(prev, cond, false);
		}
		public ConditionChain(ConditionChain prev, Term cond, boolean negated) {
			m_Prev = prev;
			m_Cond = cond;
			m_Negated = negated;
		}
		public Term getTerm() {
			return m_Negated ? 
					m_Cond.getTheory().term(m_Cond.getTheory().m_Not, m_Cond) :
						m_Cond;
		}
		public ConditionChain getPrevious() {
			return m_Prev;
		}
	}
	
	private class AddTermITEAxiom implements Operation {

		private class CollectConditions implements Operation {
			private ConditionChain m_Conds;
			private Term m_Term;
			private SharedTerm m_Ite;
			public CollectConditions(
				ConditionChain conds, Term term, SharedTerm ite) {
				m_Conds = conds;
				m_Term = term;
				m_Ite = ite;
			}
			public void perform() {
				if (m_Term instanceof ApplicationTerm) {
					ApplicationTerm at = (ApplicationTerm) m_Term;
					if (at.getFunction().getName().equals("ite") &&
							at.tmpCtr <=
								Config.OCC_INLINE_TERMITE_THRESHOLD) {
						Term c = at.getParameters()[0];
						Term t = at.getParameters()[1];
						Term e = at.getParameters()[2];
						m_Collects.push(new CollectConditions(
								new ConditionChain(m_Conds, c), t, m_Ite));
						m_Collects.push(new CollectConditions(
								new ConditionChain(m_Conds, c, true),
								e, m_Ite));
						return;
					}
				}// Not a nested ite term or a nested shared ite term
				BuildClause bc = new BuildClause(ProofConstants.AUX_TERM_ITE);
				bc.auxAxiom(null, m_Term, m_Ite.getTerm(), m_Conds);
				pushOperation(bc);
				SharedTerm st = getSharedTerm(m_Term);
				EqualityProxy eqproxy = createEqualityProxy(m_Ite, st);
				// These asserts should be safe
				assert eqproxy != EqualityProxy.getFalseProxy();
				assert eqproxy != EqualityProxy.getTrueProxy();
				DPLLAtom eq = eqproxy.getLiteral();
				bc.addLiteral(eq);
				bc.getTracker().eq(m_Ite.getTerm(), m_Term, eq);
				ConditionChain walk = m_Conds;
				Utils tmp = new Utils(bc.getTracker());
				while (walk != null) {
					pushOperation(
							new CollectLiterals(walk.m_Negated ? walk.m_Cond :
								tmp.createNot(walk.m_Cond),
									bc));
					walk = walk.m_Prev;
				}
			}
		}
		
		private SharedTerm m_TermITE;
		private ArrayDeque<Operation> m_Collects;
		
		public AddTermITEAxiom(SharedTerm termITE) {
			m_TermITE = termITE;
		}
		
		public void perform() {
			m_Collects = new ArrayDeque<Clausifier.Operation>();
			ApplicationTerm ite = (ApplicationTerm) m_TermITE.getTerm();
			Term cond = ite.getParameters()[0];
			m_Collects.push(
					new CollectConditions(new ConditionChain(null, cond),
							ite.getParameters()[1], m_TermITE));
			m_Collects.push(
					new CollectConditions(new ConditionChain(null,
							cond, true),
							ite.getParameters()[2], m_TermITE));
			while(!m_Collects.isEmpty())
				m_Collects.pop().perform();
		}
	}
	
	
	// Term Creation
	public MutableAffinTerm createMutableAffinTerm(SharedTerm term) {
		SMTAffineTerm at = SMTAffineTerm.create(term.getTerm());
		return createMutableAffinTerm(at);
	}
	
	MutableAffinTerm createMutableAffinTerm(SMTAffineTerm at) {
		MutableAffinTerm res = new MutableAffinTerm();
		res.add(at.getConstant());
		for (Map.Entry<Term,Rational> summand : at.getSummands().entrySet()) {
			SharedTerm shared = getSharedTerm(summand.getKey());
			Rational coeff = summand.getValue();
			shared.shareWithLinAr();
//			if (shared.m_linvar != null) // TODO check whether this is dead code
				res.add(shared.m_factor.mul(coeff), shared);
			res.add(shared.m_offset.mul(coeff));
		}
		return res;
	}
	
	public SharedTerm getSharedTerm(Term t) {
		return getSharedTerm(t, false);
	}
	
	/**
	 * Get or create a shared term for a term.  This version does not force
	 * creation of a CCTerm for non-internal functions with arguments if
	 * <code>inCCTermBuilder</code> is <code>true</code>.
	 * 
	 * As a side effect, this function adds divide, to_int, or ite axioms for
	 * the corresponding terms.  Furthermore, For Boolean terms other than true
	 * or false the law of excluded middle is instantiated.
	 * @param t               The term to create a shared term for.
	 * @param inCCTermBuilder Are we in {@link CCTermBuilder}?
	 * @return Shared term.
	 */
	public SharedTerm getSharedTerm(Term t, boolean inCCTermBuilder) {
		if (t instanceof SMTAffineTerm)
			t = ((SMTAffineTerm) t).normalize();
		SharedTerm res = m_SharedTerms.get(t);
		if (res == null) {
			// if we reach here, t is neither true nor false
			res = new SharedTerm(this, t);
			m_SharedTerms.put(t, res);
			if (t instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) t;
				// Special cases
				if (t.getSort() == t.getTheory().getBooleanSort())
					pushOperation(new AddExcludedMiddleAxiom(res));
				else {
					FunctionSymbol fs = at.getFunction();
					if (fs.isInterpreted()) {
						if (fs.getName().equals("div"))
							pushOperation(
									new AddDivideAxioms(t,
											at.getParameters()[0],
											SMTAffineTerm.create(
													at.getParameters()[1]).
													getConstant()));
						else if (fs.getName().equals("to_int"))
							pushOperation(new AddToIntAxioms(at));
						else if (fs.getName().equals("ite") &&
								fs.getReturnSort() != m_Theory.getBooleanSort())
							pushOperation(new AddTermITEAxiom(res));
					} else if (!inCCTermBuilder &&
							at.getParameters().length > 0) {
						CCTermBuilder cc = new CCTermBuilder();
						res.m_ccterm = cc.convert(t);
					}
				}
			}
			if (t instanceof SMTAffineTerm)
				res.shareWithLinAr();
		}
		return res;
	}
	
	/// Internalization stuff
	private FormulaUnLet m_Unlet = new FormulaUnLet();
	private TermCompiler m_Compiler = new TermCompiler();
	private OccurrenceCounter m_OccCounter = new OccurrenceCounter();
	private Deque<Operation> m_TodoStack =
		new ArrayDeque<Clausifier.Operation>();
	private ProofNode m_Proof;
	
	private Theory m_Theory;
	private DPLLEngine m_Engine;
	private CClosure m_CClosure;
	private LinArSolve m_LASolver;
//	private QuantifierTheory m_Quantifier;
	
	private boolean m_InstantiationMode;
	/**
	 * Mapping from Boolean terms to information about clauses produced for
	 * these terms.
	 */
	private Map<Term, ClausifierInfo> m_ClauseData =
		new HashMap<Term, ClausifierInfo>();
	/**
	 * Mapping from Boolean base terms to literals.  A term is considered a base
	 * term when it corresponds to an atom or its negation.
	 */
	private Map<Term, Literal> m_LiteralData = new HashMap<Term, Literal>();
	/**
	 * We cache the SharedTerms for true and false here to be able to quickly
	 * create excluded middle axioms.
	 */
	SharedTerm m_SharedTrue, m_SharedFalse;
	
	/// Statistics stuff
	private int numAtoms = 0;
	
	/// Assertion stack stuff
	/**
	 * The undo trail used as a stack.
	 */
	private TrailObject m_UndoTrail = new TrailObject() {
		
		@Override
		public void undo() {
			// Nothing to do for this sentinel entry
		}
	};
	/**
	 * Keep all shared terms that need to be unshared from congruence closure
	 * when the top level is popped off the assertion stack.
	 */
	ScopedArrayList<SharedTerm> m_UnshareCC = new ScopedArrayList<SharedTerm>();
	/**
	 * Keep all shared terms that need to be unshared from linear arithmetic
	 * when the top level is popped off the assertion stack.
	 */
	ScopedArrayList<SharedTerm> m_UnshareLA = new ScopedArrayList<SharedTerm>();
	/**
	 * Mapping from terms to their corresponding shared terms. 
	 */
	ScopedHashMap<Term, SharedTerm> m_SharedTerms =
		new ScopedHashMap<Term, SharedTerm>();
	/**
	 * Map of differences to equality proxies.
	 */
	ScopedHashMap<SMTAffineTerm, EqualityProxy> m_Equalities =
		new ScopedHashMap<SMTAffineTerm, EqualityProxy>();
	/**
	 * Current assertion stack level.
	 */
	private int m_StackLevel = 0;
	/**
	 * The number of pushes that failed since the solver already detected
	 * unsatisfiability.
	 */
	private int m_NumFailedPushes = 0;
	/**
	 * Did we emit a warning on a failed push?
	 */
	private boolean m_WarnedFailedPush = false;
	
	private Logger m_Logger;
	/**
	 * A tracker for proof production.
	 */
	private IProofTracker m_Tracker;
	
	public Clausifier(DPLLEngine engine, int proofLevel) {
		m_Theory = engine.getSMTTheory();
		m_Engine = engine;
		m_Logger = engine.getLogger();
		m_Tracker = proofLevel == 2 ? 
				new ProofTracker() : new NoopProofTracker();
		m_Compiler.setProofTracker(m_Tracker);
	}
	
	public void setAssignmentProduction(boolean on) {
		m_Compiler.setAssignmentProduction(on);
	}
	
	void pushOperation(Operation op) {
		m_TodoStack.push(op);
	}
	
	/**
	 * Transform a term to a positive normal term.  A term is a positive normal
	 * term if it
	 * <ul>
	 * <li>is an {@link ApplicationTerm} that does not correspond to a negation
	 * </li>
	 * <li>is a {@link QuantifiedFormula} that is universally quantified</li>
	 * </ul> 
	 * @param t The term to compute the positive for.
	 * @return The positive of this term.
	 */
	private static Term toPositive(Term t) {
		assert !(t instanceof AnnotatedTerm);
		if (t instanceof ApplicationTerm) {
			ApplicationTerm at = (ApplicationTerm) t;
			return (at.getFunction() == at.getTheory().m_Not) ?
					at.getParameters()[0] : at;
		}
		// FIXME: Think about how to get Utils in here...
//		else if (t instanceof QuantifiedFormula) {
//			QuantifiedFormula qf = (QuantifiedFormula) t;
//			if (qf.getQuantifier() == QuantifiedFormula.EXISTS) {
//				// (exists (x) (phi x)) is (not (forall (x) (not (phi x))))
//				return t.getTheory().forall(qf.getVariables(),
//						Utils.createNot(qf.getSubformula()));
//			}
//			return qf;
//		}
		throw new InternalError("Unclear how to compute positive for " + t);
	}
	
	NamedAtom createAnonAtom(Term smtFormula) {
		NamedAtom atom = new NamedAtom(smtFormula, m_StackLevel);
		m_Engine.addAtom(atom);
		m_Tracker.quoted(smtFormula, atom);
		numAtoms++;
		return atom;
	}

	BooleanVarAtom createBooleanVar(Term smtFormula) {
		BooleanVarAtom atom = new BooleanVarAtom(smtFormula, m_StackLevel);
		// TODO Do we want this cache?
		// It prevents dynamic model creation, but speeds it up.
//		if (m_BooleanVars != null)
//			m_BooleanVars.add(atom);
		m_UndoTrail = new RemoveAtom(m_UndoTrail, smtFormula);
		m_Engine.addAtom(atom);
		numAtoms++;
		return atom;
	}

	QuantifiedAtom createQuantifiedAtom(Term smtFormula) {
		String name = "quantproxy!" + numAtoms;
		QuantifiedAtom atom = new QuantifiedAtom(name, smtFormula, m_StackLevel);
		m_LiteralData.put(smtFormula, atom);
		m_UndoTrail = new RemoveAtom(m_UndoTrail, smtFormula);
		m_Engine.addAtom(atom);
		++numAtoms;
		return atom;
	}
	
	public EqualityProxy createEqualityProxy(SharedTerm lhs, SharedTerm rhs) {
		SMTAffineTerm diff = SMTAffineTerm.create(lhs.getTerm()).add(
				SMTAffineTerm.create(rhs.getTerm()).negate());
		if (diff.isConstant()) {
			if (diff.getConstant().equals(Rational.ZERO)) {
				m_Tracker.eq(lhs.getTerm(), rhs.getTerm(), m_Theory.TRUE);
				return EqualityProxy.getTrueProxy();
			} else {
				m_Tracker.eq(lhs.getTerm(), rhs.getTerm(), m_Theory.FALSE);
				return EqualityProxy.getFalseProxy();
			}
		}
		diff = diff.div(diff.getGcd());
		// check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
		if (diff.isIntegral() && !diff.getConstant().isIntegral()) {
			m_Tracker.eq(lhs.getTerm(), rhs.getTerm(), m_Theory.FALSE);
			return EqualityProxy.getFalseProxy();
		}
		// we cannot really normalize the sign of the term.  Try both signs.
		EqualityProxy eqForm = m_Equalities.get(diff);
		if (eqForm != null)
			return eqForm;
		eqForm = m_Equalities.get(diff.negate());
		if (eqForm != null)
			return eqForm;
		eqForm = new EqualityProxy(this, lhs, rhs);
		m_Equalities.put(diff, eqForm);
		return eqForm;
	}
	
	Literal getLiteralForPolarity(Term t, boolean positive) {
		assert t == toPositive(t);
		ClausifierInfo ci = m_ClauseData.get(t);
		if (ci != null && ci.getLiteral() != null) {
			if (positive) {
				if (!ci.testFlags(ClausifierInfo.POS_AUX_AXIOMS_ADDED))
					pushOperation(
							new AddAuxAxioms(t, ci.getLiteral(), positive));
				return ci.getLiteral();
			} else {
				if (!ci.testFlags(ClausifierInfo.NEG_AUX_AXIOMS_ADDED))
					pushOperation(
							new AddAuxAxioms(t, ci.getLiteral(), positive));
				return ci.getLiteral().negate();
			}
		}
		return null; 
	}
	
	Literal getLiteral(Term t) {
		Term idx = toPositive(t);
		boolean pos = t == idx;
		ClausifierInfo ci = m_ClauseData.get(idx);
		if (ci == null) {
			ci = new ClausifierInfo();
			m_ClauseData.put(idx, ci);
			m_UndoTrail = new RemoveClausifierInfo(m_UndoTrail, idx);
		}
		if (ci.getLiteral() == null) {
			Literal lit = createAnonAtom(idx);
			ci.setLiteral(lit);
			m_UndoTrail = new RemoveLiteral(m_UndoTrail, ci);
			pushOperation(new AddAuxAxioms(idx, lit, pos));
			return pos ? lit : lit.negate();
		}
		if (pos) {
			if (!ci.testFlags(ClausifierInfo.POS_AUX_AXIOMS_ADDED))
				pushOperation(new AddAuxAxioms(idx, ci.getLiteral(), true));
			return ci.getLiteral();
		}
		if (!ci.testFlags(ClausifierInfo.NEG_AUX_AXIOMS_ADDED))
			pushOperation(new AddAuxAxioms(idx, ci.getLiteral(), false));
		return ci.getLiteral().negate();
	}
	
	Literal getLiteralTseitin(Term t) {
		Term idx = toPositive(t);
		boolean pos = t == idx;
		ClausifierInfo ci = m_ClauseData.get(idx);
		if (ci == null) {
			ci = new ClausifierInfo();
			m_ClauseData.put(idx, ci);
			m_UndoTrail = new RemoveClausifierInfo(m_UndoTrail, idx);
		}
		if (ci.getLiteral() == null) {
			Literal lit = createAnonAtom(idx);
			ci.setLiteral(lit);
			m_UndoTrail = new RemoveLiteral(m_UndoTrail, ci);
			pushOperation(new AddAuxAxioms(idx, lit, true));
			pushOperation(new AddAuxAxioms(idx, lit, false));
			return pos ? lit : lit.negate();
		}
		if (!ci.testFlags(ClausifierInfo.POS_AUX_AXIOMS_ADDED))
			pushOperation(new AddAuxAxioms(idx, ci.getLiteral(), true));
		if (!ci.testFlags(ClausifierInfo.NEG_AUX_AXIOMS_ADDED))
			pushOperation(new AddAuxAxioms(idx, ci.getLiteral(), false));
		return pos ? ci.getLiteral() : ci.getLiteral().negate();
	}
	
	ClausifierInfo getInfo(Term idx) {
		assert(idx == toPositive(idx));
		ClausifierInfo res = m_ClauseData.get(idx);
		if (res == null) {
			res = new ClausifierInfo();
			m_ClauseData.put(idx, res);
			m_UndoTrail = new RemoveClausifierInfo(m_UndoTrail, idx);
		}
		return res;
	}
	
	void addClause(Literal[] lits, ClauseDeletionHook hook, ProofNode proof) {
		if (m_InstantiationMode) {
			// TODO Add instantiation clauses to DPLL
		} else {
			m_Engine.addFormulaClause(lits, proof, hook);
		}
	}
	
	void addToUndoTrail(TrailObject obj) {
		obj.setPrevious(m_UndoTrail);
		m_UndoTrail = obj;
	}
	
	private void pushUndoTrail() {
		m_UndoTrail = new ScopeMarker(m_UndoTrail);
	}
	
	private void popUndoTrail() {
		while (!m_UndoTrail.isScopeMarker()) {
			m_UndoTrail.undo();
			m_UndoTrail = m_UndoTrail.getPrevious();
		}
		// Skip the scope marker
		m_UndoTrail = m_UndoTrail.getPrevious();
	}
	
	SharedTerm toReal(SharedTerm t) {
		SMTAffineTerm tst = SMTAffineTerm.create(t.getTerm());
		return getSharedTerm(tst.toReal(m_Theory.getSort("Real")));
	}
	
	void addUnshareCC(SharedTerm shared) {
		m_UnshareCC.add(shared);
	}
	
	void addUnshareLA(SharedTerm shared) {
		m_UnshareLA.add(shared);
	}
	
	private void setupCClosure() {
		if (m_CClosure == null) {
			m_CClosure = new CClosure(m_Engine, this);
			m_Engine.addTheory(m_CClosure);
			/* If we do not setup the cclosure at the root level, we remove it
			 * with the corresponding pop since the axiom true != false will be
			 * removed from the assertion stack as well.
			 */
			if (m_StackLevel != 0)
				m_UndoTrail = new RemoveTheory(m_UndoTrail);
			m_SharedTrue = new SharedTerm(this, m_Theory.TRUE);
			m_SharedTrue.m_ccterm = m_CClosure.createAnonTerm(m_SharedTrue);
			m_SharedTerms.put(m_Theory.TRUE, m_SharedTrue);
			m_SharedFalse =	new SharedTerm(this, m_Theory.FALSE);
			m_SharedFalse.m_ccterm = m_CClosure.createAnonTerm(m_SharedFalse);
			m_SharedTerms.put(m_Theory.FALSE, m_SharedFalse);
			Literal[] lits = new Literal[] {
				m_CClosure.createCCEquality(
						m_StackLevel, m_SharedTrue.m_ccterm,
						m_SharedFalse.m_ccterm).negate()};
			m_Engine.addFormulaClause(lits,
					getProofNewSource(ProofConstants.AUX_TRUE_NOT_FALSE, 
							m_Tracker.auxAxiom(
									ProofConstants.AUX_TRUE_NOT_FALSE,
									null, m_Theory.TRUE, null, null)));
		}
	}
	
	private void setupLinArithmetic() {
		if (m_LASolver == null) {
			m_LASolver = new LinArSolve(m_Engine);
			m_Engine.addTheory(m_LASolver);
		}
	}
	
//	private void setupQuantifiers() {
		// TODO Implement 
//		setupCClosure();
//		try {
//			Class<?> pcclass = getClass().getClassLoader().loadClass(
//					System.getProperty(
//							Config.PATTERNCOMPILER,
//							Config.DEFAULT_PATTERNCOMPILER));
//			patternCompiler = (IPatternCompiler)pcclass.newInstance();
//		} catch (Exception e) {
//			logger.fatal("Could not load Pattern Compiler",e);
//			throw new RuntimeException("Could not load Pattern Compiler",e);
//		}
//		quantTheory = new QuantifierTheory(cclosure);
//		dpllEngine.addTheory(quantTheory);
//	}
	
	public void setLogic(Logics logic) {
		switch (logic) {
		case CORE:
			break;
		case QF_UFLRA:
		case QF_UFLIRA:
		case QF_UFLIA:
		case QF_UFIDL:
			setupCClosure();
			setupLinArithmetic();
			break;
		case QF_IDL:
		case QF_LIA:
		case QF_LRA:
		case QF_RDL:
			setupLinArithmetic();
			break;
		case QF_UF:
			setupCClosure();
			break;
		default:
			throw new UnsupportedOperationException(
					"Logic " + logic.toString() + " unsupported");
		}
	}
	
	public Iterable<BooleanVarAtom> getBooleanVars() {
		return new Iterable<BooleanVarAtom>() {
			
			@Override
			public Iterator<BooleanVarAtom> iterator() {
				return new BooleanVarIterator(m_LiteralData.values().iterator());
			}
		};
	}
	
	private static final class BooleanVarIterator 
	implements Iterator<BooleanVarAtom> {
		private Iterator<Literal> m_It;
		private BooleanVarAtom m_Next;
		public BooleanVarIterator(Iterator<Literal> it) {
			m_It = it;
			computeNext();
		}
		private final void computeNext() {
			while (m_It.hasNext()) {
				Literal lit = m_It.next();
				if (lit instanceof BooleanVarAtom) {
					m_Next = (BooleanVarAtom) lit;
					return;
				}
			}
			m_Next = null;
		}
		@Override
		public boolean hasNext() {
			return m_Next != null;
		}
		@Override
		public BooleanVarAtom next() {
			BooleanVarAtom res = m_Next;
			if (res == null)
				throw new NoSuchElementException();
			computeNext();
			return res;
		}
		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}
	
	private final void run() {
		while (!m_TodoStack.isEmpty()) {
			Operation op = m_TodoStack.pop();
			op.perform();
		}
	}
	
	public DPLLEngine getEngine() {
		return m_Engine;
	}
	
	public CClosure getCClosure() {
		return m_CClosure;
	}
	
	public LinArSolve getLASolver() {
		return m_LASolver;
	}
	
	public Logger getLogger() {
		return m_Logger;
	}
	
	public int getStackLevel() {
		return m_StackLevel;
	}
	
	public void addFormula(Term f) {
		if (m_Engine.inconsistent()) {
			m_Logger.warn("Already inconsistent.");
			return;
		}
		if (m_Engine.isProofGenerationEnabled()) {
			setSourceAnnotation(LeafNode.NO_THEORY,
					new SourceAnnotation("", null));
			if (f instanceof AnnotatedTerm) {
				AnnotatedTerm at = (AnnotatedTerm)f;
				Annotation[] annots = at.getAnnotations();
				for (Annotation a : annots) {
					if (a.getKey().equals(":named")) {
						String name = ((String) a.getValue()).intern();
						setSourceAnnotation(LeafNode.NO_THEORY,
								new SourceAnnotation(name, null));
						break;
					}
				}
			}
		}
		Term tmp = m_Unlet.unlet(f);
//		f = null;
//		System.err.println(tmp.toStringDirect());
		Term tmp2 = m_Compiler.transform(tmp);
		tmp = null;
//		System.err.println("Transformed");
//		System.err.println(SMTAffineTerm.cleanup(tmp2).toStringDirect());
		Term proof = m_Tracker.getRewriteProof(f, tmp2);
		m_Tracker.reset();
		
		m_OccCounter.count(tmp2);
		Map<Term, Set<String>> names = m_Compiler.getNames();
		if (names != null) {
			for (Map.Entry<Term, Set<String>> me : names.entrySet())
				trackAssignment(me.getKey(), me.getValue());
		}
//		System.err.println("Started convertion");
		pushOperation(new AddAsAxiom(tmp2, proof));
		m_InstantiationMode = false;
		run();
//		System.err.println("Ended convertion");
		m_OccCounter.reset(tmp2);
		tmp2 = null;
		
//		logger.info("Added " + numClauses + " clauses, " + numAtoms
//				+ " auxiliary atoms.");
		if (m_Engine.isProofGenerationEnabled())
			setSourceAnnotation(LeafNode.NO_THEORY, null);
	}
	
	// TODO need an instantiation mode here to add clauses to DPLL as deletable instantiations
//	public void addInstantiation(Term f, Map<TermVariable, Term> inst,
//			Literal quantproxy) {
//		if (m_Engine.isProofGenerationEnabled()) {
//			// TODO
//		}
//		m_Unlet.beginScope();
//		m_Unlet.addSubstitutions(inst);
//		Term tmp = m_Unlet.unlet(f);
//		m_Unlet.endScope();
//		Term tmp2 = m_Compiler.transform(tmp);
//		
//		/*
//		 * This is an ugly hack.  Since operations might introduce proxy
//		 * literals with definitions that might be deleted once an instantiation
//		 * is deleted, we cannot permanently store the proxy literals and the
//		 * knowledge about their aux axioms.
//		 */
//		pushUndoTrail();
//		m_InstantiationMode = true;
//		if (quantproxy == null) {
//			// toplevel match
//			pushOperation(new AddAsAxiom(tmp2));
//		} else {
//			BuildClause bc = new BuildClause(LeafNode.QUANT_INST);
//			bc.addLiteral(quantproxy.negate());
//			pushOperation(new CollectLiterals(tmp2, bc));
//		}
//		run();
//		popUndoTrail();
//		
//		if (m_Engine.isProofGenerationEnabled()) {
//			// TODO
//		}
//	}
	
	public void push() {
		if (m_Engine.inconsistent()) {
			if (!m_WarnedFailedPush) {
				m_Logger.warn("Already inconsistent.");
				m_WarnedFailedPush = true;
			}
			++m_NumFailedPushes;
		} else {
			m_Engine.push();
			++m_StackLevel;
			m_Equalities.beginScope();
//			m_arraySorts.beginScope();
//			m_RemoveLit.beginScope();
			m_UnshareCC.beginScope();
			m_UnshareLA.beginScope();
//			if (m_BooleanVars != null)
//				m_BooleanVars.beginScope();
			m_SharedTerms.beginScope();
			pushUndoTrail();
		}
	}
	public void pop(int numpops) {
		if (numpops <= m_NumFailedPushes) {
			m_NumFailedPushes -= numpops;
			return;
		}
		m_WarnedFailedPush = false; 
		numpops -= m_NumFailedPushes;
		m_NumFailedPushes = 0;
		m_Engine.pop(numpops);
		for (int i = 0; i < numpops; ++i) {
//			if (m_BooleanVars != null)
//				m_BooleanVars.endScope();
//			m_arraySorts.endScope();
			for (SharedTerm t : m_UnshareCC.currentScope())
				t.unshareCC();
			m_UnshareCC.endScope();
			for (SharedTerm t : m_UnshareLA.currentScope())
				t.unshareLA();
			m_UnshareLA.endScope();
//			for (FlatFormula f : m_RemoveLit.currentScope())
//				f.literalRemoved();
//			m_RemoveLit.endScope();
			m_Equalities.endScope();
			popUndoTrail();
			m_SharedTerms.endScope();
		}
		m_StackLevel -= numpops;
	}
	
	public void setSourceAnnotation(int leafKind, IAnnotation sourceAnnot) {
		m_Proof = new LeafNode(leafKind, sourceAnnot);
	}
	
	private ProofNode getProofNewSource(Term source) {
		return getProofNewSource(LeafNode.NO_THEORY, source);
	}
	
	private ProofNode getProofNewSource(int leafKind, Term source) {
		if (source == null)
			return m_Proof;
		if (m_Proof instanceof LeafNode) {
			LeafNode ln = (LeafNode) m_Proof;
			SourceAnnotation annot = 
					new SourceAnnotation(
							(SourceAnnotation) ln.getTheoryAnnotation(),
							source);
			return new LeafNode(leafKind, annot);
		}
		return m_Proof;
	}
	
	private ProofNode getClauseProof(Term proofTerm) {
		proofTerm = m_Tracker.clause(proofTerm);
		return getProofNewSource(proofTerm);
	}
	public IAnnotation getAnnotation() {
		if (m_Proof instanceof LeafNode)
			return ((LeafNode) m_Proof).getTheoryAnnotation();
		return null;
	}
	
	public Theory getTheory() {
		return m_Theory;
	}
	
	private void trackAssignment(Term term, Set<String> names) {
		Literal lit;
		Term idx = toPositive(term);
		boolean pos = idx == term;
		if (idx instanceof ApplicationTerm) {
			ApplicationTerm at = (ApplicationTerm) idx;
			FunctionSymbol fs = at.getFunction();
			if (fs.getName().equals("<=")) {
				lit = createLeq0(at);
			} else if (fs.getName().equals("=") &&
					at.getParameters()[0].getSort() !=
						m_Theory.getBooleanSort()) {
				SharedTerm lhs = getSharedTerm(at.getParameters()[0]);
				SharedTerm rhs = getSharedTerm(at.getParameters()[1]);
				EqualityProxy ep = createEqualityProxy(lhs, rhs);
				if (ep == EqualityProxy.getTrueProxy())
					lit = new DPLLAtom.TrueAtom();
				else if (ep == EqualityProxy.getFalseProxy())
					lit = new DPLLAtom.TrueAtom().negate();
				else
					lit = ep.getLiteral();
			} else if (!fs.isIntern() &&
					fs.getReturnSort() == m_Theory.getBooleanSort()) {
				lit = createBooleanLit(at);
			} else if (at == m_Theory.TRUE) {
				lit = new DPLLAtom.TrueAtom();
			} else if (at == m_Theory.FALSE) {
				lit = new DPLLAtom.TrueAtom().negate();
			} else {
				lit = getLiteralTseitin(term);
			}
		} else
			lit = getLiteralTseitin(term);
		if (!pos)
			lit = lit.negate();
		for (String name : names) {
			m_Engine.trackAssignment(name, lit);
		}
	}
	
	private Literal createLeq0(ApplicationTerm leq0term) {
		Literal lit = m_LiteralData.get(leq0term);
		if (lit == null) {
			SMTAffineTerm sum = SMTAffineTerm.create(leq0term.getParameters()[0]);
			MutableAffinTerm msum = createMutableAffinTerm(sum);
			lit = m_LASolver.generateConstraint(msum, false, m_StackLevel);
			m_LiteralData.put(leq0term, lit);
			m_UndoTrail = new RemoveAtom(m_UndoTrail, leq0term);
		}
		return lit;
	}
	
	private Literal createBooleanLit(ApplicationTerm term) {
		Literal lit = m_LiteralData.get(term);
		if (lit == null) {
			if (term.getParameters().length == 0) {
				lit = createBooleanVar(term);
			} else {
				SharedTerm st = getSharedTerm(term);
				EqualityProxy eq = createEqualityProxy(st, m_SharedTrue);
				// Safe since m_Term is neither true nor false
				assert eq != EqualityProxy.getTrueProxy();
				assert eq != EqualityProxy.getFalseProxy();
				lit = eq.getLiteral();
			}
			m_LiteralData.put(term, lit);
			m_UndoTrail = new RemoveAtom(m_UndoTrail, term);
		}
		return lit;
	}
	
	public boolean resetBy0Seen() {
		return m_Compiler.resetBy0Seen();
	}

	public IProofTracker getTracker() {
		return m_Tracker;
	}
	
}
