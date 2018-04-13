/*
 * Copyright (C) 2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.horn;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap.CopyMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

public class HornSolver extends NoopScript {
	class HornClause {
		List<TermVariable> mTvs;
		ApplicationTerm mHead;
		List<ApplicationTerm> mBody;
		Term mPhi;

		public HornClause(final List<TermVariable> tvs, final ApplicationTerm head, final List<ApplicationTerm> body,
				final Term phi) {
			mTvs = tvs;
			mHead = head;
			mBody = body;
			mPhi = phi;
		}
	}

	class DerivationTreeNode {
		ApplicationTerm mTerm;
		Term mName;
		DerivationTreeNode[] mChildren;

		public DerivationTreeNode(final ApplicationTerm term) {
			mTerm = term;
		}

		public void setName(final Term name) {

			mName = name;
		}

		public void initChildren(final int size) {
			mChildren = new DerivationTreeNode[size];
		}

		public DerivationTreeNode addChild(final int pos, final ApplicationTerm term) {
			assert mChildren[pos] == null;
			return mChildren[pos] = new DerivationTreeNode(term);
		}

		public int postOrderTraverse(final ArrayList<Term> partition, final ArrayList<Integer> startOfSubtree) {
			int pos = partition.size();
			if (mChildren.length > 0) {
				pos = mChildren[0].postOrderTraverse(partition, startOfSubtree);
				for (int i = 1; i < mChildren.length; ++i) {
					mChildren[i].postOrderTraverse(partition, startOfSubtree);
				}
			}
			partition.add(mName);
			startOfSubtree.add(pos);
			return pos;
		}

		public void printSolution(final Term[] solution) {
			printSolutionRec(solution, 0);
		}

		private int printSolutionRec(final Term[] solution, int offset) {
			for (final DerivationTreeNode n : mChildren) {
				offset += n.printSolutionRec(solution, offset);
			}
			System.err.print(mTerm);
			System.err.print(" = ");
			System.err.println((offset >= solution.length) ? "false" : solution[offset]);
			final SMTInterpol backend = (SMTInterpol) mBackend;
			final SimplifyDDA simp = new SimplifyDDA(new SMTInterpol(backend,
					Collections.singletonMap(":check-type", (Object) "quick"), CopyMode.CURRENT_VALUE));
			if (offset < solution.length) {
				System.err.println("size: " + new DAGSize().size(solution[offset]));
				final Term simplified = simp.getSimplifiedTerm(solution[offset]);
				System.err.println("simplified: " + simplified);
				System.err.println("simpsize: " + new DAGSize().size(simplified));
			}
			return offset + 1;
		}
	}

	HashMap<FunctionSymbol, ArrayList<HornClause>> mAllClauses;
	Script mBackend;

	public HornSolver() {
		mAllClauses = new HashMap<>();
		mBackend = new SMTInterpol();
		mBackend.setOption(":produce-interpolants", Boolean.TRUE);
		// m_Backend.setOption(":interpolant-check-mode", Boolean.TRUE);
		mBackend.setOption(":verbosity", 2);
		// try {
		// m_Backend = new LoggingScript(m_Backend, "/tmp/back.smt2", true);
		// } catch (FileNotFoundException ex) {
		// throw new RuntimeException("Cannot open temp file.", ex);
		// }
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		if (!logic.equals("HORN")) {
			throw new SMTLIBException("No Horn logic");
		}
		super.setLogic(Logics.AUFLIRA);
		mBackend.setLogic(Logics.QF_LIA);
	}

	@Override
	public void setOption(final String opt, final Object value) {
		super.setOption(opt, value);
		mBackend.setOption(opt, value);
	}

	@Override
	public void setInfo(final String info, final Object value) {
		super.setInfo(info, value);
		if (info.equals(":status")) {
			if (value.equals("sat")) {
				mBackend.setInfo(info, "unsat");
			} else if (value.equals("unsat")) {
				mBackend.setInfo(info, "sat");
			}
		}
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		term = toPrenex(term);
		final ArrayList<TermVariable> tvList = new ArrayList<>();
		while (term instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) term;
			if (qf.getQuantifier() != QuantifiedFormula.FORALL) {
				throw new SMTLIBException("Illegal Horn Clause");
			}
			tvList.addAll(Arrays.asList(qf.getVariables()));
			term = qf.getSubformula();
		}
		if (isNegatedTerm(term)) {
			term = ((ApplicationTerm) term).getParameters()[0];
		} else {
			term = term("not", term);
		}

		final ArrayDeque<Term> todo = new ArrayDeque<>();
		final ArrayList<Term> literals = new ArrayList<>();
		todo.addLast(term);
		while (!todo.isEmpty()) {
			term = todo.removeFirst();
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().isIntern() && appTerm.getFunction().getName().equals("and")) {
					todo.addAll(Arrays.asList(appTerm.getParameters()));
				} else {
					literals.add(term);
				}
			} else {
				literals.add(term);
			}
		}
		final ArrayList<Term> phi = new ArrayList<>();
		ApplicationTerm head = null;
		final ArrayList<ApplicationTerm> body = new ArrayList<>();
		for (final Term lit : literals) {
			if (isNegatedTerm(lit)) {
				final Term neglit = ((ApplicationTerm) lit).getParameters()[0];
				if (neglit instanceof ApplicationTerm && !((ApplicationTerm) neglit).getFunction().isIntern()) {
					if (head != null) {
						throw new SMTLIBException("Illegal Horn Clause");
					}
					head = (ApplicationTerm) neglit;
					continue;
				}
			}
			if (lit instanceof ApplicationTerm && !((ApplicationTerm) lit).getFunction().isIntern()) {
				body.add((ApplicationTerm) lit);
				continue;
			}
			phi.add(lit);
		}
		if (head == null) {
			head = (ApplicationTerm) term("false");
		}
		addHornClause(tvList, head, body, phi);
		return LBool.UNKNOWN;
	}

	private Term toPrenex(Term term) {
		class PrenexTransformer extends TermTransformer {
			LinkedHashSet<TermVariable> mTvs = new LinkedHashSet<>();

			@Override
			public void convert(Term term) {
				while (term instanceof QuantifiedFormula) {
					final QuantifiedFormula qf = (QuantifiedFormula) term;
					// TODO: check sign
					for (final TermVariable tv : qf.getVariables()) {
						if (mTvs.contains(tv)) {
							throw new SMTLIBException("Variable " + tv + " occurs more than once");
						}
						mTvs.add(tv);
					}
					term = qf.getSubformula();
				}
				super.convert(term);
			}
		}
		final PrenexTransformer trafo = new PrenexTransformer();
		term = trafo.transform(term);
		if (!trafo.mTvs.isEmpty()) {
			final TermVariable[] vars = trafo.mTvs.toArray(new TermVariable[trafo.mTvs.size()]);
			term = quantifier(FORALL, vars, term);
		}
		return term;
	}

	private void addHornClause(final ArrayList<TermVariable> tvList, final ApplicationTerm head,
			final ArrayList<ApplicationTerm> body, final ArrayList<Term> phi) {
		Term phiAsTerm;
		if (phi.size() <= 1) { // NOPMD
			if (phi.isEmpty()) {
				phiAsTerm = term("true");
			} else {
				phiAsTerm = phi.get(0);
			}
		} else {
			phiAsTerm = term("and", phi.toArray(new Term[phi.size()]));
		}
		tvList.trimToSize();
		body.trimToSize();
		ArrayList<HornClause> clauses = mAllClauses.get(head.getFunction());
		if (clauses == null) {
			clauses = new ArrayList<>(1);
			mAllClauses.put(head.getFunction(), clauses);
		}
		clauses.add(new HornClause(tvList, head, body, phiAsTerm));
	}

	private Term translateToBackend(final Term phi) {
		return new TermTransformer() {
			@Override
			public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
				setResult(mBackend.term(appTerm.getFunction().getName(), newArgs));
			}

			@Override
			public void convert(final Term term) {
				if (term instanceof TermVariable) {
					final TermVariable tv = (TermVariable) term;
					final Sort sort = mBackend.sort(tv.getSort().getName());
					setResult(mBackend.variable(tv.getName(), sort));
				} else if (term instanceof ConstantTerm) {
					final Object value = ((ConstantTerm) term).getValue();
					if (value instanceof BigInteger) {
						setResult(mBackend.numeral((BigInteger) value));
					} else if (value instanceof BigDecimal) {
						setResult(mBackend.decimal((BigDecimal) value));
					} else {
						throw new AssertionError("Unknown constant: " + value);
					}
				} else {
					super.convert(term);
				}
			}
		}.transform(phi);
	}

	private boolean isNegatedTerm(final Term lit) {
		if (!(lit instanceof ApplicationTerm)) {
			return false;
		}
		final ApplicationTerm appTerm = (ApplicationTerm) lit;
		return appTerm.getFunction().isIntern() && appTerm.getFunction().getName().equals("not");
	}

	private int mClauseCtr = 0;

	@Override
	public LBool checkSat() {
		final FormulaUnLet unletter = new FormulaUnLet();
		final ArrayDeque<DerivationTreeNode> todo = new ArrayDeque<>();
		DerivationTreeNode root;
		todo.add(root = new DerivationTreeNode((ApplicationTerm) term("false")));
		while (!todo.isEmpty()) {
			final DerivationTreeNode n = todo.removeFirst();
			final ApplicationTerm head = n.mTerm;
			final ArrayList<HornClause> hclist = mAllClauses.get(head.getFunction());
			if (hclist.size() > 1) {
				System.err.println("Cannot solve disjunctive Horn Clauses, yet");
				return LBool.UNKNOWN;
			}
			final HornClause hc = hclist.get(0);
			final TermVariable[] tvs = hc.mTvs.toArray(new TermVariable[hc.mTvs.size()]);
			final Term[] freshConstants = createConstants(tvs);
			final Term[] headParam = head.getParameters();
			final Term[] hcheadParam = hc.mHead.getParameters();
			final Term[] eqs = new Term[headParam.length + 1];
			eqs[0] = hc.mPhi;
			for (int i = 0; i < head.getParameters().length; i++) {
				eqs[i + 1] = term("=", headParam[i], hcheadParam[i]);
			}
			Term term = eqs.length > 1 ? term("and", eqs) : eqs[0];
			term = let(tvs, freshConstants, term);
			term = unletter.transform(term);
			term = translateToBackend(term);
			final String name = "X" + mClauseCtr++;
			term = mBackend.annotate(term, new Annotation(":named", name));
			mBackend.assertTerm(term);
			n.setName(mBackend.term(name));
			// System.err.println("(assert "+term+")");

			n.initChildren(hc.mBody.size());
			int i = 0;
			for (final ApplicationTerm appTerm : hc.mBody) {
				term = unletter.transform(let(tvs, freshConstants, appTerm));
				todo.add(n.addChild(i++, (ApplicationTerm) term));
			}
		}
		long nanotime = System.nanoTime();
		final LBool result = mBackend.checkSat();
		System.err.println("SAT Check Time: " + (System.nanoTime() - nanotime));
		if (result == LBool.UNSAT) {
			// Compute solution
			final ArrayList<Term> partition = new ArrayList<>();
			final ArrayList<Integer> startOfSubtree = new ArrayList<>();
			root.postOrderTraverse(partition, startOfSubtree);
			final int[] sos = new int[startOfSubtree.size()];
			int pos = 0;
			for (final Integer i : startOfSubtree) {
				sos[pos++] = i.intValue();
			}
			try {
				nanotime = System.nanoTime();
				final Term[] solution = mBackend.getInterpolants(partition.toArray(new Term[partition.size()]), sos);
				System.err.println("Interpolation Time: " + (System.nanoTime() - nanotime));
				root.printSolution(solution);
			} catch (final SMTLIBException ese) {
				System.err.println(ese);
				System.exit(1);
			}
		}
		return result == LBool.SAT ? LBool.UNSAT : LBool.SAT;
	}

	private int mCtr = 0;

	private Term[] createConstants(final TermVariable[] tvs) {
		final Term[] values = new Term[tvs.length];
		for (int i = 0; i < tvs.length; i++) {
			final String name = "x" + mCtr++;
			final Sort sort = tvs[i].getSort();
			declareFun(name, new Sort[0], sort);
			final Sort bsort = mBackend.sort(sort.getName());
			mBackend.declareFun(name, new Sort[0], bsort);
			// System.err.println("(declare-fun "+name+" () "+bsort+")");
			values[i] = term(name);
		}
		return values;
	}

	@Override
	public void reset() {
		super.reset();
		mBackend.reset();
		mAllClauses.clear();
		mCtr = 0;
		mClauseCtr = 0;
	}
}
