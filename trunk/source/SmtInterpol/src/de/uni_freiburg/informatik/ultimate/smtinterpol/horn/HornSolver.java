package de.uni_freiburg.informatik.ultimate.smtinterpol.horn;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public class HornSolver extends NoopScript {
	class HornClause {
		List<TermVariable> m_Tvs;
		ApplicationTerm m_Head;
		List<ApplicationTerm> m_Body;
		Term m_Phi;
		
		public HornClause(List<TermVariable> tvs,
				ApplicationTerm head, List<ApplicationTerm> body,
				Term phi) {
			m_Tvs = tvs;
			m_Head = head;
			m_Body = body;
			m_Phi = phi;
		}
	}
	
	class DerivationTreeNode {
		ApplicationTerm m_Term;
		Term m_Name;
		DerivationTreeNode[] m_Children;
		public DerivationTreeNode(ApplicationTerm term) {
			m_Term = term;
		}
		public void setName(Term name) {
			
			m_Name = name;
		}
		public void initChildren(int size) {
			m_Children = new DerivationTreeNode[size];
		}
		public DerivationTreeNode addChild(int pos, ApplicationTerm term) {
			assert m_Children[pos] == null;
			return m_Children[pos] = new DerivationTreeNode(term);
		}
		public int postOrderTraverse(ArrayList<Term> partition,
				ArrayList<Integer> startOfSubtree) {
			int pos = partition.size();
			if (m_Children.length > 0) {
				pos = m_Children[0].postOrderTraverse(partition, startOfSubtree);
				for (int i = 1; i < m_Children.length; ++i)
					m_Children[i].postOrderTraverse(partition, startOfSubtree);
			}
			partition.add(m_Name);
			startOfSubtree.add(pos);
			return pos;
		}
		public void printSolution(Term[] solution) {
			printSolutionRec(solution, 0);
		}
		
		private int printSolutionRec(Term[] solution, int offset) {
			for (DerivationTreeNode n : m_Children)
				offset += n.printSolutionRec(solution, offset);
			System.err.print(m_Term);
			System.err.print(" = ");
			System.err.println((offset >= solution.length) ? "false" : solution[offset]);
			return offset + 1;
		}
	}
	
	HashMap<FunctionSymbol, ArrayList<HornClause>> m_AllClauses;
	Script m_Backend;
		
	public HornSolver() {
		m_AllClauses = new HashMap<FunctionSymbol,ArrayList<HornClause>>();
		m_Backend = new SMTInterpol();
		m_Backend.setOption(":produce-interpolants", Boolean.TRUE);
//		m_Backend.setOption(":interpolant-check-mode", Boolean.TRUE);
		m_Backend.setOption(":verbosity", 2);
//		try {
//			m_Backend = new LoggingScript(m_Backend, "/tmp/back.smt2", true);
//		} catch (FileNotFoundException ex) {
//			throw new RuntimeException("Cannot open temp file.", ex);
//		}
	}
	
	public void setLogic(String logic)
	throws UnsupportedOperationException, SMTLIBException {
		if (!logic.equals("HORN"))
			throw new SMTLIBException("No Horn logic");
		super.setLogic(Logics.AUFLIRA);
		m_Backend.setLogic(Logics.QF_LIA);
	}	
	
	public void setOption(String opt, Object value) {
		super.setOption(opt, value);
		m_Backend.setOption(opt, value);
	}	
	
	public void setInfo(String info, Object value) {
		super.setInfo(info, value);
		if (info.equals(":status")) {
			if (value.equals("sat"))
				m_Backend.setInfo(info, "unsat");
			else if (value.equals("unsat"))
				m_Backend.setInfo(info, "sat");
		}
	}	
	
	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		term = toPrenex(term);
		ArrayList<TermVariable> tvList = new ArrayList<TermVariable>();
		while (term instanceof QuantifiedFormula) {
			QuantifiedFormula qf = (QuantifiedFormula) term;
			if (qf.getQuantifier() != QuantifiedFormula.FORALL)
				throw new SMTLIBException("Illegal Horn Clause");
			tvList.addAll(Arrays.asList(qf.getVariables()));
			term = qf.getSubformula();
		}
		if (isNegatedTerm(term)) {
			term = ((ApplicationTerm) term).getParameters()[0];
		} else {
			term = term("not", term);
		}

		ArrayDeque<Term> todo = new ArrayDeque<Term>();
		ArrayList<Term> literals = new ArrayList<Term>();
		todo.addLast(term);
		while (!todo.isEmpty()) {
			term = todo.removeFirst();
			if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().isIntern()
					&& appTerm.getFunction().getName().equals("and")) {
					todo.addAll(Arrays.asList(appTerm.getParameters()));
				} else
					literals.add(term);
			} else 
				literals.add(term);
		}
		ArrayList<Term> phi = new ArrayList<Term>();
		ApplicationTerm head = null;
		ArrayList<ApplicationTerm> body = new ArrayList<ApplicationTerm>();
		for (Term lit : literals) {
			if (isNegatedTerm(lit)) {
				Term neglit = ((ApplicationTerm) lit).getParameters()[0];
				if (neglit instanceof ApplicationTerm
					&& !((ApplicationTerm)neglit).getFunction().isIntern()) {
					if (head != null)
						throw new SMTLIBException("Illegal Horn Clause");
					head = (ApplicationTerm) neglit;
					continue;
				}
			}
			if (lit instanceof ApplicationTerm
				&& !((ApplicationTerm)lit).getFunction().isIntern()) {
				body.add((ApplicationTerm) lit);
				continue;
			}
			phi.add(lit);
		}
		if (head == null)
			head = (ApplicationTerm) term("false");
		addHornClause(tvList, head, body, phi);
		return LBool.UNKNOWN;
	}

	private Term toPrenex(Term term) {
		class PrenexTransformer extends TermTransformer {
			LinkedHashSet<TermVariable> m_tvs = new LinkedHashSet<TermVariable>();
			
			public void convert(Term term) {
				while (term instanceof QuantifiedFormula) {
					QuantifiedFormula qf = (QuantifiedFormula) term;
					//TODO: check sign
					for (TermVariable tv : qf.getVariables()) {
						if (m_tvs.contains(tv))
							throw new SMTLIBException("Variable "+tv+" occurs more than once");
						m_tvs.add(tv);
					}
					term = qf.getSubformula();
				}
				super.convert(term);
			}
		}
		PrenexTransformer trafo = new PrenexTransformer();
		term = trafo.transform(term);
		if (!trafo.m_tvs.isEmpty()) {
			TermVariable[] vars = trafo.m_tvs.toArray
					(new TermVariable[trafo.m_tvs.size()]);
			term = quantifier(FORALL, vars, term);
		}
		return term;
	}

	private void addHornClause(ArrayList<TermVariable> tvList, ApplicationTerm head,
			ArrayList<ApplicationTerm> body, ArrayList<Term> phi) {
		Term phiAsTerm;
		if (phi.size() <= 1) {
			if (phi.isEmpty())
				phiAsTerm = term("true");
			else
				phiAsTerm = phi.get(0);
		} else {
			phiAsTerm = term("and", phi.toArray(new Term[phi.size()]));
		}
		tvList.trimToSize();
		body.trimToSize();
		ArrayList<HornClause> clauses = m_AllClauses.get(head.getFunction());
		if (clauses == null) {
			clauses = new ArrayList<HornClause>(1);
			m_AllClauses.put(head.getFunction(), clauses);
		}
		clauses.add(new HornClause(tvList, head, body, phiAsTerm));
	}

	private Term translateToBackend(Term phi) {
		return new TermTransformer() {
			@Override
			public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
				setResult(m_Backend.term(appTerm.getFunction().getName(), newArgs));
			}

			@Override
			public void convert(Term term) {
				if (term instanceof TermVariable) {
					TermVariable tv = (TermVariable) term;
					Sort sort = m_Backend.sort(tv.getSort().getName());
					setResult(m_Backend.variable(tv.getName(), sort));
				} else if (term instanceof ConstantTerm) {
					Object value = ((ConstantTerm)term).getValue();
					if (value instanceof BigInteger) {
						setResult(m_Backend.numeral((BigInteger)value));
					} else if (value instanceof BigDecimal) {
						setResult(m_Backend.decimal((BigDecimal)value));
					} else {
						throw new AssertionError("Unknown constant: "+value);
					}
				} else {
					super.convert(term);
				}
			}
		}.transform(phi);
	}

	private boolean isNegatedTerm(Term lit) {
		if (!(lit instanceof ApplicationTerm))
			return false;
		ApplicationTerm appTerm = (ApplicationTerm) lit;
		return appTerm.getFunction().isIntern()
				&& appTerm.getFunction().getName().equals("not");
	}
	
	private int m_ClauseCtr = 0;
	@Override
	public LBool checkSat() {
		FormulaUnLet unletter = new FormulaUnLet();
		ArrayDeque<DerivationTreeNode> todo =
				new ArrayDeque<DerivationTreeNode>();
		DerivationTreeNode root;
		todo.add(root = new DerivationTreeNode((ApplicationTerm) term("false")));
		while (!todo.isEmpty()) {
			DerivationTreeNode n = todo.removeFirst();
			ApplicationTerm head = n.m_Term;
			ArrayList<HornClause> hclist = m_AllClauses.get(head.getFunction());
			if (hclist.size() > 1) {
				System.err.println("Cannot solve disjunctive Horn Clauses, yet");
				return LBool.UNKNOWN;
			}
			HornClause hc = hclist.get(0);
			TermVariable[] tvs = hc.m_Tvs.toArray(new TermVariable[hc.m_Tvs.size()]);
			Term[] freshConstants = createConstants(tvs);
			Term[] headParam = head.getParameters();
			Term[] hcheadParam = hc.m_Head.getParameters();
			Term[] eqs = new Term[headParam.length + 1];
			eqs[0] = hc.m_Phi;
			for (int i = 0; i < head.getParameters().length; i++) {
				eqs[i+1] = term("=", headParam[i], hcheadParam[i]);
			}
			Term term = eqs.length > 1 ? term("and", eqs) : eqs[0];
			term = let(tvs, freshConstants, term);
			term = unletter.transform(term);
			term = translateToBackend(term);
			String name = "X"+(m_ClauseCtr++);
			term = m_Backend.annotate(term, new Annotation(":named", name));
			m_Backend.assertTerm(term);
			n.setName(m_Backend.term(name));
			//System.err.println("(assert "+term+")");
			
			n.initChildren(hc.m_Body.size());
			int i = 0;
			for (ApplicationTerm appTerm : hc.m_Body) {
				term = unletter.transform(let(tvs, freshConstants, appTerm));
				todo.add(n.addChild(i++, (ApplicationTerm)term));
			}
		}
		long nanotime = System.nanoTime();
		LBool result = m_Backend.checkSat();
		System.err.println("SAT Check Time: " + (System.nanoTime() - nanotime));
		if (result == LBool.UNSAT) {
			// Compute solution
			ArrayList<Term> partition = new ArrayList<Term>();
			ArrayList<Integer> startOfSubtree = new ArrayList<Integer>();
			root.postOrderTraverse(partition, startOfSubtree);
			int[] sos = new int[startOfSubtree.size()];
			int pos = 0;
			for (Integer i : startOfSubtree)
				sos[pos++] = i.intValue();
			try {
				nanotime = System.nanoTime();
				Term[] solution = m_Backend.getInterpolants(
						partition.toArray(new Term[partition.size()]), sos);
				System.err.println("Interpolation Time: " + (System.nanoTime() - nanotime));
				root.printSolution(solution);
			} catch (SMTLIBException se) {
				System.err.println(se);
				System.exit(1);
			}
		}
		return result == LBool.SAT ? LBool.UNSAT : LBool.SAT;
	}

	private int m_Ctr = 0;
	private Term[] createConstants(TermVariable[] tvs) {
		Term[] values = new Term[tvs.length];
		for (int i = 0; i < tvs.length; i++) {
			String name = "x"+(m_Ctr++);
			Sort sort = tvs[i].getSort();
			declareFun(name, new Sort[0], sort);
			Sort bsort = m_Backend.sort(sort.getName());
			m_Backend.declareFun(name, new Sort[0], bsort);
			//System.err.println("(declare-fun "+name+" () "+bsort+")");
			values[i] = term(name);
		}
		return values;
	}
	
	@Override
	public void reset() {
		super.reset();
		m_Backend.reset();
		m_AllClauses.clear();
		m_Ctr = 0;
		m_ClauseCtr = 0;
	}
}
