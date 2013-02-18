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

import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

/**
 * A non-recursive proof tree printer.  This class tries to avoid a stack
 * overflow by using an explicit stack that contains different visitors. 
 * @author Juergen Christ
 */
public class NonRecursivePrinter {
	/**
	 * A very abstract base interface used for non-recursive operations.
	 * @author Juergen Christ
	 */
	public static interface Visitor {
		public void visit(NonRecursivePrinter engine);
	}
	/**
	 * The stack of pending visitors.
	 */
	private Deque<Visitor> m_Todo = new ArrayDeque<Visitor>();
	/**
	 * Enqueue a new visitor.
	 * @param visitor Visitor to enqueue.
	 */
	void enqueue(Visitor visitor) {
		m_Todo.push(visitor);
	}
	/**
	 * Process visitors until all are processed.
	 */
	private void run() {
		while (!m_Todo.isEmpty())
			m_Todo.pop().visit(this);
	}
	/**
	 * Base name used to name clauses in the proof.
	 */
	private final static String NAME_BASE = "@pn";
	/**
	 * Number of the next proof node;
	 */
	private int m_NodeNumber = 0;
	/**
	 * Stack of recently produced antecedent names.
	 */
	private Deque<String> m_Names = new ArrayDeque<String>();
	/**
	 * Output writer.
	 */
	private PrintWriter m_Out;
	/**
	 * Theory used in sexpr conversion.
	 */
	private Theory m_Theory;
	/**
	 * Mapping from clauses to names of the corresponding proof node.
	 */
	private Map<Clause,String> m_Nodes = new HashMap<Clause, String>();
	/**
	 * Mapping from source formulas to proof nodes.
	 */
	private Map<Term, String> m_Sources = new HashMap<Term, String>();
	/**
	 * The number of open (yet to close) parenthesis.
	 */
	private int m_NumOpenParens = 0;
	/**
	 * Initialize the printer with a writer and a theory.
	 * @param out The writer.
	 * @param t   The theory.
	 */
	public NonRecursivePrinter(PrintWriter out, Theory t) {
		m_Out = out;
		m_Theory = t;
	}
	/**
	 * Push a generated antecedent name on the stack.
	 * @param name The name.
	 */
	public void pushName(String name) {
		m_Names.push(name);
	}
	/**
	 * Pop the name of the last generated antecedent.
	 * @return Last pushed antecedent name.
	 */
	public String popName() {
		return m_Names.pop();
	}
	/**
	 * Get the name of the next proof node.  This also increments the proof node
	 * counter.
	 * @return Name of the next proof node.
	 */
	public String nextProofNodeName() {
		return NAME_BASE + m_NodeNumber++;
	}
	public PrintWriter getWriter() {
		return m_Out;
	}
	public Theory getTheory() {
		return m_Theory;
	}
	public String getBinding(Clause cls) {
		return m_Nodes.get(cls);
	}
	public void putBinding(Clause cls, String binding) {
		m_Nodes.put(cls, binding);
	}
	public String getSourceBinding(Term source) {
		return m_Sources.get(source);
	}
	public void putSourceBinding(Term source, String binding) {
		m_Sources.put(source, binding);
	}
	/**
	 * Increase the number of parenthesis that should be closed after all
	 * visitors are processed.
	 */
	public void incOpenParens() {
		++m_NumOpenParens;
	}
	/**
	 * Print a proof tree.  This is the main entry function into the proof
	 * printer.
	 * @param cl Root of the proof tree, i.e., the bottom clause.
	 */
	public void printProof(Clause cl) {
		assert (cl.getSize() == 0);
		ProofNode pn = cl.getProof();
		assert(pn != null);
		if (pn.isLeaf()) {
//			LeafNode ln = (LeafNode)pn;
//			printLeaf(cl, ln);
			enqueue(new LeafPrinter(cl));
			enqueue(FinalLinePrinter.INSTANCE);
			enqueue(new LeafSourcePrinter(cl));
		} else {
			ResolutionNode rn = (ResolutionNode)pn;
			enqueue(new ResPrinter(rn.getAntecedents()));
			enqueue(FinalLinePrinter.INSTANCE);
			enqueue(new PremisePrinter(rn));
		}
		run();
		popName();
		// Matching closing brackets
		for (int i = 0; i < m_NumOpenParens; ++i)
			m_Out.print(')');
		m_Out.println();
		m_Out.flush();
	}
	/**
	 * Format a leaf of the proof tree.  This function dispatches the different
	 * annotations leaves may have and builds a corresponding output.
	 * @param cl
	 * @param ln
	 */
	void printLeaf(Clause cl, LeafNode ln) {
		/*
		 * Format: (! clause explanation)
		 * where explanation in:
		 *   :asserted SourceAnnotation?
		 *   :lemma (Theory TExpl?)
		 */
		IAnnotation annotation = ln.getTheoryAnnotation();
		if (annotation == null)
			printClause(cl);
		else if (ln.getLeafKind() == LeafNode.NO_THEORY) {
			SourceAnnotation source = (SourceAnnotation) annotation;
			CNFTermChecker checker = new CNFTermChecker();
			if (ln.isTautology()) {
				m_Out.print("(! ");
				printClause(cl);
				m_Out.print(" :tautology)");
			} else if (checker.check(source.getSource())) {
				m_Out.print("(! ");
				printClause(cl);
				m_Out.print(" ");
				m_Out.print(source.toSExpr(m_Theory));
				m_Out.print(")");
			} else {
				String sourceString = getSourceBinding(source.getSource());
				assert sourceString != null;
				m_Out.print("(@res (or (not ");
				m_Out.print(sourceString);
				m_Out.print(") ");
				printClause(cl);
				m_Out.print(") (! ");
				m_Out.print(sourceString);
				m_Out.print(" :pivot ");
				m_Out.print(sourceString);
				m_Out.print("))");
			}
		} else {
			String end = ")";
			m_Out.print("(! ");
			printClause(cl);
			switch (ln.getLeafKind()) {
			case LeafNode.NO_THEORY:
			{
				// Cannot be reached anymore.
				break;
			}
			case LeafNode.QUANT_INST:
				m_Out.print(" :lemma (:Quant");
				end = "))";
				break;
			case LeafNode.THEORY_CC:
				m_Out.print(" :lemma (:CC");
				end = "))";
				break;
			case LeafNode.THEORY_LA:
				m_Out.print(" :lemma (:LA");
				end = "))";
				break;
			default:
				// TODO: What to do here?
				break;
			}
			m_Out.print(' ');
			m_Out.print(annotation.toSExpr(m_Theory));
			m_Out.print(end);
		}		
	}
	/**
	 * Print a single clause.  This function takes care of the empty clause or
	 * unit clauses (since in SMTLIB, or takes at least 2 arguments).
	 * @param cl The clause to print.
	 */
	void printClause(Clause cl) {
		// Short path for empty clause
		if (cl.getSize() == 0) {
			m_Out.print("false");
		} else if (cl.getSize() == 1) {
			printLiteral(cl.getLiteral(0));
		} else {
			m_Out.print("(or");
			for (int i = 0; i < cl.getSize(); ++i) {
				m_Out.print(' ');
				printLiteral(cl.getLiteral(i));
			}
			m_Out.print(')');
		}
	}
	/**
	 * Helper function to print a literal.  This function always uses the print
	 * function of the atom to ease readability.
	 * @param lit The literal to print.
	 */
	void printLiteral(Literal lit) {
		DPLLAtom atom = lit.getAtom();
		if (lit.getSign() == -1)
			m_Out.print("(not ");
		m_Out.print(atom.getSMTFormula(m_Theory));
		if (lit.getSign() == -1)
			m_Out.print(')');
	}
	/**
	 * A class that print the left-associative resolution chain for a resolution
	 * node.  The clauses of this node (i.e., the antecedents) have to be
	 * declared before and their names have to be on the name stack.  To get
	 * nice numbers (consecutive numbers for output), we mess up the stack a
	 * little such that the content of the stack when this visitor is called is
	 * assumed to be
	 * 
	 * |----------------------------------|
	 * | name of the result node          |
	 * | name of the n-th antecedent      |
	 * | ...                              |
	 * | name of the first antecedent     |
	 * | name of the resolution primary   |
	 * | ...                              |
	 * 
	 * The stack is changed by only removing the names of the antecedents and
	 * the primary:
	 * 
	 * |----------------------------------|
	 * | name of the result node          |
	 * | ...                              |
	 * @author Juergen Christ
	 */
	private final static class ResPrinter implements Visitor {
		/**
		 * Antecedents of the resolution.
		 */
		private final Antecedent[] m_Antes;

		public ResPrinter(Antecedent[] antes) {
			m_Antes = antes;
		}
		
		@Override
		public void visit(NonRecursivePrinter nrp) {
			// Name stack contains the name of the result, names of the
			// antecedents, name of the primary, ...
			String myname = nrp.popName();
			PrintWriter out = nrp.getWriter();
			String[] names = new String[m_Antes.length + 1];
			for (int i = names.length - 1; i >= 0; --i)
				names[i] = nrp.popName();
			out.print("(@res ");
			out.print(names[0]);
			for (int i = 1; i < names.length; ++i) {
				out.print(" (! ");
				out.print(names[i]);
				out.print(" :pivot ");
				nrp.printLiteral(m_Antes[i - 1].pivot);
				out.print(')');
			}
			out.print(')');
			nrp.pushName(myname);
		}
		
	}
	/**
	 * Print the let prefix and generate a new name for a clause.  The newly
	 * created name is pushed onto the stack.
	 * 
	 * Note that names are created lazily in {@link #visit(NonRecursive)}.
	 * Hence, they are pushed onto the stack when this visitor is executed.
	 * This messes up the stack as described in {@link ResPrinter}.
	 * @author Juergen Christ
	 */
	private final static class LetPrinter implements Visitor {

		private Clause m_Cls;
		
		public LetPrinter(Clause c) {
			m_Cls = c;
		}
		
		@Override
		public void visit(NonRecursivePrinter nrp) {
			assert nrp.getBinding(m_Cls) == null;
			String name = nrp.nextProofNodeName();
			nrp.putBinding(m_Cls, name);
			nrp.pushName(name);
			PrintWriter out = nrp.getWriter();
			out.println();
			out.print("(let ((");
			out.print(name);
			out.print(' ');
		}
		
	}
	/**
	 * Closes the parenthesis opened in a let except for the last one.  This
	 * last open parenthesis is closed by the
	 * {@link NonRecursivePrinter#printProof(Clause)} method.
	 * @author Juergen Christ
	 */
	private final static class LetEndPrinter implements Visitor {
		final static LetEndPrinter INSTANCE = new LetEndPrinter();
		@Override
		public void visit(NonRecursivePrinter nrp) {
			nrp.getWriter().print("))");
			nrp.incOpenParens();
		}
		
	}
	/**
	 * Print a leaf by calling
	 * {@link NonRecursivePrinter#printLeaf(Clause, LeafNode)}.
	 * @author Juergen Christ
	 */
	private final static class LeafPrinter implements Visitor {

		private Clause m_Cls;
		
		public LeafPrinter(Clause cls) {
			assert cls.getProof().isLeaf();
			m_Cls = cls;
		}
		
		@Override
		public void visit(NonRecursivePrinter nrp) {
			nrp.printLeaf(m_Cls, (LeafNode) m_Cls.getProof());
		}
		
	}
	
	private final static class LeafSourcePrinter implements Visitor {

		private Clause m_Cls;
		
		public LeafSourcePrinter(Clause cls) {
			assert cls.getProof().isLeaf();
			m_Cls = cls;
		}
		
		@Override
		public void visit(NonRecursivePrinter engine) {
			LeafNode ln = (LeafNode) m_Cls.getProof();
			IAnnotation annotation = ln.getTheoryAnnotation();
			CNFTermChecker checker = new CNFTermChecker();
			if (annotation != null && ln.getLeafKind() == LeafNode.NO_THEORY) {
				SourceAnnotation source = (SourceAnnotation) annotation;
				if (!ln.isTautology() && !checker.check(source.getSource())) {
					// We need to let this source
					String name = engine.getSourceBinding(source.getSource());
					if (name == null) {
						name = engine.nextProofNodeName();
						engine.putSourceBinding(source.getSource(), name);
						engine.getWriter().println();
						engine.getWriter().print("(let ((");
						engine.getWriter().print(name);
						engine.getWriter().print(" (! ");
						engine.getWriter().print(
								source.getSource().toStringDirect());
						engine.getWriter().print(' ');
						engine.getWriter().print(
								source.toSExpr(engine.getTheory()));
						engine.getWriter().print(")))");
						engine.incOpenParens();
					}
				}
			}
		}
	}
	
	/**
	 * A visitor that prints or enqueues the remaining proof tree.
	 * @author Juergen Christ
	 */
	private final static class Printer implements Visitor {
		/**
		 * The clause backing the proof tree.
		 */
		private Clause m_Cls;
		
		public Printer(Clause c) {
			m_Cls = c;
		}
		
		@Override
		public void visit(NonRecursivePrinter nrp) {
			String name = nrp.getBinding(m_Cls);
			if (name != null)
				nrp.pushName(name);
			else {
				nrp.enqueue(LetEndPrinter.INSTANCE);
				ProofNode pn = m_Cls.getProof();
				if (pn.isLeaf()) {
					nrp.enqueue(new LeafPrinter(m_Cls));
					nrp.enqueue(new LetPrinter(m_Cls));
					nrp.enqueue(new LeafSourcePrinter(m_Cls));
				} else {
					ResolutionNode rn = (ResolutionNode) pn;
					nrp.enqueue(new ResPrinter(rn.getAntecedents()));
					nrp.enqueue(new LetPrinter(m_Cls));
					nrp.enqueue(new PremisePrinter(rn));
				}
			}
		}

	}
	/**
	 * Enqueue printers for the antecedents and the primary of a resolution.
	 * @author Juergen Christ
	 */
	private final static class PremisePrinter implements Visitor {
		private ResolutionNode m_Node;

		public PremisePrinter(ResolutionNode node) {
			m_Node = node;
		}

		@Override
		public void visit(NonRecursivePrinter nrp) {
			Antecedent[] antes = m_Node.getAntecedents();
			for (int i = antes.length - 1; i >= 0; --i)
				nrp.enqueue(new Printer(antes[i].antecedent));
			nrp.enqueue(new Printer(m_Node.getPrimary()));
		}
		
	}
	/**
	 * Prepare for printing the final resolution line.  This line should be
	 * placed on an own line.  Furthermore, this is a resolution line without a
	 * corresponding let binding.  Hence, the assumption of {@link ResPrinter}
	 * that the name of the resulting node is on the name stack is violated so
	 * far.  We fix this assumption by pushing a dummy name.
	 * @author Juergen Christ
	 */
	private final static class FinalLinePrinter implements Visitor {
		final static FinalLinePrinter INSTANCE = new FinalLinePrinter();
		@Override
		public void visit(NonRecursivePrinter nrp) {
			// ResPrinter expects the name of the resolution node.  Since the
			// root node does not get a name, we have to put a dummy.
			nrp.pushName("dummy");
			nrp.getWriter().println();
		}
		
	}
}
