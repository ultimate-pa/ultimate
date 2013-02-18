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
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;


public class ProofPrinter {
	/**
	 * Base name used to name clauses in the proof.
	 */
	private final static String NAME_BASE = "@pn";
	private int m_indentation = 0;
	private int m_nodecounter = 0;
	// Number of closing brackets
	private int m_numclosing = 0;
	private boolean newline = false;
	// Mapping from clause in the proof to its let-binding
	private Map<Clause,String> m_nodes = new HashMap<Clause, String>();
	private PrintWriter m_out;
	private Theory m_theory;
	public ProofPrinter(PrintWriter out, Theory theory) {
		m_out = out;
		m_theory = theory;
	}
	private void indent() {
		if (newline)
			m_out.println();
		newline = true;
		for (int i = 0; i < m_indentation; ++i)
			m_out.write(' ');
	}
	public void printProof(Clause cl) {
		assert (cl.getSize() == 0);
		ProofNode pn = cl.getProof();
		assert(pn != null);
		if (pn.isLeaf()) {
			LeafNode ln = (LeafNode)pn;
			printLeaf(cl, ln);
		} else {
			ResolutionNode rn = (ResolutionNode)pn;
			String[] prems = printPremises(rn);
			Antecedent[] ants = rn.getAntecedents();
			indent();
			printRes(prems, ants);
		
			// Matching closing brackets
			for (int i = 0; i < m_numclosing; ++i)
				m_out.print(')');
		}
		m_out.println();
		m_out.flush();
	}
	
	private String[] printPremises(ResolutionNode rn) {
		Antecedent[] ants = rn.getAntecedents();
		String[] res = new String[ants.length + 1];
		res[0] = printProofClause(rn.getPrimary());
		for (int i = 0; i < ants.length; ++i)
			res[i+1] = printProofClause(ants[i].antecedent);
		return res;
	}
	
	private String printProofClause(Clause c) {
		String binding = m_nodes.get(c);
		if (binding != null)
			return binding;
		ProofNode pn = c.getProof();
		String name;
		if (pn.isLeaf()) {
			LeafNode ln = (LeafNode)pn;
			name = NAME_BASE + m_nodecounter++;
			m_nodes.put(c, name);
			indent();
			m_out.print("(let ((");
			m_out.print(name);
			m_out.print(' ');
			printLeaf(c, ln);
		} else {
			ResolutionNode rn = (ResolutionNode)pn;
			String[] prems = printPremises(rn);
			Antecedent[] ants = rn.getAntecedents();
			name = NAME_BASE + m_nodecounter++;
			m_nodes.put(c, name);
			m_indentation += Config.INDENTATION;
			indent();
			m_out.print("(let ((");
			m_out.print(name);
			m_out.print(' ');
			printRes(prems, ants);
		}
		m_out.print("))");
		++m_numclosing;
		return name;
	}
	
	private void printRes(String[] prems, Antecedent[] ants){
		assert prems.length == ants.length + 1;
		m_out.print("(@res ");
		m_out.print(prems[0]);
		for (int i = 1; i < prems.length; ++i) {
			m_out.print(" (! ");
			m_out.print(prems[i]);
			m_out.print(" :pivot ");
			m_out.print(ants[i - 1].pivot.getSMTFormula(m_theory));
			m_out.print(')');
		}
		m_out.print(')');
	}
		
	private void printLeaf(Clause cl, LeafNode ln) {
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
			if (checker.check(source.getSource())) {
				m_out.print("(! ");
				printClause(cl);
				m_out.print(" ");
				m_out.print(source.toSExpr(m_theory));
				m_out.print(")");
			} else {
				String sourceString = source.getSource().toStringDirect();
				m_out.print("(@res (or (not ");
				m_out.print(sourceString);
				m_out.print(") ");
				printClause(cl);
				m_out.print(") (! ");
				m_out.print(sourceString);
				m_out.print(" ");
				m_out.print(source.toSExpr(m_theory));
				m_out.print(" :pivot ");
				m_out.print(sourceString);
				m_out.print("))");
			}
		} else {
			String end = ")";
			m_out.print("(! ");
			printClause(cl);
			switch (ln.getLeafKind()) {
			case LeafNode.NO_THEORY:
			{
				// Cannot be reached anymore.
				break;
			}
			case LeafNode.QUANT_INST:
				m_out.print(" :lemma (:Quant");
				end = "))";
				break;
			case LeafNode.THEORY_CC:
				m_out.print(" :lemma (:CC");
				end = "))";
				break;
			case LeafNode.THEORY_LA:
				m_out.print(" :lemma (:LA");
				end = "))";
				break;
			default:
				// TODO: What to do here?
				break;
			}
			m_out.print(' ');
			m_out.print(annotation.toSExpr(m_theory));
			m_out.print(end);
		}		
	}
	
	private void printClause(Clause cl) {
		// Short path for empty clause
		if (cl.getSize() == 0) {
			m_out.print("false");
		} else if (cl.getSize() == 1) {
			m_out.print(cl.getLiteral(0).getSMTFormula(m_theory));
		} else {
			m_out.print("(or");
			for (int i = 0; i < cl.getSize(); ++i) {
				m_out.print(' ');
				m_out.print(cl.getLiteral(i).getSMTFormula(m_theory));
			}
			m_out.print(')');
		}
	}
}
