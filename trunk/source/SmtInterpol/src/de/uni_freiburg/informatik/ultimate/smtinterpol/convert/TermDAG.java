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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;


/**
 * A DAG for pattern compilers.
 * @author Juergen Christ
 */
public class TermDAG {
	/**
	 * Base class for all nodes in the DAG. This class stores to position of the
	 * term in the registers.
	 * @author Juergen Christ
	 */
	public static class TermNode {
		protected List<Edge> m_Incomming = new ArrayList<Edge>();
		protected List<Edge> m_Outgoing = new ArrayList<Edge>();
		int m_RegPos = -1;
		public void addIncomming(Edge in) {
			m_Incomming.add(in);
		}
		public void addOutgoing(Edge out) {
			m_Outgoing.add(out);
		}
		public Iterable<Edge> getIncomming() {
			return m_Incomming;
		}
		public Iterable<Edge> getOutgoing() {
			return m_Outgoing;
		}
		public void setRegPos(int regPos) {
			m_RegPos = regPos;
		}
		public int getRegPos() {
			return m_RegPos;
		}
		public boolean isInRegister() {
			return m_RegPos != -1;
		}
		public void removeFromRegister() {
			m_RegPos = -1;
		}
	}
	/**
	 * A markable edge from one node to another. The edge also stores to
	 * position of the argument (<code>getTo()</code>) in the function
	 * application (<code>getFrom()</code>).
	 * @author Juergen Christ
	 */
	public static final class Edge {
		boolean m_Marked;
		TermNode m_From,m_To;
		int m_Num;
		public Edge(TermNode from,TermNode to,int num) {
			m_Marked = false;
			m_From = from;
			m_To = to;
			m_Num = num;
			from.addOutgoing(this);
			to.addIncomming(this);
		}
		public void mark() {
			m_Marked = true;
		}
		public boolean isMarked() {
			return m_Marked;
		}
		public int getNumber() {
			return m_Num;
		}
		public TermNode getFrom() {
			return m_From;
		}
		public TermNode getTo() {
			return m_To;
		}
		public String toString() {
			return m_From + " --> " + m_To;
		}
	}
	/**
	 * A function application.  At least one of the child nodes contains a
	 * variable.
	 * @author Juergen Christ
	 */
	public static class AppTermNode extends TermNode {
		FunctionSymbol m_Symbol;
		public AppTermNode(FunctionSymbol symbol) {
			m_Symbol = symbol;
		}
		public FunctionSymbol getSymbol() {
			return m_Symbol;
		}
		public int getChildCount() {
			assert(m_Outgoing.size() == m_Symbol.getParameterCount());
			return m_Symbol.getParameterCount();
		}
		public void addChild(TermNode child,int pos) {
			new Edge(this,child,pos);
		}
		public Edge getChild(int pos) {
			Edge res = m_Outgoing.get(pos);
			if (res.getNumber() != pos) {
				for (Edge e : m_Outgoing) {
					if (e.getNumber() == pos)
						return e;
				}
			}
			return res;
		}
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append('(').append(m_Symbol.getName());
			for (Edge e : m_Outgoing) {
				sb.append(' ').append(e.m_To);
			}
			sb.append(')');
			return sb.toString();
		}
	}
	/**
	 * A term that does not contain a variable.  This might be any ground term
	 * including function applications to other ground terms.
	 * @author Juergen Christ
	 */
	public static class ConstTermNode extends TermNode {
		Term m_Const;
		public ConstTermNode(Term constant) {
			assert(constant.getFreeVars().length == 0);
			m_Const = constant;
		}
		public Term getConstant() {
			return m_Const;
		}
		public String toString() {
			return m_Const.toString();
		}
	}
	/**
	 * A variable in the DAG.
	 * @author Juergen Christ
	 */
	public static class VarNode extends TermNode {
		TermVariable m_Var;
		public VarNode(TermVariable var) {
			m_Var = var;
		}
		public TermVariable getVariable() {
			return m_Var;
		}
		public String toString() {
			return m_Var.toString();
		}
	}
	private LinkedHashSet<TermNode> m_Roots;
	private ArrayList<ConstTermNode> m_Consts;
	private ArrayList<VarNode> m_Vars;
	private HashMap<Term, TermNode> m_Nodes;
	public TermDAG() {
		m_Roots = new LinkedHashSet<TermNode>();
		m_Consts = new ArrayList<ConstTermNode>();
		m_Vars = new ArrayList<VarNode>();
		m_Nodes = new HashMap<Term, TermNode>();
	}
	/**
	 * Build the DAG for all given triggers.
	 * @param triggers Input triggers.
	 * @return Term DAG representing the triggers.
	 */
	public TermNode[] buildDAG(Term[] triggers) {
		m_Roots.clear();
		m_Consts.clear();
		m_Vars.clear();
		m_Nodes.clear();
		for (Term trig : triggers)
			m_Roots.add(insert(trig));
		return m_Roots.toArray(new TermNode[m_Roots.size()]);
	}
	public CCTerm[] getConstants(Clausifier converter) {
		CCTerm[] res = new CCTerm[m_Consts.size()];
		int i = -1;
		for (ConstTermNode ctn : m_Consts) {
			res[++i] = converter.getSharedTerm(ctn.getConstant()).getCCTerm();
			ctn.setRegPos(i);
		}
		return res;
	}
	public Iterable<ConstTermNode> getConstants() {
		return m_Consts;
	}
	public Iterable<VarNode> getVars() {
		return m_Vars;
	}
	private TermNode insert(Term trig) {
		TermNode cached = m_Nodes.get(trig);
		if (cached != null)
			return cached;
		if (trig.getFreeVars().length == 0) {
			ConstTermNode ctn = new ConstTermNode(trig);
			m_Consts.add(ctn);
			m_Nodes.put(trig,ctn);
			return ctn;
		} else if (trig instanceof TermVariable) {
			VarNode vn = new VarNode((TermVariable)trig);
			m_Nodes.put(trig,vn);
			m_Vars.add(vn);
			return vn;
		} else {
			assert(trig instanceof ApplicationTerm);
			ApplicationTerm at = (ApplicationTerm)trig;
			AppTermNode atn = new AppTermNode(at.getFunction());
			Term[] params = at.getParameters();
			for (int i = 0; i < params.length; ++i)
				atn.addChild(insert(params[i]), i);
			m_Nodes.put(trig,atn);
			return atn;
		}
	}
}
