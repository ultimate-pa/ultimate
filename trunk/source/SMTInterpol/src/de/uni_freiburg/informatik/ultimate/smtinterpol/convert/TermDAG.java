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
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
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
		protected final List<Edge> mIncomming = new ArrayList<Edge>();
		protected final List<Edge> mOutgoing = new ArrayList<Edge>();
		int mRegPos = -1;
		public void addIncomming(Edge in) { // NOPMD
			mIncomming.add(in);
		}
		public void addOutgoing(Edge out) { // NOPMD
			mOutgoing.add(out);
		}
		public Iterable<Edge> getIncomming() {
			return mIncomming;
		}
		public Iterable<Edge> getOutgoing() {
			return mOutgoing;
		}
		public void setRegPos(int regPos) {
			mRegPos = regPos;
		}
		public int getRegPos() {
			return mRegPos;
		}
		public boolean isInRegister() {
			return mRegPos != -1;
		}
		public void removeFromRegister() {
			mRegPos = -1;
		}
	}
	/**
	 * A markable edge from one node to another. The edge also stores to
	 * position of the argument (<code>getTo()</code>) in the function
	 * application (<code>getFrom()</code>).
	 * @author Juergen Christ
	 */
	public static final class Edge {
		boolean mMarked;
		final TermNode mFrom,mTo;
		final int mNum;
		public Edge(TermNode from,TermNode to,int num) {
			mMarked = false;
			mFrom = from;
			mTo = to;
			mNum = num;
			from.addOutgoing(this);
			to.addIncomming(this);
		}
		public void mark() {
			mMarked = true;
		}
		public boolean isMarked() {
			return mMarked;
		}
		public int getNumber() {
			return mNum;
		}
		public TermNode getFrom() {
			return mFrom;
		}
		public TermNode getTo() {
			return mTo;
		}
		@Override
		public String toString() {
			return mFrom + " --> " + mTo;
		}
	}
	/**
	 * A function application.  At least one of the child nodes contains a
	 * variable.
	 * @author Juergen Christ
	 */
	public static class AppTermNode extends TermNode {
		final FunctionSymbol mSymbol;
		public AppTermNode(FunctionSymbol symbol) {
			mSymbol = symbol;
		}
		public FunctionSymbol getSymbol() {
			return mSymbol;
		}
		public int getChildCount() {
			assert(mOutgoing.size() == mSymbol.getParameterSorts().length);
			return mSymbol.getParameterSorts().length;
		}
		public void addChild(TermNode child,int pos) {
			new Edge(this,child,pos);
		}
		public Edge getChild(int pos) {
			final Edge res = mOutgoing.get(pos);
			if (res.getNumber() != pos) {
				for (final Edge e : mOutgoing) {
					if (e.getNumber() == pos) {
						return e;
					}
				}
			}
			return res;
		}
		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append('(').append(mSymbol.getName());
			for (final Edge e : mOutgoing) {
				sb.append(' ').append(e.mTo);
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
		final Term mConst;
		public ConstTermNode(Term constant) {
			assert(constant.getFreeVars().length == 0);
			mConst = constant;
		}
		public Term getConstant() {
			return mConst;
		}
		@Override
		public String toString() {
			return mConst.toString();
		}
	}
	/**
	 * A variable in the DAG.
	 * @author Juergen Christ
	 */
	public static class VarNode extends TermNode {
		final TermVariable mVar;
		public VarNode(TermVariable var) {
			mVar = var;
		}
		public TermVariable getVariable() {
			return mVar;
		}
		@Override
		public String toString() {
			return mVar.toString();
		}
	}
	private final LinkedHashSet<TermNode> mRoots;
	private final ArrayList<ConstTermNode> mConsts;
	private final ArrayList<VarNode> mVars;
	private final HashMap<Term, TermNode> mNodes;
	public TermDAG() {
		mRoots = new LinkedHashSet<TermNode>();
		mConsts = new ArrayList<ConstTermNode>();
		mVars = new ArrayList<VarNode>();
		mNodes = new HashMap<Term, TermNode>();
	}
	/**
	 * Build the DAG for all given triggers.
	 * @param triggers Input triggers.
	 * @return Term DAG representing the triggers.
	 */
	public TermNode[] buildDAG(Term[] triggers) {
		mRoots.clear();
		mConsts.clear();
		mVars.clear();
		mNodes.clear();
		for (final Term trig : triggers) {
			mRoots.add(insert(trig));
		}
		return mRoots.toArray(new TermNode[mRoots.size()]);
	}
	public CCTerm[] getConstants(Clausifier converter, SourceAnnotation source) {
		final CCTerm[] res = new CCTerm[mConsts.size()];
		int i = -1;
		for (final ConstTermNode ctn : mConsts) {
			res[++i] = converter.getSharedTerm(ctn.getConstant(), source).getCCTerm();
			ctn.setRegPos(i);
		}
		return res;
	}
	public Iterable<ConstTermNode> getConstants() {
		return mConsts;
	}
	public Iterable<VarNode> getVars() {
		return mVars;
	}
	private TermNode insert(Term trig) {
		final TermNode cached = mNodes.get(trig);
		if (cached != null) {
			return cached;
		}
		if (trig.getFreeVars().length == 0) {
			final ConstTermNode ctn = new ConstTermNode(trig);
			mConsts.add(ctn);
			mNodes.put(trig,ctn);
			return ctn;
		} else if (trig instanceof TermVariable) {
			final VarNode vn = new VarNode((TermVariable)trig);
			mNodes.put(trig,vn);
			mVars.add(vn);
			return vn;
		} else {
			assert(trig instanceof ApplicationTerm);
			final ApplicationTerm at = (ApplicationTerm)trig;
			final AppTermNode atn = new AppTermNode(at.getFunction());
			final Term[] params = at.getParameters();
			for (int i = 0; i < params.length; ++i) {
				atn.addChild(insert(params[i]), i);
			}
			mNodes.put(trig,atn);
			return atn;
		}
	}
}
