/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.boogie;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.ExpressionStatement;
import org.joogie.boogie.statements.Statement;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;

/**
 * Comments: in case of a major re-engineering, we should introduce subtypes of
 * this: procedures that actually relate to code, and prelude procedures prelude
 * procedure have one or no statement as body and no modify clause. right now,
 * we use isPure() to distinguish but this is not a clean solution.
 * 
 * @author schaef
 */
public class BoogieProcedure {
	// Call graph successors
	private final Set<BoogieProcedure> mCalledProcedures;
	// Call graph predecessors
	private final Set<BoogieProcedure> mCallingProcedures;

	// TODO: this should be refactored to somewhere else
	// SSA should not write fields within the procedure
	// better create a wrapper around the procedure
	private final Map<Variable, LinkedList<Variable>> mVarIncarnationMap;

	private final Set<Variable> mLocalVars;

	// The exceptions that can be returned by this procedure
	private final Map<BoogieType, Expression> mExceptionReturnExpressions;

	private final List<Variable> mParameterList;

	// The set of all globals modified in the body (including the ones modified
	// by the called procedures)
	// this is computed in the BoogieExceptionAnalysis (not a good style, but no
	// need to waste time here)
	private final Set<Variable> mModifiesGlobals;

	// Procedure contracts
	private final List<Expression> mRequires;
	private final List<Expression> mEnsures;

	private final Set<Variable> tmpLocals;

	private final boolean mIsPure;
	private final LocationTag mLocationTag;
	private final String mSignatureString;

	private final BasicBlock mExitBlock;
	private final String mProcedureName;

	private final Variable mThisVariable;
	private final Variable mReturnVariable;

	private BasicBlock mRootBlock;

	private BoogieProcedure(final String procname, final Variable returnVar, final Variable thisVar,
			final boolean isPure, final List<Variable> parameterList, final LocationTag locationTag,
			final String signature, final BasicBlock rootAndExitBlock) {
		tmpLocals = new HashSet<Variable>();
		mRequires = new LinkedList<Expression>();
		mEnsures = new LinkedList<Expression>();
		mModifiesGlobals = new HashSet<Variable>();
		mParameterList = parameterList == null ? new LinkedList<Variable>() : parameterList;

		mCalledProcedures = new HashSet<BoogieProcedure>();
		mCallingProcedures = new HashSet<BoogieProcedure>();

		mVarIncarnationMap = new HashMap<Variable, LinkedList<Variable>>();
		mExceptionReturnExpressions = new HashMap<BoogieType, Expression>();
		mLocalVars = new HashSet<Variable>();

		mLocationTag = locationTag;
		mSignatureString = signature;
		mRootBlock = rootAndExitBlock;
		mExitBlock = rootAndExitBlock;

		mIsPure = isPure;
		mProcedureName = procname;
		mThisVariable = thisVar;
		mReturnVariable = returnVar;
	}

	/**
	 * This constructor is only used to create prelude functions. it takes an
	 * expression as input (e.g., IteExpression) and generates the list of
	 * parameters from the variables used in that expression. Then, it creates
	 * one block which has only one ExpressionStatement for this expression.
	 */
	public BoogieProcedure(String name, BoogieType rettype, Expression retexpression, String uid) {
		this(name, createReturnVar(rettype), null, true, null, null, "", new BasicBlock("root", uid));
		for (Variable v : retexpression.getUsedVariables()) {
			if (!mParameterList.contains(v))
				mParameterList.add(v);
		}
		mRootBlock.addStatement(new ExpressionStatement(retexpression));
	}

	public BoogieProcedure(String name, Variable retVar, LocationTag tag, String nameInSource,
			List<Variable> parameterList, Variable thisVar) {
		this(name, retVar, thisVar, false, parameterList, tag, nameInSource, null);
	}

	public BoogieProcedure(String name, BoogieType returnType, LocationTag tag, String nameInSource,
			LinkedList<BoogieType> parameterList2) {
		this(name, createReturnVar(returnType), new Variable("__this", BoogieBaseTypes.getRefType(), false), false,
				null, tag, nameInSource, null);
		int i = 0;
		for (BoogieType typ : parameterList2) {
			mParameterList.add(new Variable("param" + (i++), BoogieBaseTypes.getRefType(), false));
		}

	}

	// This constructor should only be called to create helper functions for
	// BinOps
	public BoogieProcedure(String name, BoogieType rettype, List<BoogieType> parameters, boolean ispure) {
		this(name, createReturnVar(rettype), null, ispure, null, null, "", null);
		int i = 0;
		for (BoogieType bt : parameters) {
			mParameterList.add(getFreshLocalVariable("$param" + String.valueOf(i++), bt));
		}
	}

	/**
	 * Constructs a new empty procedure. This constructor should be called to
	 * manually create empty procedures (originally for EFG).
	 * 
	 * @param name
	 *            the name of the procedure
	 * @param rettype
	 *            Return Type
	 * @param ispure
	 *            true if the procedure is declared as pure
	 * @param thisref
	 *            true if the procedure takes a "this" reference as parameter.
	 */
	public BoogieProcedure(String name, BoogieType rettype, boolean ispure, boolean thisref) {
		this(name, createReturnVar(rettype),
				thisref ? new Variable("__this", BoogieBaseTypes.getRefType(), false) : null, ispure, null, null, "",
				null);
	}

	public void addLocal(Variable v) {
		this.mLocalVars.add(v);
	}

	public Set<Variable> getLocalVars() {
		return mLocalVars;
	}

	/**
	 * @return the tmpLocals
	 */
	public Set<Variable> getTmpLocals() {
		return tmpLocals;
	}

	private static Variable createReturnVar(BoogieType rettype) {
		if (rettype == null) {
			return null;
		} else {
			return new Variable("__ret", rettype, false);
		}
	}

	public boolean isStatic() {
		return mThisVariable == null;
	}

	public String getName() {
		return this.mProcedureName;
	}

	public String getJavaName() {
		return this.mSignatureString;
	}

	public BasicBlock getRootBlock() {
		return mRootBlock;
	}

	public void setBodyRoot(BasicBlock root) {
		if (mRootBlock == null) {
			mRootBlock = root;
		} else {
			mRootBlock.connectToSuccessor(root);
		}
	}

	public Collection<Variable> getParameterList() {
		return mParameterList;
	}

	public BasicBlock getExitBlock() {
		return mExitBlock;
	}

	public Variable getReturnVariable() {
		return mReturnVariable;
	}

	public Variable getThisVariable() {
		return mThisVariable;
	}

	public Variable getFreshLocalVariable(String prefix, BoogieType t) {
		Variable v = new Variable(prefix + (this.tmpLocals.size()), t, false);
		this.tmpLocals.add(v);
		return v;
	}

	public Variable lookupParameter(Integer idx) {
		if (mParameterList.size() <= idx) {
			assert(false);
		}
		return mParameterList.get(idx);
	}

	// public Expression getExceptionalReturnVariables() {
	// return exceptionReturnExpressions.values();
	// }

	public Expression getExceptionalReturnVariable(BoogieType t) {
		if (mExceptionReturnExpressions.containsKey(t))
			return mExceptionReturnExpressions.get(t);
		return null;
	}

	// TODO: this must not be a set because the ordering is important when
	// generating the exception variables on the caller side.
	public Set<BoogieType> getUncaughtTypes() {
		return mExceptionReturnExpressions.keySet();
	}

	public void addExceptionalReturnVariable(BoogieType t, Expression v) {
		mExceptionReturnExpressions.put(t, v);
	}

	public String toBoogie() {
		StringBuilder sb = new StringBuilder();

		if (mLocationTag != null) {
			sb.append(mLocationTag);
			sb.append("// " + mSignatureString + "\n");
		} else {
			sb.append("// procedure is generated by joogie.\n");
		}

		if (isPure()) {
			sb.append("function {:inline true} ");
		} else {
			sb.append("procedure ");
		}
		sb.append(mProcedureName + "(");

		boolean firstround = true;

		// If the method is not static, add a this variable to the list of
		// parameters
		if (mThisVariable != null) {
			sb.append(mThisVariable.toBoogie());
			sb.append(" : ");
			sb.append(mThisVariable.getType().toBoogie());
			firstround = false;
		}

		for (int i = 0; i < mParameterList.size(); i++) {
			if (firstround) {
				firstround = false;
			} else {
				sb.append(", ");
			}
			Variable v = mParameterList.get(i);
			sb.append(v.toBoogie());
			sb.append(" : ");
			sb.append(v.getType().toBoogie());
		}
		sb.append(")");
		if (mReturnVariable != null || mExceptionReturnExpressions.size() > 0) {
			sb.append(" returns (");
		}

		firstround = true;
		if (mReturnVariable != null) {
			sb.append(mReturnVariable.toBoogie());
			sb.append(" : ");
			sb.append(mReturnVariable.getType().toBoogie());
			firstround = false;
		}
		for (Entry<BoogieType, Expression> en : mExceptionReturnExpressions.entrySet()) {
			if (!firstround) {
				sb.append(", ");
			} else {
				firstround = false;
			}
			sb.append(en.getValue().toBoogie());
			sb.append(" : ");
			sb.append(en.getKey().toBoogie());
		}
		if (mReturnVariable != null || mExceptionReturnExpressions.size() > 0) {
			sb.append(")");
		}

		if (!isPure()) {

			if (this.getModifiesGlobals().size() > 0) {
				sb.append("\n  modifies ");

				firstround = true;
				for (Variable v : this.getModifiesGlobals()) {
					if (!firstround) {
						sb.append(", ");
					} else
						firstround = false;
					sb.append(v.toBoogie());
				}
				sb.append(";\n");
			}
		}

		if (this.mRootBlock != null) {
			if (!mRequires.isEmpty()) {
				for (Expression e : mRequires) {
					if (e instanceof BinOpExpression)
						sb.append("  requires (" + e.toBoogie() + ");\n");
					else
						sb.append("  requires (" + e.toBoogie() + "==1);\n");
				}
			}

			if (!mEnsures.isEmpty()) {
				for (Expression e : mEnsures) {
					if (e instanceof BinOpExpression)
						sb.append("  ensures (" + e.toBoogie() + ");\n");
					else
						sb.append("  ensures (" + e.toBoogie() + "==1);\n");
				}
			}
		}

		if (this.mRootBlock == null) {
			sb.append(";\n\n");
			return sb.toString();
		}

		sb.append(" {\n");

		for (Variable v : mLocalVars) {
			sb.append("var ");
			sb.append(v.toBoogie());
			sb.append(" : ");
			sb.append(v.getType().toBoogie());
			sb.append(";\n");
		}

		if (this.tmpLocals.size() > 0) {
			sb.append("\n //temp local variables \n");
			for (Variable v : this.tmpLocals) {
				boolean alreadyDeclared = false;
				for (Expression e : mExceptionReturnExpressions.values()) {
					if (e instanceof Variable && ((Variable) e).toBoogie().equals(v.toBoogie())) {
						alreadyDeclared = true;
						break;
					}
				}
				if (alreadyDeclared)
					continue; // do not declare local variables that are also
								// return vars
				sb.append("var ");
				sb.append(v.toBoogie());
				sb.append(" : ");
				sb.append(v.getType().toBoogie());
				sb.append(";\n");
			}
			sb.append("\n");
		}

		/*
		 * TODO: it is not very nice to distinguish between pure and none pure
		 * functions here. However, it is necessary, as for pure functions,
		 * Boogie does not allow block labels, and the ExpressionStatement must
		 * not be terminated with a semicolon. This problem occurs because of
		 * many hacks we did so far and can only be fixed by a major
		 * re-engineering... this may be done later, when we replace soot by
		 * something else.
		 */
		if (this.mIsPure) {
			if (mRootBlock != null) {
				List<Statement> stmts = mRootBlock.getStatements();
				if (stmts.size() == 1) { // There should be only one
											// ExpressionStatement in a pure
											// function
					sb.append(stmts.get(0).toBoogie());
					sb.append("\n");
				}
			}
		} else {
			if (mRootBlock != null) {
				LinkedList<BasicBlock> todo = new LinkedList<BasicBlock>();
				LinkedList<BasicBlock> done = new LinkedList<BasicBlock>();
				todo.add(mRootBlock);
				BasicBlock current = null;
				while (!todo.isEmpty()) {
					current = todo.pollFirst();

					done.add(current);
					sb.append(current.toBoogie());
					for (BasicBlock suc : current.getSuccessors()) {
						if (!todo.contains(suc) && !done.contains(suc)) {
							todo.addLast(suc);
						}
					}
				}
			}
		}
		sb.append("}\n");
		return sb.toString();
	}

	public boolean isPure() {
		return mIsPure;
	}

	@Override
	public String toString() {
		return this.mProcedureName;
	}

	public void renameParametersForInlining() {
		for (Variable p : mParameterList) {
			p.setName(this.getName() + p.getName());
		}
		mThisVariable.setName(this.getName() + "$" + mThisVariable.getName());
		for (Variable v : tmpLocals) {
			v.setName(this.getName() + v.getName());
		}
	}

	public void addRequires(Expression e) {
		mRequires.add(e);
	}

	public void addEnsures(Expression e) {
		mEnsures.add(e);
	}

	public List<Expression> getRequires() {
		return mRequires;
	}

	public List<Expression> getEnsures() {
		return mEnsures;
	}

	public Map<Variable, LinkedList<Variable>> getVarIncarnationMap() {
		return mVarIncarnationMap;
	}

	public Map<BoogieType, Expression> getExceptionalReturnVariables() {
		return mExceptionReturnExpressions;
	}

	public void pruneUnreachable() {
		BasicBlock root = this.getRootBlock();
		Stack<BasicBlock> todo = new Stack<BasicBlock>();
		HashSet<BasicBlock> done = new HashSet<BasicBlock>();
		if (root != null)
			todo.push(root);
		// first collect all forward reachable nodes in "done"
		while (!todo.empty()) {
			BasicBlock current = todo.pop();
			done.add(current);
			for (BasicBlock suc : current.getSuccessors()) {
				if (!done.contains(suc) && !todo.contains(suc) && suc != null) {
					todo.add(suc);
				}
			}
		}

		for (BasicBlock b : done) {
			HashSet<BasicBlock> newPre = new HashSet<BasicBlock>();
			for (BasicBlock pre : b.getPredecessors()) {
				if (done.contains(pre))
					newPre.add(pre);
			}
			b.getPredecessors().clear();
			b.getPredecessors().addAll(newPre);
		}
	}

	public Set<BoogieProcedure> getCalledProcedures() {
		return mCalledProcedures;
	}

	public Set<BoogieProcedure> getCallingProcedures() {
		return mCallingProcedures;
	}

	public Set<Variable> getModifiesGlobals() {
		return mModifiesGlobals;
	}

	public LocationTag getLocationTag() {
		return mLocationTag;
	}
}
