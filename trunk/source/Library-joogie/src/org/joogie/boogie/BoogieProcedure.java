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

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
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
	public HashSet<BoogieProcedure> calledProcedures = new HashSet<BoogieProcedure>();
	// Call graph predecessors
	public HashSet<BoogieProcedure> callingProcedures = new HashSet<BoogieProcedure>();

	// TODO: this should be refactored to somewhere else
	// SSA should not write fields within the procedure
	// better create a wrapper around the procedure
	private HashMap<Variable, LinkedList<Variable>> varIncarnationMap = new HashMap<Variable, LinkedList<Variable>>();

	private BasicBlock rootBlock = null;
	private BasicBlock exitBlock = null;
	private String procedureName = "";

	private Variable thisVariable = null;

	private HashSet<Variable> localVars = new HashSet<Variable>();

	private Variable returnVariable = null;
	// The exceptions that can be returned by this procedure
	private HashMap<BoogieType, Expression> exceptionReturnExpressions = new HashMap<BoogieType, Expression>();

	public void addLocal(Variable v) {
		this.localVars.add(v);
	}

	/**
	 * @return the localMap
	 */
	private HashSet<Variable> tmpLocals = new HashSet<Variable>();

	/**
	 * @return the tmpLocals
	 */
	public Set<Variable> getTmpLocals() {
		return tmpLocals;
	}

	private LinkedList<Variable> parameterList = new LinkedList<Variable>();

	// The set of all globals modified in the body (including the ones modified
	// by the called procedures)
	// this is computed in the BoogieExceptionAnalysis (not a good style, but no
	// need to waste time here)
	public HashSet<Variable> modifiesGlobals = new HashSet<Variable>();

	private boolean isPure = false;
	private LocationTag locationTag = null;
	private String signatureString = "";

	// Procedure contracts
	private List<Expression> requires = new LinkedList<Expression>();
	private List<Expression> ensures = new LinkedList<Expression>();

	private void createReturnVar(BoogieType rettype) {
		// only create it once
		if (returnVariable != null)
			return;
		if (rettype == null) {
			returnVariable = null;
		} else {
			returnVariable = new Variable("__ret", rettype, false);
		}
	}

	// This constructor should only be called to create helper functions for
	// BinOps
	public BoogieProcedure(String name, BoogieType rettype, List<BoogieType> parameters, boolean ispure) {
		procedureName = name;
		createReturnVar(rettype);
		Integer i = 0;
		for (BoogieType bt : parameters) {
			parameterList.add(getFreshLocalVariable("$param" + (i++).toString(), bt));
		}
		thisVariable = null;
		this.isPure = ispure;
	}

	/*
	 * This constructor is only used to create prelude functions. it takes an
	 * expression as input (e.g., IteExpression) and generates the list of
	 * parameters from the variables used in that expression. Then, it creates
	 * one block which has only one ExpressionStatement for this expression.
	 */
	public BoogieProcedure(String name, BoogieType rettype, Expression retexpression) {
		procedureName = name;
		createReturnVar(rettype);
		this.isPure = true;
		for (Variable v : retexpression.getUsedVariables()) {
			if (!parameterList.contains(v))
				parameterList.add(v);
		}
		this.rootBlock = new BasicBlock("root");
		this.rootBlock.addStatement(new ExpressionStatement(retexpression));
		this.exitBlock = this.rootBlock;
		thisVariable = null;
	}

	// This constructor should be called to manually create empty procedures
	// (originally for EFG)
	/**
	 * Constructs a new empty procedure
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
		procedureName = name;
		createReturnVar(rettype);

		if (thisref)
			thisVariable = new Variable("__this", BoogieBaseTypes.getRefType(), false);
		this.isPure = ispure;
	}

	public BoogieProcedure(String procName, Variable retVar, LocationTag tag, String nameInSource,
			LinkedList<Variable> parameterList2, Variable thisVariable2) {
		this.procedureName = procName;
		this.returnVariable = retVar;
		this.locationTag = tag;
		this.signatureString = nameInSource;
		this.parameterList = parameterList2;
		this.thisVariable = thisVariable2;
	}

	public BoogieProcedure(String procName, BoogieType t, LocationTag tag, String nameInSource,
			LinkedList<BoogieType> parameterList2) {
		this.procedureName = procName;
		createReturnVar(t);
		this.locationTag = tag;
		this.signatureString = nameInSource;
		this.parameterList = new LinkedList<Variable>();
		int i = 0;
		for (BoogieType typ : parameterList2) {
			this.parameterList.add(new Variable("param" + (i++), BoogieBaseTypes.getRefType(), false));
		}

		thisVariable = new Variable("__this", BoogieBaseTypes.getRefType(), false);
	}

	public boolean isStatic() {
		return thisVariable == null;
	}

	public String getName() {
		return this.procedureName;
	}

	public String getJavaName() {
		return this.signatureString;
	}

	public void setJavaName(String s) {
		this.signatureString = s;
	}

	public BasicBlock getRootBlock() {
		return rootBlock;
	}

	public void setBodyRoot(BasicBlock root) {
		if (rootBlock == null) {
			rootBlock = root;
		} else {
			rootBlock.connectToSuccessor(root);
		}
	}

	public List<Variable> getParameterList() {
		return this.parameterList;
	}

	public BasicBlock getExitBlock() {
		return exitBlock;
	}

	public void setExitBlock(BasicBlock exit) {
		exitBlock = exit;
	}

	public Variable getReturnVariable() {
		return returnVariable;
	}

	public Variable getThisVariable() {
		if (thisVariable == null) {
			assert(false);
		}
		return thisVariable;
	}

	public Variable getFreshLocalVariable(String prefix, BoogieType t) {
		Variable v = new Variable(prefix + (this.tmpLocals.size()), t, false);
		this.tmpLocals.add(v);
		return v;
	}

	public Variable lookupParameter(Integer idx) {
		if (parameterList.size() <= idx) {
			assert(false);
		}
		return parameterList.get(idx);
	}

	// public Expression getExceptionalReturnVariables() {
	// return exceptionReturnExpressions.values();
	// }

	public Expression getExceptionalReturnVariable(BoogieType t) {
		if (exceptionReturnExpressions.containsKey(t))
			return exceptionReturnExpressions.get(t);
		return null;
	}

	// TODO: this must not be a set because the ordering is important when
	// generating the exception variables on the caller side.
	public Set<BoogieType> getUncaughtTypes() {
		return exceptionReturnExpressions.keySet();
	}

	public void addExceptionalReturnVariable(BoogieType t, Expression v) {
		exceptionReturnExpressions.put(t, v);
	}

	public String toBoogie() {
		StringBuilder sb = new StringBuilder();

		if (locationTag != null) {
			sb.append(locationTag);
			sb.append("// " + signatureString + "\n");
		} else {
			sb.append("// procedure is generated by joogie.\n");
		}

		if (isPure()) {
			sb.append("function {:inline true} ");
		} else {
			sb.append("procedure ");
		}
		sb.append(procedureName + "(");

		boolean firstround = true;

		// If the method is not static, add a this variable to the list of
		// parameters
		if (thisVariable != null) {
			sb.append(thisVariable.toBoogie());
			sb.append(" : ");
			sb.append(thisVariable.getType().toBoogie());
			firstround = false;
		}

		for (int i = 0; i < parameterList.size(); i++) {
			if (firstround) {
				firstround = false;
			} else {
				sb.append(", ");
			}
			Variable v = parameterList.get(i);
			sb.append(v.toBoogie());
			sb.append(" : ");
			sb.append(v.getType().toBoogie());
		}
		sb.append(")");
		if (returnVariable != null || exceptionReturnExpressions.size() > 0) {
			sb.append(" returns (");
		}

		firstround = true;
		if (returnVariable != null) {
			sb.append(returnVariable.toBoogie());
			sb.append(" : ");
			sb.append(returnVariable.getType().toBoogie());
			firstround = false;
		}
		for (Entry<BoogieType, Expression> en : exceptionReturnExpressions.entrySet()) {
			if (!firstround) {
				sb.append(", ");
			} else {
				firstround = false;
			}
			sb.append(en.getValue().toBoogie());
			sb.append(" : ");
			sb.append(en.getKey().toBoogie());
		}
		if (returnVariable != null || exceptionReturnExpressions.size() > 0) {
			sb.append(")");
		}

		if (!isPure()) {

			if (this.modifiesGlobals.size() > 0) {
				sb.append("\n  modifies ");

				firstround = true;
				for (Variable v : this.modifiesGlobals) {
					if (!firstround) {
						sb.append(", ");
					} else
						firstround = false;
					sb.append(v.toBoogie());
				}
				sb.append(";\n");
			}
		}

		if (this.rootBlock != null) {
			if (!requires.isEmpty()) {
				for (Expression e : requires) {
					if (e instanceof BinOpExpression)
						sb.append("  requires (" + e.toBoogie() + ");\n");
					else
						sb.append("  requires (" + e.toBoogie() + "==1);\n");
				}
			}

			if (!ensures.isEmpty()) {
				for (Expression e : ensures) {
					if (e instanceof BinOpExpression)
						sb.append("  ensures (" + e.toBoogie() + ");\n");
					else
						sb.append("  ensures (" + e.toBoogie() + "==1);\n");
				}
			}
		}

		if (this.rootBlock == null) {
			sb.append(";\n\n");
			return sb.toString();
		}

		sb.append(" {\n");

		for (Variable v : localVars) {
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
				for (Expression e : exceptionReturnExpressions.values()) {
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
		if (this.isPure) {
			if (rootBlock != null) {
				List<Statement> stmts = rootBlock.getStatements();
				if (stmts.size() == 1) { // There should be only one
											// ExpressionStatement in a pure
											// function
					sb.append(stmts.get(0).toBoogie());
					sb.append("\n");
				}
			}
		} else {
			if (rootBlock != null) {
				LinkedList<BasicBlock> todo = new LinkedList<BasicBlock>();
				LinkedList<BasicBlock> done = new LinkedList<BasicBlock>();
				todo.add(rootBlock);
				BasicBlock current = null;
				while (!todo.isEmpty()) {
					current = todo.pollFirst();

					done.add(current);
					sb.append(current.toBoogie());
					for (BasicBlock suc : current.Successors) {
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
		return isPure;
	}

	@Override
	public String toString() {
		return this.procedureName;
	}

	public void renameParametersForInlining() {
		for (Variable p : parameterList) {
			p.setName(this.getName() + p.getName());
		}
		thisVariable.setName(this.getName() + "$" + thisVariable.getName());
		for (Variable v : tmpLocals) {
			v.setName(this.getName() + v.getName());
		}
	}

	public void addRequires(Expression e) {
		requires.add(e);
	}

	public void addEnsures(Expression e) {
		ensures.add(e);
	}

	public List<Expression> getRequires() {
		return requires;
	}

	public List<Expression> getEnsures() {
		return ensures;
	}

	// TODO: this map is a hack
	// I only put it here to get the experiments implemented
	// more quickly.
	public HashMap<BasicBlock, Variable> vstteMap = null;

	public HashMap<Variable, LinkedList<Variable>> getVarIncarnationMap() {
		return varIncarnationMap;
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
			for (BasicBlock suc : current.Successors) {
				if (!done.contains(suc) && !todo.contains(suc) && suc != null) {
					todo.add(suc);
				}
			}
		}

		for (BasicBlock b : done) {
			HashSet<BasicBlock> newPre = new HashSet<BasicBlock>();
			for (BasicBlock pre : b.Predecessors) {
				if (done.contains(pre))
					newPre.add(pre);
			}
			b.Predecessors = newPre;
		}
	}

}
