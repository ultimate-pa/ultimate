/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 * Base class to recursively walk through a Boogie tree, doing transformations. This class changes nothing, but
 * inherited classes may override some of the provided functions. This class will then propagate the changes.
 *
 * The boogie declaration is currently read-only, so all changes have to be returned in new objects. Therefore each of
 * this function takes a Boogie-AST-node and returns the same type. If the return value for the children do not change
 * the default methods will return the same value again, so that no new objects are created.
 *
 * As an example usage see de.uni_freiburg.informatik.ultimate.boogie.preprocessor.FunctionInliner. Note that the
 * underlying ITypes are not changed by the default implementation. You either need preserve types, run this before type
 * checking, or take care of updating the types yourself.
 *
 * @author Jochen Hoenicke
 */
public abstract class BoogieTransformer {

	/**
	 * Process a declaration (including its children).
	 *
	 * @param decl
	 *            the declaration to process.
	 * @return the processed declaration.
	 */
	protected Declaration processDeclaration(final Declaration decl) {
		final Attribute[] attrs = decl.getAttributes();
		final Attribute[] newAttrs = processAttributes(attrs);
		Declaration newDecl = null;
		if (decl instanceof TypeDeclaration) {
			final TypeDeclaration tdecl = (TypeDeclaration) decl;
			final ASTType syntype = tdecl.getSynonym();
			final ASTType newSyntype = syntype != null ? processType(syntype) : null;
			if (newAttrs != attrs || newSyntype != syntype) {
				newDecl = new TypeDeclaration(tdecl.getLocation(), newAttrs, tdecl.isFinite(), tdecl.getIdentifier(),
						tdecl.getTypeParams(), newSyntype);
			}
		} else if (decl instanceof ConstDeclaration) {
			final ConstDeclaration cdecl = (ConstDeclaration) decl;
			final VarList varList = cdecl.getVarList();
			final VarList newVarList = processVarList(varList);
			if (newAttrs != attrs || newVarList != varList) {
				newDecl = new ConstDeclaration(cdecl.getLocation(), newAttrs, cdecl.isUnique(), newVarList,
						cdecl.getParentInfo(), cdecl.isComplete());
			}
		} else if (decl instanceof FunctionDeclaration) {
			final FunctionDeclaration fdecl = (FunctionDeclaration) decl;
			final VarList[] ins = fdecl.getInParams();
			final VarList[] newIns = processVarLists(ins);
			final VarList out = fdecl.getOutParam();
			final VarList newOut = processVarList(out);
			final Expression body = fdecl.getBody();
			final Expression newBody = body != null ? processExpression(body) : null;
			if (newIns != ins || newOut != out || newBody != body || newAttrs != attrs) {
				newDecl = new FunctionDeclaration(fdecl.getLocation(), newAttrs, fdecl.getIdentifier(),
						fdecl.getTypeParams(), newIns, newOut, newBody);
			}
		} else if (decl instanceof Axiom) {
			final Expression ax = ((Axiom) decl).getFormula();
			final Expression newAx = processExpression(ax);
			if (ax != newAx || attrs != newAttrs) {
				newDecl = new Axiom(decl.getLocation(), newAttrs, newAx);
			}
		} else if (decl instanceof Procedure) {
			final Procedure proc = (Procedure) decl;
			final VarList[] ins = proc.getInParams();
			final VarList[] newIns = processVarLists(ins);
			final VarList[] outs = proc.getOutParams();
			final VarList[] newOuts = processVarLists(outs);
			final Specification[] specs = proc.getSpecification();
			final Specification[] newSpecs = specs != null ? processSpecifications(specs) : null;
			final Body body = proc.getBody();
			final Body newBody = body != null ? processBody(body) : null;
			if (newAttrs != attrs || newBody != body || newSpecs != specs || newIns != ins || newOuts != outs) {
				newDecl = new Procedure(proc.getLocation(), newAttrs, proc.getIdentifier(), proc.getTypeParams(),
						newIns, newOuts, newSpecs, newBody);
			}
		} else if (decl instanceof VariableDeclaration) {
			final VarList[] vls = ((VariableDeclaration) decl).getVariables();
			final VarList[] newVls = processVarLists(vls);
			if (attrs != newAttrs || vls != newVls) {
				newDecl = new VariableDeclaration(decl.getLocation(), newAttrs, newVls);
			}
		}

		if (newDecl == null) {
			return decl;
		}
		ModelUtils.copyAnnotations(decl, newDecl);
		return newDecl;
	}

	/**
	 * Process an array of AST type. This implementation calls processType on all elements
	 *
	 * @param types
	 *            the types to process.
	 * @return the processed types.
	 */
	protected ASTType[] processTypes(final ASTType[] types) {
		boolean changed = false;
		final ASTType[] newTypes = new ASTType[types.length];
		for (int i = 0; i < types.length; i++) {
			newTypes[i] = processType(types[i]);
			if (newTypes[i] != types[i]) {
				changed = true;
			}
		}
		return changed ? newTypes : types;
	}

	/**
	 * Process a AST type. This implementation recurses on the sub types.
	 *
	 * @param type
	 *            the type to process.
	 * @return the processed type.
	 */
	protected ASTType processType(final ASTType type) {
		ASTType newType = null;
		if (type instanceof ArrayType) {
			final ArrayType arrtype = (ArrayType) type;
			final ASTType[] indexTypes = arrtype.getIndexTypes();
			final ASTType valueType = arrtype.getValueType();
			final ASTType[] newIndexTypes = processTypes(indexTypes);
			final ASTType newValueType = processType(valueType);
			if (newIndexTypes != indexTypes || newValueType != valueType) {
				newType = new ArrayType(arrtype.getLocation(), arrtype.getBoogieType(), arrtype.getTypeParams(),
						newIndexTypes, newValueType);
			}
		} else if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			final ASTType[] argTypes = ntype.getTypeArgs();
			final ASTType[] newArgTypes = processTypes(argTypes);
			if (newArgTypes != argTypes) {
				newType = new NamedType(ntype.getLocation(), ntype.getBoogieType(), ntype.getName(), newArgTypes);
			}
		}
		if (newType == null) {
			return type;
		}
		ModelUtils.copyAnnotations(type, newType);
		return newType;
	}

	/**
	 * Process an array of variable list as it appears in function- and variable-specifications. This implementation
	 * calls processVarList on all elements.
	 *
	 * @param vls
	 *            the variable lists
	 * @return the processed variable lists.
	 */
	protected VarList[] processVarLists(final VarList[] vls) {
		boolean changed = false;
		final VarList[] newVls = new VarList[vls.length];
		for (int i = 0; i < vls.length; i++) {
			newVls[i] = processVarList(vls[i]);
			if (newVls[i] != vls[i]) {
				changed = true;
			}
		}
		return changed ? newVls : vls;
	}

	/**
	 * Process a variable list as it appears in function- and variable-specifications. This implementation processes the
	 * where clause and the type.
	 *
	 * @param vl
	 *            the variable list
	 * @return the processed variable list.
	 */
	protected VarList processVarList(final VarList vl) {
		final ASTType type = vl.getType();
		final ASTType newType = processType(type);
		final Expression where = vl.getWhereClause();
		final Expression newWhere = where != null ? processExpression(where) : null;
		if (newType != type || newWhere != where) {
			final VarList newVl = new VarList(vl.getLocation(), vl.getIdentifiers(), newType, newWhere);
			ModelUtils.copyAnnotations(vl, newVl);
			return newVl;
		}
		return vl;
	}

	/**
	 * Process the body of an implementation. Processes the contained variable declarations and statements.
	 *
	 * @param body
	 *            the implementation body.
	 * @return the processed body.
	 */
	protected Body processBody(final Body body) {
		final VariableDeclaration[] locals = body.getLocalVars();
		final VariableDeclaration[] newLocals = processLocalVariableDeclarations(locals);

		final Statement[] statements = body.getBlock();
		final Statement[] newStatements = processStatements(statements);
		if (newLocals != locals || newStatements != statements) {
			final Body newBody = new Body(body.getLocation(), newLocals, newStatements);
			ModelUtils.copyAnnotations(body, newBody);
			return newBody;
		}
		return body;
	}

	/**
	 * Process a local variable declaration. Global declarations are processed by processDeclaration.
	 *
	 * @param local
	 *            The local variable declaration.
	 * @return the processed declaration.
	 */
	protected VariableDeclaration processLocalVariableDeclaration(final VariableDeclaration local) {
		final Attribute[] attrs = local.getAttributes();
		final Attribute[] newAttrs = processAttributes(attrs);
		final VarList[] vl = local.getVariables();
		final VarList[] newVl = processVarLists(vl);
		if (vl != newVl || attrs != newAttrs) {
			final VariableDeclaration newLocal = new VariableDeclaration(local.getLocation(), newAttrs, newVl);
			ModelUtils.copyAnnotations(local, newLocal);
			return newLocal;
		}
		return local;
	}

	/**
	 * Process array of local variable declarations. This is called for implementations.
	 *
	 * @param locals
	 *            the array of variable declarations
	 * @return the processed declarations.
	 */
	protected VariableDeclaration[] processLocalVariableDeclarations(final VariableDeclaration[] locals) {
		boolean changed = false;
		final VariableDeclaration[] newLocals = new VariableDeclaration[locals.length];
		for (int i = 0; i < locals.length; i++) {
			newLocals[i] = processLocalVariableDeclaration(locals[i]);
			if (newLocals[i] != locals[i]) {
				changed = true;
			}
		}
		return changed ? newLocals : locals;
	}

	/**
	 * Process the statements. Calls processStatement for all statements in the array.
	 *
	 * @param statements
	 *            the statement to process.
	 * @return processed statements.
	 */
	protected Statement[] processStatements(final Statement[] statements) {
		boolean changed = false;
		final Statement[] newStatements = new Statement[statements.length];
		for (int i = 0; i < statements.length; i++) {
			newStatements[i] = processStatement(statements[i]);
			if (newStatements[i] != statements[i]) {
				changed = true;
			}
		}
		return changed ? newStatements : statements;
	}

	/**
	 * Process the statement. Calls processExpression for all contained expressions and recurses for while and if
	 * statements.
	 *
	 * @param statement
	 *            the statement to process.
	 * @return processed statement.
	 */
	protected Statement processStatement(final Statement statement) {
		Statement newStatement = null;
		if (statement instanceof AssertStatement) {
			final AssertStatement assertStmt = (AssertStatement) statement;
			final Expression expr = assertStmt.getFormula();
			final Expression newExpr = processExpression(expr);
			final Attribute[] newAttr = processAttributes(assertStmt.getAttributes());
			if (expr != newExpr || assertStmt.getAttributes() != newAttr) {
				newStatement = new AssertStatement(statement.getLocation(), (NamedAttribute[]) newAttr, newExpr);
			}
		} else if (statement instanceof AssignmentStatement) {
			final AssignmentStatement assign = (AssignmentStatement) statement;
			final LeftHandSide[] lhs = assign.getLhs();
			final LeftHandSide[] newLhs = processLeftHandSides(lhs);
			final Expression[] rhs = assign.getRhs();
			final Expression[] newRhs = processExpressions(rhs);
			if (lhs != newLhs || rhs != newRhs) {
				newStatement = new AssignmentStatement(statement.getLocation(), newLhs, newRhs);
			}
		} else if (statement instanceof AssumeStatement) {
			final AssumeStatement assumeStmt = (AssumeStatement) statement;
			final Expression expr = ((AssumeStatement) statement).getFormula();
			final Expression newExpr = processExpression(expr);
			final Attribute[] newAttr = processAttributes(assumeStmt.getAttributes());
			if (expr != newExpr || assumeStmt.getAttributes() != newAttr) {
				newStatement = new AssumeStatement(statement.getLocation(), (NamedAttribute[]) newAttr, newExpr);
			}
		} else if (statement instanceof HavocStatement) {
			final HavocStatement havoc = (HavocStatement) statement;
			final VariableLHS[] ids = havoc.getIdentifiers();
			final VariableLHS[] newIds = processVariableLHSs(ids);
			if (ids != newIds) {
				newStatement = new HavocStatement(havoc.getLocation(), newIds);
			}
		} else if (statement instanceof CallStatement) {
			final CallStatement call = (CallStatement) statement;
			final Expression[] args = call.getArguments();
			final Expression[] newArgs = processExpressions(args);
			final VariableLHS[] lhs = call.getLhs();
			final VariableLHS[] newLhs = processVariableLHSs(lhs);
			final Attribute[] newAttr = processAttributes(call.getAttributes());
			if (args != newArgs || lhs != newLhs || newAttr != call.getAttributes()) {
				newStatement = new CallStatement(call.getLocation(), (NamedAttribute[]) newAttr, call.isForall(),
						newLhs, call.getMethodName(), newArgs);
			}
		} else if (statement instanceof IfStatement) {
			final IfStatement ifstmt = (IfStatement) statement;
			final Expression cond = ifstmt.getCondition();
			final Expression newCond = processExpression(cond);
			final Statement[] thens = ifstmt.getThenPart();
			final Statement[] newThens = processStatements(thens);
			final Statement[] elses = ifstmt.getElsePart();
			final Statement[] newElses = processStatements(elses);
			if (newCond != cond || newThens != thens || newElses != elses) {
				newStatement = new IfStatement(ifstmt.getLocation(), newCond, newThens, newElses);
			}
		} else if (statement instanceof WhileStatement) {
			final WhileStatement whilestmt = (WhileStatement) statement;
			final Expression cond = whilestmt.getCondition();
			final Expression newCond = processExpression(cond);
			final LoopInvariantSpecification[] invs = whilestmt.getInvariants();
			final LoopInvariantSpecification[] newInvs = processLoopSpecifications(invs);
			final Statement[] body = whilestmt.getBody();
			final Statement[] newBody = processStatements(body);
			if (newCond != cond || newInvs != invs || newBody != body) {
				newStatement = new WhileStatement(whilestmt.getLocation(), newCond, newInvs, newBody);
			}
		} else if (statement instanceof ForkStatement) {
			final ForkStatement forkstmt = (ForkStatement) statement;
			final Expression[] threadId = forkstmt.getThreadID();
			final String procName = forkstmt.getProcedureName();
			final Expression[] arguments = forkstmt.getArguments();
			final Expression[] newThreadId = processExpressions(threadId);
			final Expression[] newArguments = processExpressions(arguments);
			if (newThreadId != threadId || newArguments != arguments) {
				newStatement = new ForkStatement(forkstmt.getLoc(), newThreadId, procName, newArguments);
			}
		} else if (statement instanceof JoinStatement) {
			final JoinStatement joinstmt = (JoinStatement) statement;
			final Expression[] threadId = joinstmt.getThreadID();
			final VariableLHS[] lhs = joinstmt.getLhs();
			final Expression[] newThreadId = processExpressions(threadId);
			final VariableLHS[] newLhs = processVariableLHSs(lhs);
			if (newThreadId != threadId || newLhs != lhs) {
				newStatement = new JoinStatement(joinstmt.getLoc(), newThreadId, newLhs);
			}
		} else if (statement instanceof AtomicStatement) {
			final AtomicStatement atomicstmt = (AtomicStatement) statement;
			final Statement[] body = atomicstmt.getBody();
			final Statement[] newBody = processStatements(body);
			if (newBody != body) {
				newStatement = new AtomicStatement(atomicstmt.getLocation(), newBody);
			}
		}
		if (newStatement == null) {
			/* No recursion for label, havoc, break, return and goto */
			return statement;
		}
		ModelUtils.copyAnnotations(statement, newStatement);
		return newStatement;
	}

	/**
	 * Process the loop invariant specifications. Calls processExpression for all loop invariants.
	 *
	 * @param specs
	 *            the invariant specifications to process.
	 * @return processed specifications.
	 */
	protected LoopInvariantSpecification[] processLoopSpecifications(final LoopInvariantSpecification[] specs) {
		boolean changed = false;
		final LoopInvariantSpecification[] newSpecs = new LoopInvariantSpecification[specs.length];
		for (int i = 0; i < newSpecs.length; i++) {
			final Expression expr = specs[i].getFormula();
			final Expression newExpr = processExpression(expr);
			if (expr != newExpr) {
				changed = true;
				newSpecs[i] = new LoopInvariantSpecification(specs[i].getLocation(), specs[i].isFree(), newExpr);
				ModelUtils.copyAnnotations(specs[i], newSpecs[i]);
			} else {
				newSpecs[i] = specs[i];
			}
		}
		return changed ? newSpecs : specs;
	}

	/**
	 * Process a left hand side (of an assignement). Recurses for array left hand side and calls processExpression for
	 * all contained expressions.
	 *
	 * @param lhs
	 *            the left hand side to process.
	 * @return processed left hand side.
	 */
	protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
		if (lhs instanceof ArrayLHS) {
			final ArrayLHS alhs = (ArrayLHS) lhs;
			final LeftHandSide array = alhs.getArray();
			final LeftHandSide newArray = processLeftHandSide(array);
			final Expression[] indices = alhs.getIndices();
			final Expression[] newIndices = processExpressions(indices);
			if (array != newArray || indices != newIndices) {
				final LeftHandSide newLhs = new ArrayLHS(lhs.getLocation(), alhs.getType(), newArray, newIndices);
				ModelUtils.copyAnnotations(lhs, newLhs);
				return newLhs;
			}
		} else if (lhs instanceof StructLHS) {
			final StructLHS slhs = (StructLHS) lhs;
			final LeftHandSide struct = slhs.getStruct();
			final LeftHandSide newStruct = processLeftHandSide(struct);
			if (newStruct != struct) {
				return new StructLHS(lhs.getLocation(), slhs.getType(), newStruct, slhs.getField());
			}
		}
		return lhs;
	}

	/**
	 * Process the left hand sides (of an assignment). Calls processLeftHandSide for each element in the array.
	 *
	 * @param lhs
	 *            the left hand sides to process.
	 * @return processed left hand sides.
	 */
	protected LeftHandSide[] processLeftHandSides(final LeftHandSide[] lhs) {
		boolean changed = false;
		final LeftHandSide[] newLhs = new LeftHandSide[lhs.length];
		for (int i = 0; i < newLhs.length; i++) {
			newLhs[i] = processLeftHandSide(lhs[i]);
			if (newLhs[i] != lhs[i]) {
				changed = true;
			}
		}
		return changed ? newLhs : lhs;
	}

	/**
	 * Process the left hand sides (of a call or havoc, or modifies specification). Default implementation calls
	 * processLeftHandSides and casts back to VariableLHS.
	 *
	 * @param lhs
	 *            the left hand sides to process.
	 * @return processed left hand sides.
	 */
	protected VariableLHS[] processVariableLHSs(final VariableLHS[] lhs) {
		final LeftHandSide[] newLhs = processLeftHandSides(lhs);
		if (newLhs == lhs) {
			return lhs;
		}
		final VariableLHS[] nnewLhs = new VariableLHS[newLhs.length];
		System.arraycopy(newLhs, 0, nnewLhs, 0, newLhs.length);
		return nnewLhs;
	}

	/**
	 * Process a procedure specification. Recursively calls processExpression for ensures and requires specifications.
	 * This must not be called for LoopInvariantSpecifications.
	 *
	 * @param spec
	 *            the specification to process.
	 * @return processed specification.
	 */
	protected Specification processSpecification(final Specification spec) {
		Specification newSpec = null;
		if (spec instanceof EnsuresSpecification) {
			final Expression expr = ((EnsuresSpecification) spec).getFormula();
			final Expression newExpr = processExpression(expr);
			if (expr != newExpr) {
				newSpec = new EnsuresSpecification(spec.getLocation(), spec.isFree(), newExpr);
			}
		} else if (spec instanceof RequiresSpecification) {
			final Expression expr = ((RequiresSpecification) spec).getFormula();
			final Expression newExpr = processExpression(expr);
			if (expr != newExpr) {
				newSpec = new RequiresSpecification(spec.getLocation(), spec.isFree(), newExpr);
			}
		} else if (spec instanceof ModifiesSpecification) {
			final VariableLHS[] ids = ((ModifiesSpecification) spec).getIdentifiers();
			final VariableLHS[] newIds = processVariableLHSs(ids);
			if (ids != newIds) {
				newSpec = new ModifiesSpecification(spec.getLocation(), spec.isFree(), newIds);
			}
		}
		if (newSpec == null) {
			return spec;
		}
		ModelUtils.copyAnnotations(spec, newSpec);
		return newSpec;
	}

	/**
	 * Process the procedure specifications. Calls processSpecification for each element in the array. This must not be
	 * called for LoopInvariantSpecifications.
	 *
	 * @param specs
	 *            the specifications to process.
	 * @return processed specifications.
	 */
	protected Specification[] processSpecifications(final Specification[] specs) {
		boolean changed = false;
		final Specification[] newSpecs = new Specification[specs.length];
		for (int i = 0; i < newSpecs.length; i++) {
			newSpecs[i] = processSpecification(specs[i]);
			if (newSpecs[i] != specs[i]) {
				changed = true;
			}
		}
		return changed ? newSpecs : specs;
	}

	/**
	 * Process the attribute. Calls processExpression for all contained expressions. This must handle all kinds of
	 * attributes, including triggers.
	 *
	 * @param attr
	 *            the attribute to process.
	 * @return processed attribute.
	 */
	@SuppressWarnings("unchecked")
	protected <T extends Attribute> T processAttribute(final T attr) {
		T newAttr = null;
		if (attr instanceof Trigger) {
			final Expression[] exprs = ((Trigger) attr).getTriggers();
			final Expression[] newExprs = processExpressions(exprs);
			if (newExprs != exprs) {
				return (T) new Trigger(attr.getLocation(), newExprs);
			}
		} else if (attr instanceof NamedAttribute) {
			final Expression[] exprs = ((NamedAttribute) attr).getValues();
			final Expression[] newExprs = processExpressions(exprs);
			if (newExprs != exprs) {
				newAttr = (T) new NamedAttribute(attr.getLocation(), ((NamedAttribute) attr).getName(), newExprs);
			}
		}
		if (newAttr == null) {
			return attr;
		}
		ModelUtils.copyAnnotations(attr, newAttr);
		return newAttr;
	}

	/**
	 * Process the attributes. Calls processAttribute for each element in the array. This must handle all kinds of
	 * attributes, including triggers.
	 *
	 * @param attributes
	 *            the attributes to process.
	 * @return processed attributes.
	 */
	protected <T extends Attribute> T[] processAttributes(final T[] attributes) {
		if (attributes == null) {
			return attributes;
		}
		boolean changed = false;

		final T[] newAttrs = Arrays.copyOf(attributes, attributes.length);
		for (int i = 0; i < attributes.length; i++) {
			newAttrs[i] = processAttribute(attributes[i]);
			if (newAttrs[i] != attributes[i]) {
				changed = true;
			}
		}
		return changed ? newAttrs : attributes;
	}

	/**
	 * Process the expressions. Calls processExpression for each element in the array.
	 *
	 * @param exprs
	 *            the expression to process.
	 * @return processed expressions.
	 */
	protected Expression[] processExpressions(final Expression[] exprs) {
		final Expression[] newExprs = new Expression[exprs.length];
		boolean changed = false;
		for (int j = 0; j < exprs.length; j++) {
			newExprs[j] = processExpression(exprs[j]);
			if (newExprs[j] != exprs[j]) {
				changed = true;
			}
		}
		return changed ? newExprs : exprs;
	}

	/**
	 * Process the expressions. Calls processExpression for each subexpression.
	 *
	 * @param expr
	 *            the expression to process.
	 * @return processed expression.
	 */
	protected Expression processExpression(final Expression expr) {
		Expression newExpr = null;
		if (expr instanceof BinaryExpression) {
			final BinaryExpression binexp = (BinaryExpression) expr;
			final Expression left = processExpression(binexp.getLeft());
			final Expression right = processExpression(binexp.getRight());
			if (left != binexp.getLeft() || right != binexp.getRight()) {
				newExpr = new BinaryExpression(expr.getLocation(), binexp.getType(), binexp.getOperator(), left, right);
			}
		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression unexp = (UnaryExpression) expr;
			final Expression subexpr = processExpression(unexp.getExpr());
			if (subexpr != unexp.getExpr()) {
				newExpr = new UnaryExpression(expr.getLocation(), unexp.getType(), unexp.getOperator(), subexpr);
			}
		} else if (expr instanceof ArrayAccessExpression) {
			final ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
			final Expression arr = processExpression(aaexpr.getArray());
			final Expression[] indices = aaexpr.getIndices();
			final Expression[] newIndices = processExpressions(indices);
			if (arr != aaexpr.getArray() || indices != newIndices) {
				newExpr = new ArrayAccessExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices);
			}
		} else if (expr instanceof ArrayStoreExpression) {
			final ArrayStoreExpression aaexpr = (ArrayStoreExpression) expr;
			final Expression arr = processExpression(aaexpr.getArray());
			final Expression value = processExpression(aaexpr.getValue());
			final Expression[] indices = aaexpr.getIndices();
			final Expression[] newIndices = processExpressions(indices);
			if (arr != aaexpr.getArray() || indices != newIndices || value != aaexpr.getValue()) {
				newExpr = new ArrayStoreExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices, value);
			}
		} else if (expr instanceof BitVectorAccessExpression) {
			final BitVectorAccessExpression bvaexpr = (BitVectorAccessExpression) expr;
			final Expression bv = processExpression(bvaexpr.getBitvec());
			if (bv != bvaexpr.getBitvec()) {
				newExpr = new BitVectorAccessExpression(bvaexpr.getLocation(), bvaexpr.getType(), bv, bvaexpr.getEnd(),
						bvaexpr.getStart());
			}
		} else if (expr instanceof FunctionApplication) {
			final FunctionApplication app = (FunctionApplication) expr;
			final String name = app.getIdentifier();
			final Expression[] args = processExpressions(app.getArguments());
			if (args != app.getArguments()) {
				newExpr = new FunctionApplication(app.getLocation(), app.getType(), name, args);
			}
		} else if (expr instanceof IfThenElseExpression) {
			final IfThenElseExpression ite = (IfThenElseExpression) expr;
			final Expression cond = processExpression(ite.getCondition());
			final Expression thenPart = processExpression(ite.getThenPart());
			final Expression elsePart = processExpression(ite.getElsePart());
			if (cond != ite.getCondition() || thenPart != ite.getThenPart() || elsePart != ite.getElsePart()) {
				newExpr = new IfThenElseExpression(ite.getLocation(), thenPart.getType(), cond, thenPart, elsePart);
			}
		} else if (expr instanceof QuantifierExpression) {
			final QuantifierExpression quant = (QuantifierExpression) expr;
			final Attribute[] attrs = quant.getAttributes();
			final Attribute[] newAttrs = processAttributes(attrs);
			final VarList[] params = quant.getParameters();
			final VarList[] newParams = processVarLists(params);
			final Expression subform = processExpression(quant.getSubformula());
			if (subform != quant.getSubformula() || attrs != newAttrs || params != newParams) {
				newExpr = new QuantifierExpression(quant.getLocation(), quant.getType(), quant.isUniversal(),
						quant.getTypeParams(), newParams, newAttrs, subform);
			}
		} else if (expr instanceof StructConstructor) {
			final StructConstructor sConst = (StructConstructor) expr;
			final Expression[] fieldValues = processExpressions(sConst.getFieldValues());
			if (fieldValues != sConst.getFieldValues()) {
				newExpr = new StructConstructor(sConst.getLocation(), sConst.getFieldIdentifiers(), fieldValues);
			}
		} else if (expr instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) expr;
			final Expression struct = processExpression(sae.getStruct());
			if (struct != sae.getStruct()) {
				newExpr = new StructAccessExpression(sae.getLocation(), struct, sae.getField());
			}
		} else if (expr instanceof BooleanLiteral) {
		} else if (expr instanceof IntegerLiteral) {
		} else if (expr instanceof BitvecLiteral) {
		} else if (expr instanceof StringLiteral) {
		} else if (expr instanceof IdentifierExpression) {
		} else if (expr instanceof WildcardExpression) {
		} else if (expr instanceof RealLiteral) {
		} else if (expr == null) {
			throw new IllegalArgumentException("expression may not be null");
		} else {
			throw new UnsupportedOperationException("unknown expression " + expr.getClass().getName());
		}

		if (newExpr == null || newExpr == expr) {
			/*
			 * BooleanLiteral, IntegerLiteral, BitvecLiteral, StringLiteral, IdentifierExpression and WildcardExpression
			 * do not need recursion, and recursion can leave the expression unchanged.
			 */
			return expr;
		}
		ModelUtils.copyAnnotations(expr, newExpr);
		return newExpr;
	}
}
