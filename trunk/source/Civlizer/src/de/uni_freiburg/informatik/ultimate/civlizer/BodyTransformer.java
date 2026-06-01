package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

final class BodyTransformer extends BoogieTransformer {

	private ProgramAndProof mProgramAndProof;
    private String mCurrentProcedure;
	private int mAtomicStatementCounter;

    BodyTransformer(ProgramAndProof programAndProof) {
		mProgramAndProof = programAndProof;
        mCurrentProcedure = null;
        mAtomicStatementCounter = 0;
    }

    private void setCurrentProcedure(String name) {
        if (mCurrentProcedure != name) {
            mCurrentProcedure = name;
            mAtomicStatementCounter = 0;
        }
    }

	private static List<Expression> tidListToArrayExpression(List<Tid> tidList) {
		return tidList.stream().map(
			tid ->
			(Expression) new IdentifierExpression(
				null, /* maybe to be change TODO or not */
				BoogieType.createPlaceholderType(0),
				tid.toString(),
				new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)
			)
		).toList();
	}

    Body transformBody(final String name, Body body) {
        setCurrentProcedure(name);
        // TO BE improved
        return processBody(body);
    }

    Statement[] transformStatements(final String name, Statement[] statements) {
		setCurrentProcedure(name);

        return processStatements(statements);
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
		List<Statement> newStatements = new ArrayList<>();
		
		int size = mProgramAndProof
			.getTemplateVisitor()
			.getAllTidMap()
			.getOrDefault(mCurrentProcedure, Collections.emptyList())
			.size()
			+ (mCurrentProcedure.equals("ULTIMATE.start") ? 1 : 0);

		Expression[] tids = new Expression[size];

		int i = 0;

		if (mCurrentProcedure.equals("ULTIMATE.start")) {
			tids[i++] = new IdentifierExpression(
				null,
				BoogieType.createPlaceholderType(0),
				"start_tid",
				new DeclarationInformation(
					DeclarationInformation.StorageClass.GLOBAL,
					null
				)
			);
		}

		for (Tid tid : mProgramAndProof
			.getTemplateVisitor()
			.getAllTidMap()
			.getOrDefault(mCurrentProcedure, Collections.emptyList())) 
		{
			tids[i++] = new IdentifierExpression(
				null,
				BoogieType.createPlaceholderType(0),
				tid.toString(),
				new DeclarationInformation(
					DeclarationInformation.StorageClass.GLOBAL,
					null
				)
			);
		}
		
		// we ignore some kind of first Label $Ultimate##0
		for (i = 1; i < statements.length - 1; i++) { // ignore standard return
			mAtomicStatementCounter += 1;

			boolean globalVar = mProgramAndProof
				.getTemplateVisitor()
				.containsGlobalVariables(statements[i]);

			boolean localVar = mProgramAndProof
				.getTemplateVisitor()
				.containsLocalVariables(mCurrentProcedure, statements[i]);
			
			if (statements[i] instanceof ForkStatement
				|| statements[i] instanceof JoinStatement
				|| globalVar && !localVar) {
					newStatements.add(processStatement(statements[i]));
			}
			else if (!globalVar && localVar) {

				NamedAttribute[] layer = new NamedAttribute[] {
					new NamedAttribute(
						statements[i].getLoc(), 
						"layer", 
						new Expression[] {
							new IdentifierExpression(
								statements[i].getLoc(), 
								BoogieType.createPlaceholderType(0),
								"1,2",
								new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)
							)
						}
					)
				};

				if (statements[i] instanceof final AssertStatement assertStmt) {
					newStatements.add(
						new AssertStatement(
							assertStmt.getLoc(), 
							layer, 
							assertStmt.getFormula()
						)
					);
				}
				else if (statements[i] instanceof final AssumeStatement assumeStmt) {
					newStatements.add(
						new AssumeStatement(
							assumeStmt.getLoc(), 
							layer, 
							assumeStmt.getFormula()
						)
					);
				}
				/*else if (statements[i] instanceof final HavocStatement havoc) {
					maybe havoc
				}*/
				else {
					newStatements.add(statements[i]);
				}
			}
			else {
				final var loc = statements[i].getLoc();

				Expression[] arguments = mProgramAndProof
					.getTemplateVisitor()
					.getStatementParametersMap()
					.get(loc)
					.stream()
					.map(arg -> new IdentifierExpression(
						loc, 
						BoogieType.createPlaceholderType(0),
						arg,
						new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)
					))
					.toArray(Expression[]::new);

				VariableLHS[] returns = mProgramAndProof
					.getTemplateVisitor()
					.getStatementParametersMap()
					.get(loc)
					.stream()
					.map(ret -> new VariableLHS(
						loc, 
						ret
					))
					.toArray(VariableLHS[]::new);

				newStatements.add(new CallStatement(statements[i].getLocation(), new NamedAttribute[0], false,
			    	returns, mCurrentProcedure + "_stmt_" + mAtomicStatementCounter, arguments));
			}

			newStatements.add(new CallStatement(statements[i].getLocation(), new NamedAttribute[0], false,
			    new VariableLHS[0], "yield_" + mCurrentProcedure + "_" + mAtomicStatementCounter, tids));

			// Ghost update
			if (mProgramAndProof.getGhostUpdateMap() != null 
				&& mProgramAndProof
					.getGhostUpdateMap().get(statements[i].getLocation()) != null) {
				for (CallStatement stmt : mProgramAndProof
						.getGhostUpdateMap().get(statements[i].getLocation())
				) {
					newStatements.add(stmt);
				}
			}
		}
		
		if (mCurrentProcedure != "ULTIMATE.start") {
			newStatements.add(new CallStatement(null, new NamedAttribute[0], false,
			    new VariableLHS[0], "terminate", tids));
		}

		return newStatements.toArray(Statement[]::new);
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
		//Label, IfStatement, AssignmentStatement, ReturnStatement, ForkStatement, CallStatement, JoinStatement, AssertStatement, WhileStatement, GotoStatement, AtomicStatement, AssumeStatement, BreakStatement, HavocStatement
		if (statement instanceof AssertStatement 
			|| statement instanceof IfStatement
            || statement instanceof AssignmentStatement
            || statement instanceof AssumeStatement
			|| statement instanceof WhileStatement
            || statement instanceof AtomicStatement
			|| statement instanceof HavocStatement
        ) {
		    newStatement = new CallStatement(statement.getLocation(), new NamedAttribute[0], false,
		    	new VariableLHS[0], mCurrentProcedure + "_stmt_" + mAtomicStatementCounter, new Expression[0]);

		} else if (statement instanceof final CallStatement call) {
			final Expression[] args = call.getArguments();
			final Expression[] newArgs = processExpressions(args);
			final VariableLHS[] lhs = call.getLhs();
			final VariableLHS[] newLhs = processVariableLHSs(lhs);
			final Attribute[] newAttr = processAttributes(call.getAttributes());
			if (args != newArgs || lhs != newLhs || newAttr != call.getAttributes()) {
				newStatement = new CallStatement(call.getLocation(), (NamedAttribute[]) newAttr, call.isForall(),
						newLhs, call.getMethodName(), newArgs);

				// create error
			}
		} else if (statement instanceof final ForkStatement forkstmt) {
			final Expression[] threadId = forkstmt.getThreadID();
			final String procName = forkstmt.getProcedureName();
			final Expression[] arguments = forkstmt.getArguments();
			final Expression[] newThreadId = processExpressions(threadId);
			final Expression[] newArguments = processExpressions(arguments);

			Expression[] tids = new Expression[] { 
				new IdentifierExpression(
					forkstmt.getLoc(), /* maybe to be change TODO or not */
					BoogieType.createPlaceholderType(0),
					"start_tid",
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)
				),
				new IdentifierExpression(
					forkstmt.getLoc(), /* maybe to be change TODO or not */
					BoogieType.createPlaceholderType(0),
					(new Tid(threadId)).toString(),
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)
				)
			};

            newStatement = new CallStatement(forkstmt.getLoc(), new NamedAttribute[0], false,
				new VariableLHS[0], "fork_" + procName, tids);  // add expression TODO

		} else if (statement instanceof final JoinStatement joinstmt) {
			final Expression[] threadId = joinstmt.getThreadID();
			final VariableLHS[] lhs = joinstmt.getLhs();
			final Expression[] newThreadId = processExpressions(threadId);
			final VariableLHS[] newLhs = processVariableLHSs(lhs);

			// variable out to define TODO

			Expression[] tid = new Expression[] {
				new IdentifierExpression(
					joinstmt.getLoc(), /* maybe to be change TODO or not */
					BoogieType.createPlaceholderType(0),
					"start_tid",
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)
				),
				new IdentifierExpression(
					joinstmt.getLoc(), /* maybe to be change TODO or not */
					BoogieType.createPlaceholderType(0),
					(new Tid(threadId)).toString(),
					new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)
				)
			};

			//VariableLHS[] out = new VariableLHS[] {
			//	new VariableLHS(joinstmt.getLoc(), "out" + ((new Tid(threadId)).toString()).substring(3))
			//}; Maybe laiter

            newStatement = new CallStatement(joinstmt.getLoc(), new NamedAttribute[0], false,
				new VariableLHS[0], "join", tid); // LHS TODO
		
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
		if (lhs instanceof final ArrayLHS alhs) {
			final LeftHandSide array = alhs.getArray();
			final LeftHandSide newArray = processLeftHandSide(array);
			final Expression[] indices = alhs.getIndices();
			final Expression[] newIndices = processExpressions(indices);
			if (array != newArray || indices != newIndices) {
				final LeftHandSide newLhs = new ArrayLHS(lhs.getLocation(), alhs.getType(), newArray, newIndices);
				ModelUtils.copyAnnotations(lhs, newLhs);
				return newLhs;
			}
		} else if (lhs instanceof final StructLHS slhs) {
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
		if (spec instanceof final EnsuresSpecification ensures) {
			final Expression expr = ensures.getFormula();
			final Expression newExpr = processExpression(expr);
			if (expr != newExpr) {
				newSpec = new EnsuresSpecification(spec.getLocation(), spec.isFree(), newExpr);
			}
		} else if (spec instanceof final RequiresSpecification requires) {
			final Expression expr = requires.getFormula();
			final Expression newExpr = processExpression(expr);
			if (expr != newExpr) {
				newSpec = new RequiresSpecification(spec.getLocation(), spec.isFree(), newExpr);
			}
		} else if (spec instanceof final ModifiesSpecification modifies) {
			final VariableLHS[] ids = modifies.getIdentifiers();
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
		if (attr instanceof final Trigger trigger) {
			final Expression[] exprs = trigger.getTriggers();
			final Expression[] newExprs = processExpressions(exprs);
			if (newExprs != exprs) {
				return (T) new Trigger(attr.getLocation(), newExprs);
			}
		} else if (attr instanceof final NamedAttribute named) {
			final Expression[] exprs = named.getValues();
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
}