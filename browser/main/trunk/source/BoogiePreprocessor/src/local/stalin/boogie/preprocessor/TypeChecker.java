/**
 * 
 */
package local.stalin.boogie.preprocessor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import org.apache.log4j.Logger;

import java.util.ListIterator;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.boogie.type.ArrayType;
import local.stalin.boogie.type.BoogieType;
import local.stalin.boogie.type.FunctionSignature;
import local.stalin.boogie.type.PrimitiveType;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.boogie.ast.*;
import local.stalin.model.boogie.ast.wrapper.WrapperNode;

/**
 * This class is a AST-Visitor for creating textual representations of the tree. It creates a String.
 * 
 */
public class TypeChecker implements IUnmanagedObserver {
	private TypeManager typeManager;
	private HashMap<String, FunctionInfo> declaredFunctions;
	private HashMap<String, ProcedureInfo> declaredProcedures;
	private HashMap<String, VariableInfo> declaredVars;
	private Stack<VariableInfo[]> varScopes;
	
	private static BoogieType boolType = BoogieType.boolType;
	private static BoogieType intType = BoogieType.intType;
	private static BoogieType realType = BoogieType.realType;
	private static BoogieType errorType = BoogieType.errorType;
	
	private static Logger s_logger = StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	
	private int getBitVecLength(BoogieType t) {
		t = t.getUnderlyingType();
		if (!(t instanceof PrimitiveType))
			return -1;
		return ((PrimitiveType) t).getTypeCode();
	}
	
	private VariableInfo findVariable(String name) {
		ListIterator<VariableInfo[]> it = varScopes.listIterator(varScopes.size());
		while (it.hasPrevious()) {
			for (VariableInfo vi : it.previous()) {
				if (vi.getName().equals(name))
					return vi;
			}
		}
		return declaredVars.get(name);
	}
	
	private BoogieType typecheckExpression(Expression expr) {
		BoogieType resultType;
		if (expr instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) expr;
			BoogieType left = typecheckExpression(binexp.getLeft());
			BoogieType right = typecheckExpression(binexp.getRight());
			
			switch (binexp.getOperator()) {
			case LOGICIFF:
			case LOGICIMPLIES:
			case LOGICAND:
			case LOGICOR:
				if ((!left.equals(errorType) && !left.equals(boolType))
					|| (!right.equals(errorType) && !right.equals(boolType))) {
					s_logger.error("Type check failed for "+expr);
				}
				resultType = boolType; /* try to recover in any case */
				break;
			case ARITHDIV:
			case ARITHMINUS:
			case ARITHMOD:
			case ARITHMUL:
			case ARITHPLUS:
				/* Try to recover for error types */
				if (left.equals(errorType)) {
					left = right;
				} else if (right.equals(errorType)) {
					right = left;
				}
				if (!left.equals(right)
					|| (!left.equals(intType) && !left.equals(realType))
					|| (left.equals(realType) 
						&& binexp.getOperator() == BinaryExpression.Operator.ARITHMOD)) {
					s_logger.error("Type check failed for "+expr);
					resultType = errorType;
				} else {
					resultType = left;
				}
				break;
			case COMPLT:
			case COMPGT:
			case COMPLEQ:
			case COMPGEQ:
				/* Try to recover for error types */
				if (left.equals(errorType)) {
					left = right;
				} else if (right.equals(errorType)) {
					right = left;
				}
				if (!left.equals(right)
					|| (!left.equals(intType) && !left.equals(realType))) {
					s_logger.error("Type check failed for "+expr);
				}
				resultType = boolType; /* try to recover in any case */
				break;
			case COMPNEQ:
			case COMPEQ:
				if (!left.isUnifiableTo(right))
					s_logger.error("Type check failed for "+expr);
				resultType = boolType; /* try to recover in any case */
				break;
			case COMPPO:
				if (!left.equals(right)
					&& !left.equals(errorType) && !right.equals(errorType)) {
					s_logger.error("Type check failed for "+expr+": "+left.getUnderlyingType()+" != "+right.getUnderlyingType());
				}
				resultType = boolType; /* try to recover in any case */
				break;
			case BITVECCONCAT:
				int leftLen = getBitVecLength(left);
				int rightLen = getBitVecLength(right);
				if (leftLen < 0 || rightLen < 0 || leftLen+rightLen < 0 /* handle overflow */) {
					if (!left.equals(errorType) && !right.equals(errorType))
						s_logger.error("Type check failed for "+expr);
					leftLen = 0; rightLen = 0; /* recover */
				}
				resultType = BoogieType.createBitvectorType(leftLen+rightLen);
				break;
			default:
				s_logger.fatal("Unknown Binary operator "+binexp.getOperator());
				resultType = errorType;
			}
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) expr;
			BoogieType subtype = typecheckExpression(unexp.getExpr());
			switch (unexp.getOperator()) {
			case LOGICNEG:
				if (!subtype.equals(errorType) && !subtype.equals(boolType))
					s_logger.error("Type check failed for "+expr);
				resultType = boolType; /* try to recover in any case */
				break;
			case ARITHNEGATIVE:
				if (!subtype.equals(errorType) && !subtype.equals(intType))
					s_logger.error("Type check failed for "+expr);
				resultType = intType; /* try to recover in any case */
				break;
			case OLD:
				resultType = subtype;
				break;
			default:
				s_logger.fatal("Unknown Unary operator "+unexp.getOperator());
				resultType = errorType;
			}
		} else if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression bvaexpr = 
				(BitVectorAccessExpression) expr;
			BoogieType bvType = typecheckExpression(bvaexpr.getBitvec());
			int bvlen = getBitVecLength(bvType);
			int end   = bvaexpr.getEnd();
			int start = bvaexpr.getStart();
			if (start < 0 || end < start || bvlen < end) {
				if (!bvType.equals(errorType))
					s_logger.error("Type check failed for "+expr);
				start = end = 0;
			}
			resultType = BoogieType.createBitvectorType(end-start);
		} else if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
			BoogieType e = typecheckExpression(aaexpr.getArray()).getUnderlyingType();
			if (!(e instanceof ArrayType)) {
				if (!e.equals(errorType))
					s_logger.error("Type check failed (not an array): "+expr);
				resultType = errorType;
			} else {
				ArrayType arr = (ArrayType) e;
				BoogieType[] subst = new BoogieType[arr.getNumPlaceholders()];
				Expression[] indices = aaexpr.getIndices(); 
				if (indices.length != arr.getIndexCount()) {
					s_logger.error("Type check failed (wrong number of indices): "+expr);
				} else {
					for (int i = 0; i < indices.length; i++) {
						BoogieType t = typecheckExpression(indices[i]);
						if (!t.equals(errorType) 
							&& !arr.getIndexType(i).unify(t, subst)) {
							s_logger.error("Type check failed (index "+i+"): "+expr);
						}
					}
				}
				resultType = arr.getValueType().substitutePlaceholders(subst);
			}
		} else if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression asexpr = (ArrayStoreExpression) expr;
			BoogieType e = typecheckExpression(asexpr.getArray()).getUnderlyingType();
			if (!(e instanceof ArrayType)) {
				if (!e.equals(errorType))
					s_logger.error("Type check failed (not an array): "+expr);
				resultType = errorType;
			} else {
				ArrayType arr = (ArrayType) e;
				BoogieType[] subst = new BoogieType[arr.getNumPlaceholders()];
				Expression[] indices = asexpr.getIndices(); 
				if (indices.length != arr.getIndexCount()) {
					s_logger.error("Type check failed (wrong number of indices): "+expr);
				} else {
					for (int i = 0; i < indices.length; i++) {
						BoogieType t = typecheckExpression(indices[i]);
						if (!t.equals(errorType) 
								&& !arr.getIndexType(i).unify(t, subst)) {
								s_logger.error("Type check failed (index "+i+"): "+expr);
							}
					}
					BoogieType valueType = typecheckExpression(asexpr.getValue());
					if (!valueType.equals(errorType) 
						&& !arr.getValueType().unify(valueType, subst)) {
						s_logger.error("Type check failed (value): "+expr);
					}
				}
				resultType = arr;
			}
		} else if (expr instanceof BooleanLiteral) {
			resultType = boolType;
		} else if (expr instanceof IntegerLiteral) {
			resultType = intType;
		} else if (expr instanceof RealLiteral) {
			resultType = realType;
		} else if (expr instanceof BitvecLiteral) {
			BitvecLiteral bvlit = (BitvecLiteral) expr;
			resultType = BoogieType.createBitvectorType(bvlit.getLength());
		} else if (expr instanceof IdentifierExpression) {
			IdentifierExpression idexpr = (IdentifierExpression) expr;
			String name = idexpr.getIdentifier();
			VariableInfo info = findVariable(name);
			if (info == null) {
				s_logger.error("Undeclared identifier "+name+" in "+expr);
				resultType = errorType;
			} else {
				resultType = info.getType();
			}
		} else if (expr instanceof FunctionApplication) {
			FunctionApplication app = (FunctionApplication) expr;
			String name = app.getIdentifier();
			FunctionInfo fi = declaredFunctions.get(name);
			if (fi == null) {
				s_logger.error("Undeclared function "+name+" in "+expr);
				resultType = errorType;
			} else {
				FunctionSignature fs = fi.getSignature();
				BoogieType[] subst = new BoogieType[fs.getTypeArgCount()];
				Expression[] appArgs = app.getArguments(); 
				if (appArgs.length != fs.getParamCount()) {
					s_logger.error("Type check failed (wrong number of indices): "+expr);
				} else {
					for (int i = 0; i < appArgs.length; i++) {
						BoogieType t = typecheckExpression(appArgs[i]);
						if (!t.equals(errorType)
								&& !fs.getParamType(i).unify(t, subst)) {
							s_logger.error("Type check failed (index "+i+"): "+expr);
						}
					}
				}
				resultType = fs.getResultType().substitutePlaceholders(subst);
			}
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			BoogieType condType = typecheckExpression(ite.getCondition());
			if (!condType.equals(errorType) && !condType.equals(boolType)) {
				s_logger.error("if expects boolean type: "+expr);
			}
			BoogieType left = typecheckExpression(ite.getThenPart());
			BoogieType right = typecheckExpression(ite.getElsePart());
			if (!left.isUnifiableTo(right)) {
				s_logger.error("Type check failed for "+expr);
				resultType = errorType;
			} else {
				resultType = left.equals(errorType) ? right : left;
			}
		} else if (expr instanceof QuantifierExpression) {
			QuantifierExpression quant = (QuantifierExpression) expr;
			TypeParameters typeParams = new TypeParameters(quant.getTypeParams()); 
			typeManager.pushTypeScope(typeParams);

			VarList[] parameters = quant.getParameters();
			List<VariableInfo> vinfo = new ArrayList<VariableInfo>();
			for (VarList p : parameters) {
				BoogieType type = typeManager.resolveType(p.getType());
				for (String id : p.getIdentifiers()) {
					vinfo.add(new VariableInfo(true, null, id, type));
				}
			}
			if (!typeParams.fullyUsed())
				s_logger.error("Type args not fully used in variable types: "+expr);

			VariableInfo[] scope = vinfo.toArray(new VariableInfo[vinfo.size()]);
			varScopes.push(scope);
			typecheckAttributes(quant.getAttributes());
			BoogieType t = typecheckExpression(quant.getSubformula());
			if (!t.equals(errorType) && !t.equals(boolType)) {
				s_logger.error("Type check error in: "+expr);
			}
			varScopes.pop();
			typeManager.popTypeScope();
			resultType = boolType;
		} else {
			throw new IllegalStateException("Unknown expression node "+expr);
		}
		expr.setType(resultType);
		return resultType;
	}
	
	private BoogieType typecheckLeftHandSide(LeftHandSide lhs) {
		BoogieType resultType;
		if (lhs instanceof VariableLHS) {
			String name = ((VariableLHS)lhs).getIdentifier();
			VariableInfo info = findVariable(name);
			if (info == null) {
				s_logger.error("Undeclared identifier "+name);
				resultType = errorType;
			} else {
				if (info.isRigid())
					s_logger.error("Assignment to read-only variable "+name);
				resultType = info.getType(); 
			}
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS alhs = (ArrayLHS) lhs;
			BoogieType type = typecheckLeftHandSide(alhs.getArray());
			if (!(type instanceof ArrayType)) {
				if (!type.equals(errorType))
					s_logger.error("Type check failed (not an array): "+lhs);
				resultType = errorType;
			} else {
				ArrayType arrType = (ArrayType) type;
				BoogieType[] subst = new BoogieType[arrType.getNumPlaceholders()];
				Expression[] indices = alhs.getIndices(); 
				if (indices.length != arrType.getIndexCount()) {
					s_logger.error("Type check failed (wrong number of indices): "+lhs);
					resultType = errorType;
				} else {
					for (int i = 0; i < indices.length; i++) {
						BoogieType t = typecheckExpression(indices[i]);
						if (!t.equals(errorType) 
							&& !arrType.getIndexType(i).unify(t, subst)) {
							s_logger.error("Type check failed (index "+i+"): "+lhs);
						}
					}
					resultType = arrType.getValueType().substitutePlaceholders(subst);
				}
			}
		} else {
			s_logger.fatal("Unknown LHS: "+lhs);
			resultType = errorType;
		}
		lhs.setType(resultType);
		return resultType;
	}
	
	private void typecheckAttributes(Attribute[] attributes) {
		for (Attribute attr: attributes) {
			Expression[] exprs;
			if (attr instanceof Trigger) {
				exprs = ((Trigger)attr).getTriggers();
			} else if (attr instanceof NamedAttribute) {
				exprs = ((NamedAttribute)attr).getValues();
			} else 
				throw new IllegalStateException("Unknown Attribute "+attr);
			for (Expression e : exprs) {
				if (!(e instanceof StringLiteral))
					typecheckExpression(e);
			}
		}
	}
	
	private String getLeftHandSideIdentifier(LeftHandSide lhs) {
		while (lhs instanceof ArrayLHS) {
			lhs = ((ArrayLHS) lhs).getArray();
		}
		return ((VariableLHS)lhs).getIdentifier();
	}
	
	private void processVariableDeclaration(VariableDeclaration varDecl) {
		for (VarList varlist : varDecl.getVariables()) {
			BoogieType type = typeManager.resolveType(varlist.getType());
			for (String id : varlist.getIdentifiers()) {
				//s_logger.info("Declaring variable "+id+":"+type);
				declaredVars.put(id, new VariableInfo(false, varDecl, id, type));
			}			
		}
	}
	private void processConstDeclaration(ConstDeclaration constDecl) {
		VarList varList = constDecl.getVarList();
		BoogieType type = typeManager.resolveType(varList.getType());
		for (String id: varList.getIdentifiers()) {
			//s_logger.info("Declaring constant "+id+":"+type);
			declaredVars.put(id, new VariableInfo(true, constDecl, id, type));
		}	
	}

	private void checkConstDeclaration(ConstDeclaration constDecl) {
		ParentEdge[] parents = constDecl.getParentInfo();
		if (parents == null)
			return;
		BoogieType type = (BoogieType) constDecl.getVarList().getType().getBoogieType();
		for (ParentEdge p : parents) {
			VariableInfo var = declaredVars.get(p.getIdentifier());
			if (var == null || !var.isRigid())
				s_logger.error(constDecl + ": parent is not a const");
			else if (!type.equals(var.getType())
				&& !var.getType().equals(BoogieType.errorType)
			    && !type.equals(BoogieType.errorType))
				s_logger.error(constDecl + ": parent is not of same type");
		}	
	}

	private void processFunctionDeclaration(FunctionDeclaration funcDecl) {
		String name = funcDecl.getIdentifier();

		TypeParameters typeParams = new TypeParameters(funcDecl.getTypeParams()); 
		typeManager.pushTypeScope(typeParams);

		VarList[] paramNodes = funcDecl.getInParams();
		String[]  paramNames = new String[paramNodes.length];
		BoogieType[] paramTypes = new BoogieType[paramNodes.length];
		for (int i = 0; i < paramNodes.length; i++) {
			String[] names = paramNodes[i].getIdentifiers();
			if (names.length > 0)
				paramNames[i] = names[0];
			paramTypes[i] = typeManager.resolveType(paramNodes[i].getType());
		}
		if (!typeParams.fullyUsed())
			s_logger.error("Type args not fully used in function parameter: "+funcDecl);

		String valueName = null;
		String[] valueNames = funcDecl.getOutParam().getIdentifiers();
		BoogieType valueType = typeManager.resolveType(funcDecl.getOutParam().getType());
		if (valueNames.length > 0)
			valueName = valueNames[0];

		typeManager.popTypeScope();

		FunctionSignature fs = new FunctionSignature
			(funcDecl.getTypeParams().length, paramNames, paramTypes, valueName, valueType);
		//s_logger.info("Declaring function "+name+fs);
		declaredFunctions.put(name, new FunctionInfo(funcDecl, name, typeParams, fs));
	}

	private void processFunctionDefinition(FunctionDeclaration funcDecl) {
		/* type check the body of a function */
		if (funcDecl.getBody() == null)
			return;

		/* Declare local variables for parameters */
		String name = funcDecl.getIdentifier();
		FunctionInfo fi = declaredFunctions.get(name);
		TypeParameters typeParams = fi.getTypeParameters();
		
		typeManager.pushTypeScope(typeParams);
		FunctionSignature fs  = fi.getSignature();
		List<VariableInfo> vinfo = new ArrayList<VariableInfo>();
		int paramCount = fs.getParamCount();		
		for (int i = 0; i < paramCount; i++) {
			if (fs.getParamName(i) != null) {
				vinfo.add(new VariableInfo(true, null, 
						fs.getParamName(i), fs.getParamType(i)));
			}
		}
		VariableInfo[] scope = vinfo.toArray(new VariableInfo[vinfo.size()]);
		varScopes.push(scope);
		BoogieType valueType = typecheckExpression(funcDecl.getBody());
		if (!valueType.equals(errorType) && !valueType.equals(fs.getResultType()))
			s_logger.error(funcDecl.getFilename()+":"+funcDecl.getLineNr()
					+": Return type of function doesn't match body");
		varScopes.pop();
		typeManager.popTypeScope();
	}
	
	public void processProcedureDeclaration(Procedure proc) {
		if (proc.getSpecification() == null) {
			/* This is only an implementation.  It is checked later. */
			return;
		}
		
		String name = proc.getIdentifier();
		TypeParameters typeParams = new TypeParameters(proc.getTypeParams());
		typeManager.pushTypeScope(typeParams);

		LinkedList<VariableInfo> inParams = new LinkedList<VariableInfo>();
		for (VarList vl : proc.getInParams()) {
			BoogieType type = typeManager.resolveType(vl.getType());
			for (String id : vl.getIdentifiers()) {
				inParams.add(new VariableInfo(true /* in params are rigid */, proc, id, type));
			}
		}
		if (!typeParams.fullyUsed())
			s_logger.error("Type args not fully used in procedure parameter: "+proc);
		LinkedList<VariableInfo> outParams = new LinkedList<VariableInfo>();
		for (VarList vl : proc.getOutParams()) {
			BoogieType type = typeManager.resolveType(vl.getType());
			for (String id : vl.getIdentifiers()) {
				outParams.add(new VariableInfo(false, proc, id, type));
			}
		}
		
		VariableInfo[] allParams = new VariableInfo[inParams.size()+outParams.size()];
		int i = 0;
		for (VariableInfo vi : inParams)
			allParams[i++] = vi;
		for (VariableInfo vi : outParams)
			allParams[i++] = vi;
		varScopes.push(allParams);
		for (VarList vl : proc.getInParams()) {
			if (vl.getWhereClause() != null) {
				BoogieType t = typecheckExpression(vl.getWhereClause());
				if (!t.equals(boolType) && !t.equals(errorType))
					s_logger.error("Where clause is not boolean: "+vl.getWhereClause());
			}
		}
		for (VarList vl : proc.getOutParams()) {
			if (vl.getWhereClause() != null) {
				BoogieType t = typecheckExpression(vl.getWhereClause());
				if (!t.equals(boolType) && !t.equals(errorType))
					s_logger.error("Where clause is not boolean: "+vl.getWhereClause());
			}
		}
		for (Specification s: proc.getSpecification()) {
			if (s instanceof RequiresSpecification) {
				BoogieType t = typecheckExpression(((RequiresSpecification)s).getFormula());
				if (!t.equals(boolType) && !t.equals(errorType))
					s_logger.error("Requires clause is not boolean: "+s);
			} else if (s instanceof EnsuresSpecification) {
				BoogieType t = typecheckExpression(((EnsuresSpecification)s).getFormula());
				if (!t.equals(boolType) && !t.equals(errorType))
					s_logger.error("Ensures clause is not boolean: "+s);
			} else if (s instanceof ModifiesSpecification) {
				for (String id : ((ModifiesSpecification)s).getIdentifiers()) {
					if (findVariable(id) == null)
						s_logger.error("Modifies clause contains unknown id "+id);
				}
			} else {
				s_logger.fatal("Unknown Procedure specification: "+s);
			}
		}
		varScopes.pop();
		typeManager.popTypeScope();

		ProcedureInfo pi = new ProcedureInfo(proc, typeParams, 
				inParams.toArray(new VariableInfo[inParams.size()]), 
				outParams.toArray(new VariableInfo[outParams.size()]));
		//s_logger.info("Declaring procedure "+pi);
		declaredProcedures.put(name, pi);
	}
	
	/**
	 * Collect all labels in the given block and store them in the hash set labels.
	 * @param labels The hash set where the labels are stored.
	 * @param block The code block.
	 */
	private void processLabels(HashSet<String> labels, Statement[] block) {
		for (Statement s: block) {
			if (s instanceof Label) {
				labels.add(((Label)s).getName());
			} else if (s instanceof IfStatement) {
				processLabels(labels, ((IfStatement)s).getThenPart());
				processLabels(labels, ((IfStatement)s).getElsePart());
			} else if (s instanceof WhileStatement) {
				processLabels(labels, ((WhileStatement)s).getBody());
			}
		}
	}

	/**
	 * Type check the given statement.
	 * @param outer the labels right before some outer block.
	 * @param allLabels all labels appearing in the implementation body.
	 * @param statement the code to type check.
	 */
	private void typecheckStatement(Stack<String> outer, HashSet<String> allLabels, 
			Statement statement) {
		if (statement instanceof AssumeStatement) {
			BoogieType t = typecheckExpression(((AssumeStatement)statement).getFormula());
			if (!t.equals(boolType) && !t.equals(errorType))
				s_logger.error("Assume is not boolean: "+statement);
		} else if (statement instanceof AssertStatement) {
			BoogieType t = typecheckExpression(((AssertStatement)statement).getFormula());
			if (!t.equals(boolType) && !t.equals(errorType))
				s_logger.error("Assert is not boolean: "+statement);
		} else if (statement instanceof BreakStatement) {
			String label = ((BreakStatement)statement).getLabel();
			if (!outer.contains(label == null ? "*" : label)) {
				s_logger.error("Break label not found: "+statement);
			}
		} else if (statement instanceof HavocStatement) {
			for (String id : ((HavocStatement)statement).getIdentifiers()) {
				if (findVariable(id) == null) {
					s_logger.error("Unknown Variable "+id+" in "+statement);
				}
			}
		} else if (statement instanceof AssignmentStatement) {
			AssignmentStatement astmt = (AssignmentStatement) statement;
			LeftHandSide[] lhs = astmt.getLhs();
			String[] lhsId = new String[lhs.length];
		    Expression[] rhs = astmt.getRhs();
		    if (lhs.length != rhs.length) {
		    	s_logger.error("Number of variables do not match in "+statement);
		    } else {
		    	for (int i = 0; i < lhs.length; i++) {
		    		lhsId[i] = getLeftHandSideIdentifier(lhs[i]);
		    		for (int j = 0; j < i; j++) {
		    			if (lhsId[i].equals(lhsId[j]))
		    				s_logger.error("Variable appears multiple times in assignment: "+statement);
		    		}
		    		BoogieType lhsType = typecheckLeftHandSide(lhs[i]);
		    		BoogieType rhsType = typecheckExpression(rhs[i]);
		    		if (!lhsType.equals(errorType) && !rhsType.equals(errorType)
		    			&& !lhsType.equals(rhsType)) {
		    			s_logger.error("Type mismatch ("+lhsType + " != "+rhsType+
		    					") in "+statement);
		    		}
		    	}
		    }
		} else if (statement instanceof GotoStatement) {
			for (String label : ((GotoStatement)statement).getLabels()) {
				if (!allLabels.contains(label)) {
					s_logger.error("Goto label not found: "+statement);
				}
			}
		} else if (statement instanceof ReturnStatement) {
			/* Nothing to check */
		} else if (statement instanceof IfStatement) {
			IfStatement ifstmt = (IfStatement)statement;
			if (!(ifstmt.getCondition() instanceof WildcardExpression)) {
				BoogieType t = typecheckExpression(ifstmt.getCondition());
				if (!t.equals(boolType) && !t.equals(errorType))
					s_logger.error("Condition is not boolean: "+statement);
			}
			typecheckBlock(outer, allLabels, ifstmt.getThenPart());
			typecheckBlock(outer, allLabels, ifstmt.getElsePart());
		} else if (statement instanceof WhileStatement) {
			WhileStatement whilestmt = (WhileStatement)statement;
			if (!(whilestmt.getCondition() instanceof WildcardExpression)) {
				BoogieType t = typecheckExpression(whilestmt.getCondition());
				if (!t.equals(boolType) && !t.equals(errorType))
					s_logger.error("Condition is not boolean: "+statement);
			}
			for (Specification inv : whilestmt.getInvariants()) {
				if (inv instanceof LoopInvariantSpecification) {
					typecheckExpression(((LoopInvariantSpecification)inv).getFormula());
				} else {
					s_logger.fatal("Unknown while specification: "+inv);
				}
			}
			outer.push("*");
			typecheckBlock(outer, allLabels, whilestmt.getBody());
			outer.pop();
		} else if (statement instanceof CallStatement) {
			CallStatement call = (CallStatement) statement;
			ProcedureInfo procInfo = declaredProcedures.get(call.getMethodName());
			if (procInfo == null) {
				s_logger.error("Calling undeclared procedure "+call);
				return;
			}
			if (call.isForall()) {
				Specification[] spec = procInfo.getDeclaration().getSpecification();
				for (Specification s: spec) {
					if (s instanceof ModifiesSpecification && !s.isFree()) {
						s_logger.error("call forall on method with checked modifies: "+statement);
						break;
					}
				}
			}
			BoogieType[] typeParams = new BoogieType[procInfo.getTypeParameters().getCount()];
			VariableInfo[] inParams = procInfo.getInParams();
			Expression[] arguments = call.getArguments();
			if (arguments.length != inParams.length) {
				s_logger.error("Procedure called with wrong number of arguments: "+call);
				return;
			}
			for (int i = 0; i < arguments.length; i++) {
				if (call.isForall()) {
					/* check for wildcard expresion and just skip them. */
					if (arguments[i] instanceof WildcardExpression)
						continue;
				}
				BoogieType t = typecheckExpression(arguments[i]);
				if (!inParams[i].getType().unify(t, typeParams)) {
					s_logger.error("Wrong parameter type at index "+i+": "+call);
				}
			}
			VariableInfo[] outParams = procInfo.getOutParams();
			String[] lhs = call.getLhs();
		    if (lhs.length != outParams.length) {
		    	s_logger.error("Number of output variables do not match in "+statement);
		    } else {
		    	for (int i = 0; i < lhs.length; i++) {
		    		for (int j = 0; j < i; j++) {
		    			if (lhs[i].equals(lhs[j]))
		    				s_logger.error("Variable appears multiple times in assignment: "+statement);
		    		}
					VariableInfo info = findVariable(lhs[i]);
					if (info == null) {
						s_logger.error("Undeclared identifier "+lhs[i]+" in "+statement);
						continue;
					}
					if (info.isRigid())
						s_logger.error("Assignment to read-only variable "+lhs[i]+" in "+statement);
					if (!outParams[i].getType().unify(info.getType(), typeParams)) {
		    			s_logger.error("Type mismatch (output parameter "+i+") in "+statement);
		    		}
		    	}
		    }
		} else {
			s_logger.fatal("Not implemented: type checking for "+statement);
		}
	}

	/**
	 * Type check the given block.
	 * @param outer the labels right before some outer block.
	 * @param allLabels all labels appearing in the implementation body.
	 * @param block the code to type check.
	 */
	private void typecheckBlock(Stack<String> outer, HashSet<String> allLabels, 
			Statement[] block) {
		int numLabels = 0;
		for (Statement s: block) {
			if (s instanceof Label) {
				outer.push(((Label)s).getName());
				numLabels++;
			} else {
				typecheckStatement(outer, allLabels, s);
				while (numLabels-- > 0)
					outer.pop();
			}
		}
	}
	
	private void processBody(Body body) {
		LinkedList<VariableInfo> localVarList = new LinkedList<VariableInfo>();
		for (VariableDeclaration decl : body.getLocalVars()) {
			for (VarList vl : decl.getVariables()) {
				BoogieType type = typeManager.resolveType(vl.getType());
				for (String id : vl.getIdentifiers()) {
					localVarList.add(new VariableInfo(false, decl, id, type));
				}
			}
		}
		varScopes.push(localVarList.toArray(new VariableInfo[localVarList.size()]));
		/* Now check where clauses */
		for (VariableDeclaration decl : body.getLocalVars()) {
			for (VarList vl : decl.getVariables()) {
				if (vl.getWhereClause() != null) {
					BoogieType t = typecheckExpression(vl.getWhereClause());
					if (!t.equals(boolType) && !t.equals(errorType))
						s_logger.error("Where clause is not boolean: "+decl);
				}
			}
		}
		
		/* Get Labels */
		HashSet<String> labels = new HashSet<String>();
		processLabels(labels, body.getBlock());
		/* Finally check statements */
		typecheckBlock(new Stack<String>(), labels, body.getBlock());
		varScopes.pop();
	}
	
	private void processImplementation(Procedure impl) {
		if (impl.getBody() == null) {
			/* This is a procedure declaration without body.  Nothing to check. */
			return;
		}
		ProcedureInfo procInfo = declaredProcedures.get(impl.getIdentifier());
		if (procInfo == null) {
			s_logger.error("Implementation without procedure: "+impl.getIdentifier());
			return;
		}
		TypeParameters typeParams = new TypeParameters(impl.getTypeParams());
		typeManager.pushTypeScope(typeParams);

		LinkedList<VariableInfo> allParams = new LinkedList<VariableInfo>();
		VariableInfo[] procInParams = procInfo.getInParams();
		VariableInfo[] procOutParams = procInfo.getOutParams();
		int i = 0;
		for (VarList vl : impl.getInParams()) {
			BoogieType type = typeManager.resolveType(vl.getType());
			for (String id : vl.getIdentifiers()) {
				if (i >= procInParams.length) {
					s_logger.error("Too many input parameters in "+impl);
				} else if (!procInParams[i++].getType().equals(type)) {
					s_logger.error("Type differs at parameter "+id+" in "+impl);
				}
				allParams.add(new VariableInfo(true /* in params are rigid */, impl, id, type));
			}
		}
		if (i < procInParams.length)
			s_logger.error("Too few input parameters in "+impl);
		if (!typeParams.fullyUsed())
			s_logger.error("Type args not fully used in implementation: "+impl);
		i = 0;
		for (VarList vl : impl.getOutParams()) {
			BoogieType type = typeManager.resolveType(vl.getType());
			for (String id : vl.getIdentifiers()) {
				if (i >= procOutParams.length) {
					s_logger.error("Too many output parameters in "+impl);
				} else if (!procOutParams[i++].getType().equals(type)) {
					s_logger.error("Type differs at parameter "+id+" in "+impl);
				}
				allParams.add(new VariableInfo(false, impl, id, type));
			}
		}
		if (i < procOutParams.length)
			s_logger.error("Too few output parameters in "+impl);
		
		varScopes.push(allParams.toArray(new VariableInfo[allParams.size()]));
		
		processBody(impl.getBody());
		
		varScopes.pop();
		typeManager.popTypeScope();
	}

	public boolean process(IElement root) {
		if (root instanceof WrapperNode) {
			Unit unit = (Unit) ((WrapperNode) root).getBacking();
			declaredVars      = new HashMap<String,VariableInfo>();
			declaredFunctions = new HashMap<String,FunctionInfo>();
			declaredProcedures= new HashMap<String,ProcedureInfo>();
			varScopes         = new Stack<VariableInfo[]>();
			// pass1: parse type declarations
			typeManager  = new TypeManager(unit.getDeclarations());
			typeManager.init();
			// pass2: variable, constant and function declarations
			for (Declaration decl: unit.getDeclarations()) {
				if (decl instanceof FunctionDeclaration)
					processFunctionDeclaration((FunctionDeclaration)decl);
				else if (decl instanceof VariableDeclaration)
					processVariableDeclaration((VariableDeclaration)decl);
				else if (decl instanceof ConstDeclaration)
					processConstDeclaration((ConstDeclaration)decl);
			}
				
			// pass3: attributes function definition, axioms, 
			//        procedure declarations, where clauses
			for (Declaration decl: unit.getDeclarations()) {
				typecheckAttributes(decl.getAttributes());
				if (decl instanceof ConstDeclaration)
					checkConstDeclaration((ConstDeclaration) decl);
				else if (decl instanceof FunctionDeclaration)
					processFunctionDefinition((FunctionDeclaration) decl);
				else if (decl instanceof Axiom)
					typecheckExpression(((Axiom)decl).getFormula());
				else if (decl instanceof Procedure)
					processProcedureDeclaration((Procedure) decl);
				else if (decl instanceof VariableDeclaration) {
					/* check where clauses */
					for (VarList vl : ((VariableDeclaration) decl).getVariables()) {
						if (vl.getWhereClause() != null) {
							BoogieType t = typecheckExpression(vl.getWhereClause());
							if (!t.equals(boolType) && !t.equals(errorType))
								s_logger.error("Where clause is not boolean: "+decl);
						}
					}
				}
			}
			// pass4: procedure definitions, implementations
			for (Declaration decl: unit.getDeclarations()) {
				if (decl instanceof Procedure)
					processImplementation((Procedure) decl);
			}
			return false;
		}
		return true;
	}

	//@Override
	public void finish() {
		
	}

	//@Override
	public WalkerOptions getWalkerOptions() {
		/* use standard DFS tree walker */
		return null;
	}

	//@Override
	public void init() {
	}

	@Override
	public boolean performedChanges() {
		// TODO Replace with a decent implementation!
		return getDefaultPerformedChanges();
	}

	@Deprecated
	private boolean getDefaultPerformedChanges() {
		return false;
	}

	
}