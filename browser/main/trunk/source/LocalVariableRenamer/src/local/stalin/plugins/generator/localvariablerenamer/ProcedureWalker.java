package local.stalin.plugins.generator.localvariablerenamer;

import local.stalin.model.IType;
import local.stalin.model.boogie.ast.ASTType;
import local.stalin.model.boogie.ast.ArrayAccessExpression;
import local.stalin.model.boogie.ast.ArrayLHS;
import local.stalin.model.boogie.ast.ArrayStoreExpression;
import local.stalin.model.boogie.ast.AssertStatement;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Attribute;
import local.stalin.model.boogie.ast.BinaryExpression;
import local.stalin.model.boogie.ast.Body;
import local.stalin.model.boogie.ast.BooleanLiteral;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.EnsuresSpecification;
import local.stalin.model.boogie.ast.Expression;
import local.stalin.model.boogie.ast.FunctionApplication;
import local.stalin.model.boogie.ast.GotoStatement;
import local.stalin.model.boogie.ast.HavocStatement;
import local.stalin.model.boogie.ast.IdentifierExpression;
import local.stalin.model.boogie.ast.IfThenElseExpression;
import local.stalin.model.boogie.ast.IntegerLiteral;
import local.stalin.model.boogie.ast.Label;
import local.stalin.model.boogie.ast.LeftHandSide;
import local.stalin.model.boogie.ast.LoopInvariantSpecification;
import local.stalin.model.boogie.ast.ModifiesSpecification;
import local.stalin.model.boogie.ast.NamedAttribute;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.QuantifierExpression;
import local.stalin.model.boogie.ast.RequiresSpecification;
import local.stalin.model.boogie.ast.ReturnStatement;
import local.stalin.model.boogie.ast.Specification;
import local.stalin.model.boogie.ast.Statement;
import local.stalin.model.boogie.ast.Trigger;
import local.stalin.model.boogie.ast.UnaryExpression;
import local.stalin.model.boogie.ast.VarList;
import local.stalin.model.boogie.ast.VariableDeclaration;
import local.stalin.model.boogie.ast.VariableLHS;

/**
 * Walk through a procedure to obtain a deep copy of the procedure. Extend this
 * class and override methods to obtain a modified copy of the procedure.
 * @author heizmann@informatik.uni-freiburg.de
 */


public class ProcedureWalker {
	

	public Procedure walkProcedure(Procedure proc) {
		if (proc==null) {
			return null;
		}
		else {
		}
			String filename = proc.getFilename();
			
			int lineNr = proc.getLineNr();
			
			Attribute[] attributes = proc.getAttributes();
			Attribute[] newAttributes;
			if (attributes == null) {
				newAttributes = null;
			}
			else {
				newAttributes = new Attribute[attributes.length];
				for (int i=0;i<attributes.length;i++) {
					newAttributes[i] = walkAttribute(attributes[i]);
				}
			}
			
			String identifier = proc.getIdentifier();
			
			String[] typeParams = proc.getTypeParams();
			
			VarList[] inParams = proc.getInParams();
			VarList[] newInParams;
			if (inParams == null) {
				newInParams = null;
			}
			else {
				newInParams = new VarList[inParams.length];
				for (int i=0;i<inParams.length;i++) {
					newInParams[i] = walkVarList(inParams[i]);
				}
			}
			
			VarList[] outParams = proc.getOutParams();
			VarList[] newOutParams;
			if (outParams == null) {
				newOutParams = null;
			}
			else {
				newOutParams = new VarList[outParams.length];
				for (int i=0;i<outParams.length;i++) {
					newOutParams[i] = walkVarList(outParams[i]);
				}
			}
			
			Specification[] specification = proc.getSpecification();
			Specification[] newSpecification;
			if (specification == null) {
				newSpecification = null;
			}
			else {
				newSpecification = new Specification[specification.length];
				for (int i=0;i<specification.length;i++) {
					newSpecification[i] = walkSpecification(specification[i]);
				}
			}
						
			Body body = walkBody(proc.getBody());
			
			return new Procedure(filename,lineNr,newAttributes,identifier,
					typeParams,newInParams,newOutParams,newSpecification,body);
	}



////////////////////////////////////////////////////////////////////////////////
	//Specification walkers
	public Specification walkSpecification(Specification specification) {
		if (specification == null) {
			return null;
		}
		else if (specification instanceof EnsuresSpecification) {
			specification = walkEnsuresSpecification((EnsuresSpecification)specification);
		}
		else if (specification instanceof LoopInvariantSpecification) {
			specification = walkLoopInvariantSpecification((LoopInvariantSpecification)specification);
		}
		else if (specification instanceof ModifiesSpecification) {
			specification = walkModifiesSpecification((ModifiesSpecification)specification);
		}
		else if (specification instanceof RequiresSpecification) {
			specification = walkRequiresSpecification((RequiresSpecification)specification);
		}
		else {
			throw new IllegalArgumentException();
		}
		return specification;
	}

	public Specification walkEnsuresSpecification(EnsuresSpecification specification) {
		if (specification == null) {
			return null;
		}
		else {
			String filename = specification.getFilename();
			int lineNr = specification.getLineNr();
			boolean isFree = specification.isFree();
			Expression formula = walkExpression(specification.getFormula());
			return new EnsuresSpecification(filename, lineNr, isFree, formula);
		}
	}

	public Specification walkLoopInvariantSpecification(LoopInvariantSpecification specification) {
		//TODO
		return specification;
	}

	public Specification walkModifiesSpecification(ModifiesSpecification specification) {
		//TODO
		return specification;
	}

	public Specification walkRequiresSpecification(RequiresSpecification specification) {
		if (specification == null) {
			return null;
		}
		else {
			String filename = specification.getFilename();
			int lineNr = specification.getLineNr();
			boolean isFree = specification.isFree();
			Expression formula = walkExpression(specification.getFormula());
			return new RequiresSpecification(filename, lineNr, isFree, formula);
		}
	}
	

////////////////////////////////////////////////////////////////////////////////
	//Attribute walkers
	public Attribute walkAttribute(Attribute attribute) {
		if (attribute==null) {
			return null;
		}
		else if (attribute instanceof NamedAttribute) {
			return walkNamedAttribute((NamedAttribute)attribute);
		}
		else if (attribute instanceof Trigger) {
			return  walkTrigger((Trigger)attribute);
		}
		else {
			throw new IllegalArgumentException();
		}
	
	}
	
	public Attribute walkNamedAttribute(NamedAttribute attribute) {
		if (attribute == null) {
			return null;
		}
		else {
			String name = attribute.getName();
			Expression[] values = attribute.getValues();
			Expression[] newValues;
			if (values == null) {
				newValues = null;
			}
			else {
				newValues = new Expression[values.length];
				for (int i=0;i<values.length;i++) {
					newValues[i] = walkExpression(values[i]);
				}
			}
			return new NamedAttribute(name, newValues);
		}
	}
	
	public Attribute walkTrigger(Trigger attribute) {
		if (attribute == null) {
			return null;
		}
		else {
			Expression[] triggers = attribute.getTriggers();
			Expression[] newTriggers;
			if (triggers == null) {
				newTriggers = null;
			}
			else {
				newTriggers = new Expression[triggers.length];
				for (int i=0;i<triggers.length;i++) {
					newTriggers[i] = walkExpression(triggers[i]);
				}
			}
			return new Trigger(newTriggers);
		}
	}

	
////////////////////////////////////////////////////////////////////////////////
	// expression walkers
	public Expression walkExpression(Expression formula) {
		if (formula == null) {
			return null;
		}
		else if (formula instanceof ArrayAccessExpression) {
			return walkArrayAccessExpression((ArrayAccessExpression)formula);
		}
		else if (formula instanceof ArrayStoreExpression) {
			return walkArrayStoreExpression((ArrayStoreExpression)formula);
		}
		else if (formula instanceof BinaryExpression) {
			return walkBinaryExpression((BinaryExpression)formula);
		}
		else if (formula instanceof BooleanLiteral) {
			return walkBooleanLiteral((BooleanLiteral)formula);
		}
		else if (formula instanceof FunctionApplication) {
			return walkFunctionApplication((FunctionApplication)formula);
		}
		else if (formula instanceof IdentifierExpression) {
			return walkIdentifierExpression((IdentifierExpression)formula);
		}
		else if (formula instanceof IfThenElseExpression) {
			return walkIfThenElseExpression((IfThenElseExpression)formula);
		}
		else if (formula instanceof IntegerLiteral) {
			return walkIntegerLiteral((IntegerLiteral)formula);
		}
		else if (formula instanceof QuantifierExpression) {
			return walkQuantifierExpression((QuantifierExpression)formula);
		}
		else if (formula instanceof UnaryExpression) {
			return walkUnaryExpression((UnaryExpression)formula);
		}
		else {
			//TODO some cases missing
			throw new IllegalArgumentException();
		}
	}	
	

	public Expression walkArrayAccessExpression(ArrayAccessExpression formula) {
		IType type = formula.getType();
		Expression array = walkExpression(formula.getArray());
		Expression[] indices = formula.getIndices();
		Expression[] newIndices;
		if (indices == null) {
			newIndices = null;
		}
		else {
			newIndices = new Expression[indices.length];
			for (int i=0;i<indices.length;i++) {
				newIndices[i] = walkExpression(indices[i]);
			}
		}
		return new ArrayAccessExpression(type,array, newIndices);
	}

	
	public Expression walkArrayStoreExpression(ArrayStoreExpression formula) {
		IType type = formula.getType();
		Expression array = walkExpression(formula.getArray());
		Expression[] indices = formula.getIndices();
		Expression[] newIndices;
		if (indices == null) {
			newIndices = null;
		}
		else {
			newIndices = new Expression[indices.length];
			for (int i=0;i<indices.length;i++) {
				newIndices[i] = walkExpression(indices[i]);
			}
		}
		Expression value = walkExpression(formula.getValue());
		return new ArrayStoreExpression(type, array, newIndices, value);
	}


	public Expression walkBinaryExpression(BinaryExpression formula) {
		IType type = walkIType(formula.getType());
		BinaryExpression.Operator operator = formula.getOperator();
		Expression left = walkExpression(formula.getLeft());
		Expression right = walkExpression(formula.getRight());
		return new BinaryExpression(type, operator, left, right);
	}


	public Expression walkBooleanLiteral(BooleanLiteral formula) {
		return formula;
	}
	
	
	public Expression walkFunctionApplication(FunctionApplication formula) {
		IType type = formula.getType();
		String identifier = formula.getIdentifier();
		Expression[] arguments = formula.getArguments();
		Expression[] newArguments;
		if (arguments == null) {
			newArguments = null;
		}
		else {
			newArguments = new Expression[arguments.length];
			for (int i=0;i<arguments.length;i++) {
				newArguments[i] = walkExpression(arguments[i]);
			}
		}
		return new FunctionApplication(type, identifier, newArguments);
	}


	public Expression walkIdentifierExpression(IdentifierExpression formula) {
		IType type = formula.getType();
		String identifier = walkVariableIdentifier(formula.getIdentifier());
		return new IdentifierExpression(type,identifier);
	}
	
	
	public Expression walkIfThenElseExpression(IfThenElseExpression formula) {
		IType type = formula.getType();
		Expression condition = walkExpression(formula.getCondition());
		Expression thenPart = walkExpression(formula.getThenPart());
		Expression elsePart = walkExpression(formula.getElsePart());
		return new IfThenElseExpression(type,condition,thenPart,elsePart);
	}


	public Expression walkIntegerLiteral(IntegerLiteral formula) {
		return formula;
	}
	

	public Expression walkQuantifierExpression(QuantifierExpression formula) {
		IType type = formula.getType();
		boolean isUniversal = formula.isUniversal();
		String[] typeParams = formula.getTypeParams();
		VarList[] parameters = formula.getParameters();
		VarList[] newParameters;
		if (parameters == null) {
			newParameters = null;
		}
		else {
			newParameters = new VarList[parameters.length];
			for (int i=0; i<parameters.length; i++) {
				newParameters[i] = walkVarList(parameters[i]);
			}
		}
		Attribute[] attributes = formula.getAttributes();
		Attribute[] newAttributes;
		if (attributes == null) {
			newAttributes = null;
		}
		else {
			newAttributes = new Attribute[attributes.length];
			for (int i=0; i<attributes.length; i++) {
				newAttributes[i] = walkAttribute(attributes[i]);
			}
		}
		Expression subformula = walkExpression(formula.getSubformula());
		return new QuantifierExpression(type, isUniversal, typeParams, newParameters, newAttributes, subformula);
	}


	public Expression walkUnaryExpression(UnaryExpression formula) {
		IType type = walkIType(formula.getType());
		UnaryExpression.Operator operator = formula.getOperator();
		Expression expr = walkExpression(formula.getExpr());
		return new UnaryExpression(type, operator, expr);
	}


	
////////////////////////////////////////////////////////////////////////////////
	// IType walker
	public IType walkIType(IType type) {
		return type;
	}
	


////////////////////////////////////////////////////////////////////////////////
	// VarList walker
	public VarList walkVarList(VarList varList) {
		if (varList==null) {
			return null;
		}
		else {
			String[] identifiers = varList.getIdentifiers();
			String[] newIdentifiers;
			if (identifiers == null) {
				newIdentifiers = null;
			}
			else {
				newIdentifiers = new String[identifiers.length];
				for (int i=0;i<identifiers.length;i++) {
					newIdentifiers[i] = walkVariableIdentifier(identifiers[i]);
				}
			}
			ASTType type = varList.getType();
			Expression whereClause = walkExpression(varList.getWhereClause());
			return new VarList(newIdentifiers, type, whereClause);
		}
	}
	
	
	
////////////////////////////////////////////////////////////////////////////////
	// Body walker
	public Body walkBody(Body body) {
		if (body == null){
			return null;
		}
		else {
			VariableDeclaration[] localVars = body.getLocalVars();
			if (localVars != null) {
				for (int i=0;i<localVars.length;i++) {
					localVars[i] = walkVariableDeclaration(localVars[i]);
				}
			}
			Statement[] block = body.getBlock();
			if (block != null) {
				for (int i=0;i<block.length;i++) {
					block[i] = walkStatement(block[i]);
				}
			}
			return new Body(localVars, block);
		}			
	}

	

////////////////////////////////////////////////////////////////////////////////
	// VariableDeclaration walker
	public VariableDeclaration walkVariableDeclaration(VariableDeclaration variableDeclaration) {
		if (variableDeclaration == null) {
			return null;
		}
		else {
			String filename = variableDeclaration.getFilename();
			
			int lineNr = variableDeclaration.getLineNr();
			
			Attribute[] attributes = variableDeclaration.getAttributes();
			Attribute[] newAttributes;
			if (attributes == null) {
				newAttributes = null;
			}
			else {
				newAttributes = new Attribute[attributes.length];
				for (int i=0; i<attributes.length; i++) {
					newAttributes[i] = walkAttribute(attributes[i]);
				}
			}
			
			VarList[] variables = variableDeclaration.getVariables();
			VarList[] newVariables;
			if (variables == null) {
				newVariables = null;
			}
			else {
				newVariables = new VarList[variables.length];
				for (int i=0; i<variables.length; i++) {
					newVariables[i] = walkVarList(variables[i]);
				}
			}
			
			return new VariableDeclaration(filename, lineNr, newAttributes, newVariables);
		}
	}

	
////////////////////////////////////////////////////////////////////////////////
	//Statement walkers
	public Statement walkStatement(Statement statement) {
		if (statement == null) {
			return null;
		}
		else if (statement instanceof AssertStatement) {
			return walkAssertStatement((AssertStatement) statement);
		}
		else if (statement instanceof AssignmentStatement) {
			return walkAssignmentStatement((AssignmentStatement) statement);
		}
		else if (statement instanceof AssumeStatement) {
			return walkAssumeStatement((AssumeStatement) statement);
		}
		else if (statement instanceof CallStatement) {
			return walkCallStatement((CallStatement) statement);
		}
		else if (statement instanceof GotoStatement) {
			return walkGotoStatement((GotoStatement) statement);
		}
		else if (statement instanceof HavocStatement) {
			return walkHavocStatement((HavocStatement) statement);
		}
		else if (statement instanceof Label) {
			return walkLabel((Label) statement);
		}
		else if (statement instanceof ReturnStatement) {
			return walkReturnStatement((ReturnStatement) statement);
		}
		else {
			throw new IllegalArgumentException();
		}
	}


	public Statement walkAssertStatement(AssertStatement statement) {
		String filename = statement.getFilename();
		int lineNr = statement.getLineNr();
		Expression formula = walkExpression(statement.getFormula());
		return new AssertStatement(filename, lineNr, formula);
	}


	public Statement walkAssignmentStatement(AssignmentStatement statement) {
		String filename = statement.getFilename();
		int lineNr = statement.getLineNr();
		LeftHandSide[] lhs = statement.getLhs();
		LeftHandSide[] newLhs;
		if (lhs == null) {
			newLhs = null;
		}
		else {
			newLhs = new LeftHandSide[lhs.length];
			for (int i=0;i<lhs.length;i++) {
				newLhs[i] = walkLeftHandSide(lhs[i]);
			}
		}	
		Expression[] rhs = statement.getRhs();
		Expression[] newRhs;
		if (rhs == null) {
			newRhs = null;
		}
		else {
			newRhs = new Expression[rhs.length];
			for (int i=0;i<rhs.length;i++) {
				newRhs[i] = walkExpression(rhs[i]);
			}
		}
		return new AssignmentStatement(filename, lineNr, newLhs, newRhs);
	}


	public Statement walkAssumeStatement(AssumeStatement statement) {
		String filename = statement.getFilename();
		int lineNr = statement.getLineNr();
		Expression formula = walkExpression(statement.getFormula());
		return new AssumeStatement(filename, lineNr, formula);
	}


	public Statement walkCallStatement(CallStatement statement) {
		String filename = statement.getFilename();
		int lineNr = statement.getLineNr();
		boolean isForall = statement.isForall();
		String[] lhs = statement.getLhs();
		String[] newLhs;
		if (lhs == null) {
			newLhs = null;
		}
		else {
			newLhs = new String[lhs.length];
			for (int i=0;i<lhs.length;i++) {
				newLhs[i] = walkVariableIdentifier(lhs[i]);
			}
		}
		String methodName = statement.getMethodName();
		Expression[] arguments = statement.getArguments();
		Expression[] newArguments;
		if (arguments == null) {
			newArguments = null;
		}
		else {
			newArguments = new Expression[arguments.length];
			for (int i=0;i<arguments.length;i++) {
				newArguments[i] = walkExpression(arguments[i]);
			}
		}
		return new CallStatement(filename, lineNr, isForall, newLhs, methodName, newArguments);
	}

	public Statement walkGotoStatement(GotoStatement statement) {
		// TODO 
		return statement;
	}

	public Statement walkHavocStatement(HavocStatement statement) {
		String filename = statement.getFilename();
		int lineNr = statement.getLineNr();
		String[] identifiers = statement.getIdentifiers();
		String[] newIdentifiers;
		if (identifiers == null) {
			newIdentifiers = null;
		}
		else {
			newIdentifiers = new String[identifiers.length];
			for (int i=0;i<identifiers.length;i++) {
				newIdentifiers[i] = walkVariableIdentifier(identifiers[i]);
			}
		}
		return new HavocStatement(filename, lineNr, newIdentifiers);
	}

	public Statement walkLabel(Label statement) {
		String filename = statement.getFilename();
		int lineNr = statement.getLineNr();
		String name = statement.getName();
		return new Label(filename, lineNr, name);
	}

	public Statement walkReturnStatement(ReturnStatement statement) {
		String filename = statement.getFilename();
		int lineNr = statement.getLineNr();
		return new ReturnStatement(filename, lineNr);
	}
	
	
	
////////////////////////////////////////////////////////////////////////////////
	//LeftHandSide walker
	public LeftHandSide walkLeftHandSide(LeftHandSide leftHandSide) {
		if (leftHandSide == null) {
			return null;
		}
		else if (leftHandSide instanceof VariableLHS) {
			return walkVariableLHS((VariableLHS)leftHandSide);
		}
		else if (leftHandSide instanceof ArrayLHS) {
			throw new IllegalArgumentException();
		}
		else {
			throw new IllegalArgumentException();
		}
	}


	public LeftHandSide walkVariableLHS(VariableLHS leftHandSide) {
		IType type = leftHandSide.getType(); 
		String identifier = walkVariableIdentifier(leftHandSide.getIdentifier());
		return new VariableLHS(type, identifier);
	}

	
	
////////////////////////////////////////////////////////////////////////////////
	//VariableIdentifier walker
	public String walkVariableIdentifier(String identifier) {
		return identifier;
	}
	
}
