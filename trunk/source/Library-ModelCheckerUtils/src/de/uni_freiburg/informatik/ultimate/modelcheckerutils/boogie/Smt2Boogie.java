package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.io.Serializable;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * Maps Boogie variables to the corresponding SMT variables. The SMT variables 
 * are represented by ApplicationTerms that consist of one 0-ary function symbol
 * (which represents a constant).
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Smt2Boogie implements Serializable {

	private static final long serialVersionUID = -4519646474900935398L;

	private final Script m_Script;
	
	private final Map<String, BoogieVar> m_Globals;
	private final Map<String, BoogieVar> m_OldGlobals;
	
	private final Map<IType, Sort> m_type2sort = new HashMap<IType, Sort>();
	private final Map<Sort, IType> m_sort2type = new HashMap<Sort, IType>();
	
	final Map<TermVariable,BoogieVar> m_SmtVar2SmtBoogieVar;
	
	final Map<String,String> m_BoogieFunction2SmtFunction
			= new HashMap<String,String>();
	final Map<String,String> m_SmtFunction2BoogieFunction
			= new HashMap<String,String>();
	
	private final Map<Term, IdentifierExpression> m_SmtTerm2Const;
	
	private final ScopedHashMap<TermVariable, VarList> m_QuantifiedVariables =
			new ScopedHashMap<TermVariable, VarList>();

	
	private int m_freshIdentiferCounter = 0;
	
	private final boolean m_BlackHoleArrays;
	
	
	public Smt2Boogie(Script script, Map<String, BoogieVar> globals, 
									 Map<String, BoogieVar> oldGlobals,
									 boolean blackHoleArrays) {
		m_BlackHoleArrays = blackHoleArrays;
		m_Script = script;
		m_Globals = globals;
		m_OldGlobals = oldGlobals;
		m_SmtVar2SmtBoogieVar = new HashMap<TermVariable,BoogieVar>();
		m_SmtTerm2Const = new HashMap<Term, IdentifierExpression>();
		
		Sort boolSort = m_Script.sort("Bool");
		IType boolType = BoogieType.boolType;
		m_type2sort.put(boolType, boolSort);
		m_sort2type.put(boolSort, boolType);
		Sort intSort = m_Script.sort("Int");
		IType intType = BoogieType.intType;
		m_type2sort.put(intType, intSort);
		m_sort2type.put(intSort, intType);

	}
	

//	/**
//	 * @param boogieVar variable of boogie program
//	 * @return The (unique) SmtTerm that represents {@code varName} in 
//	 * <ul>
//	 *  <li> formulas that denote sets of states,
//	 *  <li> and ranking functions
//	 * </ul>
//	 */
//	public TermVariable getSmtVar(BoogieVar boogieVar) {
//		TermVariable smtVar = m_BoogieVar2SmtVar.get(boogieVar);
//		if (smtVar == null) {
//			Sort sort = getSort(boogieVar.getIType());
//			String name;
//			if (boogieVar.isOldvar()) {
//				name = "old(" + boogieVar.getIdentifier() + ")";
//			}
//			else {
//				name = (boogieVar.getProcedure() == null ?
//						"" : boogieVar.getProcedure() + "_" )
//						+ boogieVar.getIdentifier();
//			}
//			smtVar = m_Script.variable(name, sort);
//			m_BoogieVar2SmtVar.put(boogieVar,smtVar);
//			m_SmtVar2SmtBoogieVar.put(smtVar,boogieVar);
//		}
//		return smtVar;
//	}
	
	
	public Script getScript() {
		return m_Script;
	}
	
	public IdentifierExpression getConstDeclaration(Term term) {
		return m_SmtTerm2Const.get(term);
	}

	public BoogieVar getBoogieVar(TermVariable smtVar) {
		return m_SmtVar2SmtBoogieVar.get(smtVar);
	}
	
	/**
	 * Return global variables;
	 */
	public Map<String, BoogieVar> getGlobals() {
		return Collections.unmodifiableMap(m_Globals);
	}
	
	/**
	 * Return global oldvars;
	 */
	public Map<String, BoogieVar> getOldGlobals() {
		return Collections.unmodifiableMap(m_OldGlobals);
	}

	public IType getType(Sort sort) {
		IType type = m_sort2type.get(sort);
		if (type == null) {
			//TODO Matthias: The following special treatment of arrays is only
			//necessary if we allow to backtranslate to arrays that do not occur
			//in the boogie program. Might be useful if we allow store
			// expressions in interpolants and don't replace them by select
			// expressions.
			if (sort.isArraySort()) {
				assert sort.getName().equals("Array");
				Sort indexSort = sort.getArguments()[0];
				Sort valueSort = sort.getArguments()[1];
				BoogieType[] indexTypes = { (BoogieType) getType(indexSort) };
				BoogieType valueType = (BoogieType) getType(valueSort);
				type = BoogieType.createArrayType(0, indexTypes, valueType);
			} else {
				throw new IllegalArgumentException("Unknown sort" + sort);
			}
		}
		return type;
	}
	
	
	/**
	 * Return the SMT sort for a boogie type.
	 * If the (type,sort) pair is not already stored in m_type2sort the 
	 * corresponding sort is constructed and the pair (sort, type) is added to
	 * m_sort2type which is used for a backtranslation.
	 * @param astNode astNode for which Sort is computed 
	 */
	public Sort getSort(IType type, ASTNode astNode) {
		if (m_type2sort.containsKey(type)) {
			return m_type2sort.get(type);
		} else {
			return constructSort(type, astNode);
		}
	}
		
		
		
	/**
	 * Construct the SMT sort for a boogie type.
	 * Store the (type, sort) pair in m_type2sort. Store the (sort, type) pair 
	 * in m_sort2type.
	 * @param astNode astNode for which Sort is computed 
	 */
	private Sort constructSort(IType boogieType, ASTNode astNode) {
		Sort result;
		if (boogieType instanceof PrimitiveType) {
			if (boogieType.equals(PrimitiveType.boolType)) {
				result = m_Script.sort("Bool");
			}
			else if (boogieType.equals(PrimitiveType.intType)) {
				result = m_Script.sort("Int");
			}
			else if (boogieType.equals(PrimitiveType.realType)) {
				result = m_Script.sort("Real");
			}
			else {
				throw new IllegalArgumentException("Unsupported primitive type");
			}
		}
		else if (boogieType instanceof ArrayType) {
			ArrayType arrayType = (ArrayType) boogieType;
			Sort rangeSort = constructSort(arrayType.getValueType(), astNode);
			if (m_BlackHoleArrays) {
				result = rangeSort;
			} else {
				try {
					for (int i = arrayType.getIndexCount() - 1; i >= 1; i--) {
						Sort sorti = constructSort(arrayType.getIndexType(i), astNode);
						rangeSort = m_Script.sort("Array", sorti, rangeSort);
					}
					Sort domainSort = constructSort(arrayType.getIndexType(0), astNode);
					result = m_Script.sort("Array", domainSort,rangeSort);
				}
				catch (SMTLIBException e) {
					if (e.getMessage().equals("Sort Array not declared")) {
						reportUnsupportedSyntax(astNode, "Solver does not support arrays");
						throw e;
					}
					else {
						throw new AssertionError(e);
					}
				}
			}
		}
		else if (boogieType instanceof ConstructedType) {
			ConstructedType constructedType = (ConstructedType) boogieType;
			String name = constructedType.getConstr().getName();
			result = m_Script.sort(name);
		} else {
			throw new IllegalArgumentException("Unsupported type" + boogieType);
		}
		m_type2sort.put(boogieType, result);
		m_sort2type.put(result, boogieType);
		return result;
	}

	
	
	
	
	public void declareConst(String id, Term term) {
		IdentifierExpression ie;
		ie = new IdentifierExpression(null, getType(term.getSort()),id);
		m_SmtTerm2Const.put(term, ie);
	}
	
	
	
	
	
	
	
	
	Set<IdentifierExpression> m_freeVariables = new HashSet<IdentifierExpression>();
	
	private String getFreshIdenfier() {
		return "freshIdentifier" + m_freshIdentiferCounter++;
	}
	
	public Expression translate(Term term) {
		Expression result;
		if (term instanceof AnnotatedTerm) {
			result = translate( (AnnotatedTerm) term);
		}else if (term instanceof ApplicationTerm) {
			return translate( (ApplicationTerm) term);
		}else if (term instanceof ConstantTerm) {
			result = translate( (ConstantTerm) term);
		}else if (term instanceof LetTerm) {
			result = translate( (LetTerm) term);
		}else if (term instanceof QuantifiedFormula) {
			result = translate( (QuantifiedFormula) term);
		}else if (term instanceof TermVariable) {
			result = translate( (TermVariable) term);
		}else {
			throw new UnsupportedOperationException("unknown kind of Term");
		}
		assert (result != null);
		return result;
	}
	
	private Expression translate(AnnotatedTerm term) {
		throw new UnsupportedOperationException(
					"annotations not supported yet" + term);
	}
	
	private Expression translate(ApplicationTerm term) {
		FunctionSymbol symb = term.getFunction();
		IType type = getType(symb.getReturnSort());
		Term[] termParams = term.getParameters();
		if (symb.isIntern() && symb.getName().equals("select")) {
			return translateSelect(term);
		} else if (symb.isIntern() && symb.getName().equals("store")) {
			return translateStore(term);
		}
		Expression[] params = new Expression[termParams.length];
		for (int i=0; i<termParams.length; i++) {
			params[i] = translate(termParams[i]);
		}
		if (symb.getParameterCount() == 0) {
			if (term == m_Script.term("true")) {
				IType booleanType = getType(m_Script.sort("Bool"));
				return new BooleanLiteral(null, booleanType, true);
			}
			if (term == m_Script.term("false")) {
				IType booleanType = getType(m_Script.sort("Bool"));
				return new BooleanLiteral(null, booleanType, false);
			}
			IdentifierExpression ie = getConstDeclaration(term);
			if (ie == null) {
				throw new IllegalArgumentException();
			}
			else {
				return ie;
			}
		} else if (symb.getName().equals("ite")) {
				return new IfThenElseExpression(null, type, params[0], params[1], params[2]); 
		} else if (symb.isIntern()) {
			if (symb.getParameterCount() == 1) {
				if (symb.getName().equals("not")) {
					Expression param = translate(term.getParameters()[0]);
					return new UnaryExpression(null, type, de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator.LOGICNEG,
							param);
				} else if (symb.getName().equals("-")) {
					Expression param = translate(term.getParameters()[0]);
					return new UnaryExpression(null, type, de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator.ARITHNEGATIVE,
							param);
				}else {
					throw new IllegalArgumentException("unknown symbol " + symb);
				}
			}
			else {
				if (symb.getName().equals("xor")) {
					return xor(params);
				}
				Operator op = getBinaryOperator(symb);
				if (symb.isLeftAssoc()) {
					return leftAssoc(op, type, params);
				} else if (symb.isRightAssoc()) {
					return rightAssoc(op, type, params);
				} else if (symb.isChainable()) {
					return chainable(op, type, params);
				} else if (symb.isPairwise()) {
					return pairwise(op, type, params);
				} else {
					throw new UnsupportedOperationException("don't know symbol" +
							" which is neither leftAssoc, rightAssoc, chainable, or pairwise.");
				}
			}
		} else if (m_SmtFunction2BoogieFunction.containsKey(symb.getName())) {
			String identifier = m_SmtFunction2BoogieFunction.get(symb.getName());
			Expression[] arguments = new Expression[termParams.length];
			for (int i=0; i<termParams.length; i++) {
				arguments[i] = translate(termParams[i]);
			}
			return new FunctionApplication(null,type, identifier, arguments); 
		} else {
			throw new UnsupportedOperationException("translation of " + symb + 
					" not yet implemented, please contact Matthias");
		}
	}
	
	private ArrayStoreExpression translateStore(ApplicationTerm term) {
		Expression array = translate(term.getParameters()[0]);
		Expression index = translate(term.getParameters()[1]);
		Expression[] indices = { index };
		Expression value = translate(term.getParameters()[2]);
		return new ArrayStoreExpression(null, array, indices, value);
	}

	/**
	 * Translate a single select expression to an ArrayAccessExpression.
	 * If we have nested select expressions this leads to nested
	 * ArrayAccessExpressions, hence arrays which do not occur in the boogie
	 * program. 
	 */
	private ArrayAccessExpression translateSelect(ApplicationTerm term) {
		Expression array = translate(term.getParameters()[0]);
		Expression index = translate(term.getParameters()[1]);
		Expression[] indices = { index };
		return new ArrayAccessExpression(null, array, indices);
	}

	/**
	 * Translate a nested sequence of select expressions to a single 
	 * ArrayAccessExpression. (see translateSelect why this might be useful) 
	 */
	private ArrayAccessExpression translateArray(ApplicationTerm term) {
		List<Expression> reverseIndices = new ArrayList<Expression>();
		while (term.getFunction().getName().equals("select") && 
				(term.getParameters()[0] instanceof ApplicationTerm)) {
			assert (term.getParameters().length == 2);
			Expression index = translate(term.getParameters()[1]);
			reverseIndices.add(index);
			term = (ApplicationTerm) term.getParameters()[0];
		}
		assert (term.getParameters().length == 2);
		Expression index = translate(term.getParameters()[1]);
		reverseIndices.add(index);

		Expression array = translate(term.getParameters()[0]);
		Expression[] indices = new Expression[reverseIndices.size()];
		for (int i=0; i<indices.length; i++) {
			indices[i] = reverseIndices.get(indices.length-1-i);
		}
		return new ArrayAccessExpression(null, array, indices);
	}


	private Expression translate(ConstantTerm term) {
		Object value = term.getValue();
		if (value instanceof String) {
			IType type = getType(term.getSort());
			return new StringLiteral(null, type, value.toString());
			
		} else if (value instanceof BigInteger) {
			IType type = getType(term.getSort());
			return new IntegerLiteral(null, type, value.toString());
			
		} else if (value instanceof BigDecimal) {
			IType type = getType(term.getSort());
			return new RealLiteral(null, type, value.toString());
		} else {
			throw new UnsupportedOperationException("unknown kind of Term");
		}
	}
	
	private Expression translate(LetTerm term) {
		throw new IllegalArgumentException("unlet Term first");
	}
	
	private Expression translate(QuantifiedFormula term) {
		m_QuantifiedVariables.beginScope();
		VarList[] parameters = new VarList[term.getVariables().length];
		int offset = 0;
		for (TermVariable tv : term.getVariables()) {
			IType type = getType(tv.getSort());
			String[] identifiers = { tv.getName() };
			//FIXME: Matthias: How can I get the ASTType of type?
			VarList varList = new VarList(null, identifiers, null);
			parameters[offset] = varList;
			m_QuantifiedVariables.put(tv, varList);
			offset++;
		}
		IType type = getType(term.getSort());
		assert (term.getQuantifier() == QuantifiedFormula.FORALL || 
							term.getQuantifier() == QuantifiedFormula.EXISTS);
		boolean isUniversal = term.getQuantifier() == QuantifiedFormula.FORALL;
		String[] typeParams = new String[0];
		Attribute[] attributes;
		Term subTerm = term.getSubformula();
		if (subTerm instanceof AnnotatedTerm) {
				assert ((AnnotatedTerm) subTerm).getAnnotations()[0].getKey().equals(":pattern");
			Annotation[] annotations = ((AnnotatedTerm) subTerm).getAnnotations();
			//FIXME: does not have to be the case, allow several annotations
			assert (annotations.length == 1) : "expecting only one annotation at a time";
			Annotation annotation = annotations[0];
			Object value = annotation.getValue();
			assert (value instanceof Term[]) : "expecting Term[]" + value;
			Term[] pattern = (Term[]) value;
			subTerm = ((AnnotatedTerm) subTerm).getSubterm();
			Expression[] triggers = new Expression[pattern.length];
			for (int i=0; i<pattern.length; i++) {
				triggers[i] = translate(pattern[i]);
			}
			Trigger trigger = new Trigger(null, triggers);
			attributes = new Attribute[1];
			attributes[0] = trigger;
		} else {
			attributes = new Attribute[0];			
		}
		Expression subformula = translate(subTerm);
		QuantifierExpression result = new QuantifierExpression(null, type, 
					isUniversal, typeParams, parameters, attributes, subformula);
		m_QuantifiedVariables.endScope();
		return result;
	}
	
	private Expression translate(TermVariable term) {
		Expression result;
		IType type = getType(term.getSort());
		if (m_QuantifiedVariables.containsKey(term)) {
			VarList varList = m_QuantifiedVariables.get(term);
			assert varList.getIdentifiers().length == 1;
			String id = varList.getIdentifiers()[0];
			result = new IdentifierExpression(null, type, id);
		} else if (getBoogieVar(term) == null) {
			//Case where term contains some auxilliary variable that was 
			//introduced during model checking. 
			//TODO: Matthias: I think we want closed expressions, we should
			//quantify auxilliary variables
			result = new IdentifierExpression(null, type, getFreshIdenfier());
			m_freeVariables.add((IdentifierExpression) result);
		}
		else {
			BoogieVar var = getBoogieVar(term);
			result = new IdentifierExpression(null, type, var.getIdentifier());
			if (var.isOldvar()) {
				assert(var.isGlobal());
				result = new UnaryExpression(null, type, UnaryExpression.Operator.OLD, result);
			}
		}
		return result;
	}


	private Operator getBinaryOperator(FunctionSymbol symb) {
		if (symb.getName().equals("and")) {
			return Operator.LOGICAND;
		}
		else if (symb.getName().equals("or")) {
			return Operator.LOGICOR;
		}
		else if (symb.getName().equals("=>")) {
			return Operator.LOGICIMPLIES;
		}
		else if (symb.getName().equals("=") && 
				symb.getParameterSort(0).getName().equals("bool")) {
			return Operator.LOGICIFF;
		}
		else if (symb.getName().equals("=")) {
			return Operator.COMPEQ;
		}
		else if (symb.getName().equals("distinct")) {
			return Operator.COMPNEQ;
		}
		else if (symb.getName().equals("<=")) {
			return Operator.COMPLEQ;
		}
		else if (symb.getName().equals(">=")) {
			return Operator.COMPGEQ;
		}
		else if (symb.getName().equals("<")) {
			return Operator.COMPLT;
		}
		else if (symb.getName().equals(">")) {
			return Operator.COMPGT;
		}
		else if (symb.getName().equals("+")) {
			return Operator.ARITHPLUS;
		}
		else if (symb.getName().equals("-")) {
			return Operator.ARITHMINUS;
		}
		else if (symb.getName().equals("*")) {
			return Operator.ARITHMUL;
		}
		else if (symb.getName().equals("/")) {
			return Operator.ARITHDIV;
		}
		else if (symb.getName().equals("div")) {
			return Operator.ARITHDIV;
		}
		else if (symb.getName().equals("mod")) {
			return Operator.ARITHMOD;
		}
		else if (symb.getName().equals("ite")) {
			throw new UnsupportedOperationException("not yet implemented");
		}
		else if (symb.getName().equals("abs")) {
			throw new UnsupportedOperationException("not yet implemented");
		}		
		else {
			throw new IllegalArgumentException("unknown symbol " + symb);
		}
	}

	private Expression leftAssoc(Operator op, IType type, Expression[] params) {
		Expression result = params[0];
		for (int i=0; i<params.length-1; i++) {
			result = new BinaryExpression(null, type, op, result, params[i+1]);
		}
		return result;
	}
	
	
	private Expression rightAssoc(Operator op, IType type, Expression[] params) {
		Expression result = params[params.length-1];
		for (int i=params.length-1; i>0; i--) {
			result = new BinaryExpression(null, type, op, params[i-1],result);
		}
		return result;
	}
	
	private Expression chainable(Operator op, IType type, Expression[] params) {
		assert(type == BoogieType.boolType);
		Expression result = new BinaryExpression(null, type, op, params[0], params[1]);
		Expression chain;
		for (int i=1;i<params.length-1; i++) {
			chain = new BinaryExpression(null, type, op, params[i], params[i+1]);
			result = new BinaryExpression(null, BoogieType.boolType, Operator.LOGICAND, result, chain);
		}
		return result;
	}

	private Expression pairwise(Operator op, IType type, Expression[] params) {
		assert(type == BoogieType.boolType);
		Expression result = new BinaryExpression(null, type, op, params[0], params[1]);
		Expression neq;
			for (int i=0; i<params.length-1; i++) {
				for (int j=i+1; j<params.length-1; j++) {
					if (i==0 && j==1) {
						continue;
					}
					neq = new BinaryExpression(null, type, op, params[j], params[j+1]);
					result = new BinaryExpression(null, BoogieType.boolType, Operator.LOGICAND, result, neq);
				}
			}
		return result;
	}
	
	
	private Expression xor(Expression[] params) {
		IType type = BoogieType.boolType;
		Operator iff = Operator.LOGICIFF;
		UnaryExpression.Operator neg = UnaryExpression.Operator.LOGICNEG;
		Expression result = params[0];
		for (int i=0; i<params.length-1; i++) {
			result = new BinaryExpression(null, type, iff, params[i+1],result);
			result = new UnaryExpression(null, type, neg, result);
		}
		return result;
	}
	
	void reportUnsupportedSyntax(ASTNode astNode, String longDescription) {
		SyntaxErrorResult<?> result = new SyntaxErrorResult(null,
				Activator.s_PLUGIN_NAME,
				UltimateServices.getInstance().getTranslatorSequence(),
				astNode.getLocation(), SyntaxErrorType.UnsupportedSyntax);
		result.setLongDescription(longDescription);
		UltimateServices.getInstance().reportResult("Smt2Boogie", result);
		UltimateServices.getInstance().cancelToolchain();
	}


}
