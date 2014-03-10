package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.io.Serializable;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
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
	

	
	final Map<String,String> m_BoogieFunction2SmtFunction
			= new HashMap<String,String>();
	final Map<String,String> m_SmtFunction2BoogieFunction
			= new HashMap<String,String>();
	
	private final Map<Term, IdentifierExpression> m_SmtTerm2Const;
	
	private final ScopedHashMap<TermVariable, VarList> m_QuantifiedVariables =
			new ScopedHashMap<TermVariable, VarList>();

	
	private int m_freshIdentiferCounter = 0;


	private final TypeSortTranslator m_TypeSortTranslator;
	
	private final Boogie2SmtSymbolTable m_Boogie2SmtSymbolTable;
	
	
	public Smt2Boogie(Script script, TypeSortTranslator tsTranslation, 
			Boogie2SmtSymbolTable boogie2SmtSymbolTable) {
		m_Script = script;
		m_TypeSortTranslator = tsTranslation;
		m_Boogie2SmtSymbolTable = boogie2SmtSymbolTable;
		m_SmtTerm2Const = new HashMap<Term, IdentifierExpression>();
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
	
	public IdentifierExpression getConstDeclaration(ApplicationTerm term) {
		BoogieConst boogieConst = m_Boogie2SmtSymbolTable.getBoogieConst(term);
		if (boogieConst == null) {
			throw new AssertionError("no such BoogieConst");
		} else {
			IdentifierExpression result = m_SmtTerm2Const.get(term);
			if (result == null) {
				result = new IdentifierExpression(null, 
						m_TypeSortTranslator.getType(term.getSort()),
						boogieConst.getIdentifier(),
						new DeclarationInformation(StorageClass.GLOBAL, null));
				m_SmtTerm2Const.put(term, result);
			}
			return result;
		}
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
		IType type = m_TypeSortTranslator.getType(symb.getReturnSort());
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
				IType booleanType = m_TypeSortTranslator.getType(m_Script.sort("Bool"));
				return new BooleanLiteral(null, booleanType, true);
			}
			if (term == m_Script.term("false")) {
				IType booleanType = m_TypeSortTranslator.getType(m_Script.sort("Bool"));
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
		IType type = m_TypeSortTranslator.getType(term.getSort());
		if (value instanceof String) {
			return new StringLiteral(null, type, value.toString());
		} else if (value instanceof BigInteger) {
			return new IntegerLiteral(null, type, value.toString());
		} else if (value instanceof BigDecimal) {
			return new RealLiteral(null, type, value.toString());
		} else if (value instanceof Rational) {
			if (term.getSort().getName().equals("Int")) {
				return new IntegerLiteral(null, type, value.toString());
			} else if (term.getSort().getName().equals("Real")) {
				return new RealLiteral(null, type, value.toString());
			} else {
				throw new UnsupportedOperationException("unknown Sort");
			}
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
			IType type = m_TypeSortTranslator.getType(tv.getSort());
			String[] identifiers = { tv.getName() };
			//FIXME: Matthias: How can I get the ASTType of type?
			VarList varList = new VarList(null, identifiers, null);
			parameters[offset] = varList;
			m_QuantifiedVariables.put(tv, varList);
			offset++;
		}
		IType type = m_TypeSortTranslator.getType(term.getSort());
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
		IType type = m_TypeSortTranslator.getType(term.getSort());
		if (m_QuantifiedVariables.containsKey(term)) {
			VarList varList = m_QuantifiedVariables.get(term);
			assert varList.getIdentifiers().length == 1;
			String id = varList.getIdentifiers()[0];
			result = new IdentifierExpression(null, type, id,
					new DeclarationInformation(StorageClass.QUANTIFIED, null));
		} else if (m_Boogie2SmtSymbolTable.getBoogieVar(term) == null) {
			//Case where term contains some auxilliary variable that was 
			//introduced during model checking. 
			//TODO: Matthias: I think we want closed expressions, we should
			//quantify auxilliary variables
			result = new IdentifierExpression(null, type, getFreshIdenfier(),
					new DeclarationInformation(StorageClass.QUANTIFIED, null));
			m_freeVariables.add((IdentifierExpression) result);
		}
		else {
			BoogieVar var = m_Boogie2SmtSymbolTable.getBoogieVar(term);
			result = new IdentifierExpression(null, type, var.getIdentifier(), 
					null /* FIXME: obtain declaration info from bv*/);
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
	



}
