package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridVariableManager;

/**
 * Helper class to convert math expressions to SMT stuff
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridMathHelper {
	
	private enum Operator {
		ADD(1), SUBTRACT(1), MULTIPLY(2), DIVIDE(2), LTEQ(5), GTEQ(5), LT(5), GT(5), EQ(5), DOUBLEEQ(5), AND(4),
		DOUBLEAND(4), OR(3);
		final int precedence;
		
		Operator(int p) {
			precedence = p;
		}
	}
	
	private static Map<String, Operator> mOperators = new HashMap<>();
	static {
		mOperators.put("+", Operator.ADD);
		mOperators.put("-", Operator.SUBTRACT);
		mOperators.put("*", Operator.MULTIPLY);
		mOperators.put("/", Operator.DIVIDE);
		mOperators.put("<=", Operator.LTEQ);
		mOperators.put(">=", Operator.GTEQ);
		mOperators.put("<", Operator.LT);
		mOperators.put(">", Operator.GT);
		mOperators.put("==", Operator.DOUBLEEQ);
		mOperators.put("=", Operator.EQ);
		mOperators.put("&&", Operator.DOUBLEAND);
		mOperators.put("&", Operator.AND);
		mOperators.put("|", Operator.OR);
	}
	
	/**
	 * This function splits a given expression into an array. e.g "x == 5" will return [x,==,5].
	 * 
	 * @param expression
	 * @return
	 */
	public static String[] expressionToArray(String expression) {
		final String regex = "(?<=\\G(\\w+(?!\\w+)|\\+|-|\\/|\\*|\\&|\\||<(?!=)|>(?!=)|<=|>=|==|\\(|\\)))\\s*";
		return expression.split(regex);
		
	}
	
	private static boolean isHigherPrec(String op, String sub) {
		return mOperators.containsKey(sub) && mOperators.get(sub).precedence >= mOperators.get(op).precedence;
	}
	
	/**
	 * Function to convert infix to postfix (Shunting yard algorithm)
	 * 
	 * @param infix
	 * @return
	 */
	public static List<String> postfix(String[] infix) {
		final List<String> output = new ArrayList<>();
		final Deque<String> stack = new LinkedList<>();
		
		for (final String element : infix) {
			// operator
			if (mOperators.containsKey(element)) {
				while (!stack.isEmpty() && isHigherPrec(element, stack.peek()))
					output.add(stack.pop());
				stack.push(element);
				
				// left bracket
			} else if ("(".equals(element)) {
				stack.push(element);
				
				// right bracket
			} else if (")".equals(element)) {
				while (!"(".equals(stack.peek()))
					output.add(stack.pop());
				stack.pop();
				
				// digit
			} else {
				output.add(element);
			}
		}
		
		while (!stack.isEmpty())
			output.add(stack.pop());
		
		return output;
	}
	
	/**
	 * Function to convert a given formula postfix notation as array, into a term.
	 * 
	 * @param postfix
	 * @param script
	 * @param variableManager
	 * @return
	 */
	public static Term postfixToTerm(List<String> postfix, Script script, HybridVariableManager variableManager) {
		/*
		 * 1. Create an empty stack that can hold string values. 2. Scan the postfix expression from left to right 2a.
		 * If operand then push into stack 2b. If operator then 1. Pop first two elements 2. Now make a term of the form
		 * (operand2,operator,operand1)" 3. Push the new term onto stack
		 */
		
		Term term = null;
		final Deque<String> stack = new LinkedList<>();
		final Map<String, Term> strTerm = new HashMap<>();
		for (final String el : postfix) {
			String element = el;
			
			if (isOperator(element)) {
				// & is "and" in SMT
				// == is "=" in SMT
				if ("&".equals(el)) {
					element = "and";
				} else if ("==".equals(el)) {
					element = "=";
				}
				
				final String operand1 = stack.pop();
				final String operand2 = stack.pop();
				final String operator = element;
				final Map<String, TermVariable> outVarTVMap = variableManager.getVar2OutVarTermVariable();
				final Term tmpTerm = checkAndbuildTerm(operand1, operand2, operator, strTerm, outVarTVMap, script);
				
				if (term == null) {
					term = tmpTerm;
					stack.push(term.toString());
					strTerm.put(term.toString(), term);
				} else if (tmpTerm != null) {
					term = tmpTerm;
					stack.push(tmpTerm.toString());
					strTerm.put(tmpTerm.toString(), term);
				} else {
					throw new IllegalStateException("this exception should not happen, ever");
				}
			} else {
				stack.push(element);
			}
		}
		return term;
	}
	
	private static Term checkAndbuildTerm(String operand1, String operand2, String operator, Map<String, Term> strTerm,
			Map<String, TermVariable> outVarTVMap, Script script) {
		// check if the operand already got a term.
		Term tmpTerm;
		if (strTerm.containsKey(operand1) && strTerm.containsKey(operand2)) {
			final Term t1 = strTerm.get(operand1);
			final Term t2 = strTerm.get(operand2);
			tmpTerm = script.term(operator, t2, t1);
		} else if (strTerm.containsKey(operand1) && !strTerm.containsKey(operand2)) {
			final Term t1 = strTerm.get(operand1);
			tmpTerm = buildTerm(t1, operand2, operator, strTerm, outVarTVMap, script);
		} else if (!strTerm.containsKey(operand1) && strTerm.containsKey(operand2)) {
			final Term t2 = strTerm.get(operand2);
			tmpTerm = buildTerm(operand1, t2, operator, strTerm, outVarTVMap, script);
		} else {
			tmpTerm = buildTerm(operand1, operand2, operator, strTerm, outVarTVMap, script);
		}
		return tmpTerm;
	}
	
	private static Term buildTerm(String operand1, Term term2, String operator, Map<String, Term> strTerm,
			Map<String, TermVariable> outVarTVMap, Script script) {
		Term tmpTerm;
		TermVariable tv1;
		// operand 2
		if (outVarTVMap.containsKey(operand1)) {
			tv1 = outVarTVMap.get(operand1);
		} else {
			tv1 = null;
		}
		// build term
		if (tv1 == null) {
			tmpTerm = script.term(operator, term2, script.decimal(operand1));
		} else {
			tmpTerm = script.term(operator, term2, tv1);
		}
		return tmpTerm;
	}
	
	private static Term buildTerm(String operand1, String operand2, String operator, Map<String, Term> strTerm,
			Map<String, TermVariable> outVarTVMap, Script script) {
		Term tmpTerm;
		TermVariable tv1;
		TermVariable tv2;
		// get variables
		// operand 1
		if (outVarTVMap.containsKey(operand1)) {
			tv1 = outVarTVMap.get(operand1);
		} else {
			tv1 = null;
		}
		// operand 2
		if (outVarTVMap.containsKey(operand2)) {
			tv2 = outVarTVMap.get(operand2);
		} else {
			tv2 = null;
		}
		// build term
		if (tv1 == null && tv2 == null) {
			tmpTerm = script.term(operator, script.decimal(operand2), script.decimal(operand1));
		} else if (tv1 != null && tv2 == null) {
			tmpTerm = script.term(operator, script.decimal(operand2), tv1);
		} else if (tv1 == null) {
			tmpTerm = script.term(operator, tv2, script.decimal(operand1));
		} else {
			tmpTerm = script.term(operator, tv2, tv1);
		}
		return tmpTerm;
	}
	
	private static Term buildTerm(Term term1, String operand2, String operator, Map<String, Term> strTerm,
			Map<String, TermVariable> outVarTVMap, Script script) {
		Term tmpTerm;
		TermVariable tv2;
		// operand 2
		if (outVarTVMap.containsKey(operand2)) {
			tv2 = outVarTVMap.get(operand2);
		} else {
			tv2 = null;
		}
		// build term
		if (tv2 == null) {
			tmpTerm = script.term(operator, script.decimal(operand2), term1);
		} else {
			tmpTerm = script.term(operator, tv2, term1);
		}
		return tmpTerm;
	}
	
	private static boolean isOperator(String sign) {
		return mOperators.containsKey(sign);
	}
}
