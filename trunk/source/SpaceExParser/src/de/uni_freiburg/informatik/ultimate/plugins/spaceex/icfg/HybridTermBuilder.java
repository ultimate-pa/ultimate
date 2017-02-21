package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Class to build Terms from Hybrid automata expressions like Initial values, Invariants and Jumps
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridTermBuilder {
	private final HybridVariableManager mVariableManager;
	private final Script mScript;
	private final Map<String, Term> mStringTerm;
	private final Map<HybridProgramVar, TermVariable> mInVars;
	private final Map<HybridProgramVar, TermVariable> mOutVars;
	protected static final Map<String, Operator> mOperators = new HashMap<>();
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
		mOperators.put("and", Operator.ANDTEXT);
		mOperators.put("|", Operator.OR);
		mOperators.put("||", Operator.DOUBLEOR);
		mOperators.put("or", Operator.ORTEXT);
	}
	
	public enum BuildScenario {
		INITIALLY, INVARIANT, UPDATE, GUARD;
	}
	
	public enum Operator {
		ADD(1), SUBTRACT(1), MULTIPLY(2), DIVIDE(2), LTEQ(5), GTEQ(5), LT(5), GT(5), EQ(5), DOUBLEEQ(5), AND(4),
		DOUBLEAND(4), ANDTEXT(4), OR(3), DOUBLEOR(3), ORTEXT(3);
		final int precedence;
		
		Operator(final int p) {
			precedence = p;
		}
	}
	
	public HybridTermBuilder(final HybridVariableManager variableManger, final Script script) {
		mVariableManager = variableManger;
		mScript = script;
		mStringTerm = new HashMap<>();
		mInVars = new HashMap<>();
		mOutVars = new HashMap<>();
	}
	
	public Term infixToTerm(final String infix, final BuildScenario scenario) {
		List<String> infixArray = expressionToArray(infix);
		if (scenario == BuildScenario.UPDATE) {
			infixArray = preprocessForUpdate(infixArray);
		}
		final List<String> postfix = postfix(infixArray);
		final List<String> postfixSMTConform = preprocessForTermBuilding(postfix);
		return postfixToTerm(postfixSMTConform, scenario);
	}
	
	private List<String> preprocessForTermBuilding(final List<String> postfix) {
		final List<String> newPostfix = new ArrayList<>();
		for (String el : postfix) {
			// & is "and" in SMT
			// == is "=" in SMT
			// | is "or" in SMT
			if ("&".equals(el) || "&&".equals(el)) {
				el = "and";
			} else if ("==".equals(el) || ":=".equals(el)) {
				el = "=";
			} else if ("|".equals(el) || "||".equals(el)) {
				el = "or";
			}
			newPostfix.add(el);
		}
		return newPostfix;
	}
	
	// update of the form x := x+1 becomes x := (x+1)
	// needed for postfix form.
	private List<String> preprocessForUpdate(final List<String> infixArray) {
		final List<String> res = new ArrayList<>();
		boolean open = false;
		for (final String el : infixArray) {
			if ("==".equals(el)) {
				res.add(el);
				res.add("(");
				open = true;
			} else if ("&".equals(el)) {
				res.add(")");
				res.add(el);
				open = false;
			} else {
				res.add(el);
			}
		}
		if (open) {
			res.add(")");
			open = false;
		}
		return res;
	}
	
	/**
	 * Function to convert a given formula postfix notation as array, into a term., sali ge
	 *
	 * @param postfix
	 * @param script
	 * @param variableManager
	 * @return
	 */
	public Term postfixToTerm(final List<String> postfix, final BuildScenario scenario) {
		/*
		 * 1. Create an empty stack that can hold string values. 2. Scan the postfix expression from left to right 2a.
		 * If operand then push into stack 2b. If operator then 1. Pop first two elements 2. Now make a term of the form
		 * (operand2,operator,operand1)" 3. Push the new term onto stack
		 */
		Term term = null;
		final Deque<String> stack = new LinkedList<>();
		for (final String el : postfix) {
			final String element = el;
			if (isOperator(element)) {
				final String operand1 = stack.pop();
				final String operand2 = stack.pop();
				final String operator = element;
				final Term tmpTerm = checkAndbuildInitialTerm(operand1, operand2, operator, scenario);
				
				if (term == null) {
					term = tmpTerm;
					stack.push(term.toString());
					mStringTerm.put(term.toString(), term);
				} else if (tmpTerm != null) {
					term = tmpTerm;
					stack.push(tmpTerm.toString());
					mStringTerm.put(tmpTerm.toString(), term);
				}
			} else {
				stack.push(element);
			}
		}
		return term;
	}
	
	// helper function to build terms from postfix notation
	private Term checkAndbuildInitialTerm(final String operand1, final String operand2, final String operator,
			final BuildScenario scenario) {
		// check if the operand already got a term.
		Term tmpTerm;
		if (mStringTerm.containsKey(operand1) && mStringTerm.containsKey(operand2)) {
			final Term t1 = mStringTerm.get(operand1);
			final Term t2 = mStringTerm.get(operand2);
			tmpTerm = mScript.term(operator, t2, t1);
		} else if (mStringTerm.containsKey(operand1) && !mStringTerm.containsKey(operand2)) {
			final Term t1 = mStringTerm.get(operand1);
			tmpTerm = buildInitialTerm(t1, operand2, operator, scenario);
		} else if (!mStringTerm.containsKey(operand1) && mStringTerm.containsKey(operand2)) {
			final Term t2 = mStringTerm.get(operand2);
			tmpTerm = buildInitialTerm(operand1, t2, operator, scenario);
		} else {
			tmpTerm = buildInitialTerm(operand1, operand2, operator, scenario);
		}
		return tmpTerm;
	}
	
	// helper function to build terms from postfix notation
	private Term buildInitialTerm(final String operand1, final Term term2, final String operator,
			final BuildScenario scenario) {
		Term tmpTerm;
		final TermVariable tv1 = checkAndGetTermVariable(operand1, scenario, true);
		// build term
		final TermVariable[] free = term2.getFreeVars();
		if (tv1 == null) {
			final Term t1 = mScript.term(operator, free[free.length - 1], mScript.decimal(operand1));
			tmpTerm = mScript.term("and", term2, t1);
		} else {
			final Term t1 = mScript.term(operator, free[free.length - 1], tv1);
			tmpTerm = mScript.term("and", term2, t1);
		}
		return tmpTerm;
	}
	
	// helper function to build terms from postfix notation
	private Term buildInitialTerm(final String operand1, final String operand2, final String operator,
			final BuildScenario scenario) {
		Term tmpTerm;
		final TermVariable tv1 = checkAndGetTermVariable(operand1, scenario, true);
		final TermVariable tv2 = checkAndGetTermVariable(operand2, scenario, false);
		// build term
		if (tv1 == null && tv2 == null) {
			tmpTerm = mScript.term(operator, mScript.decimal(operand2), mScript.decimal(operand1));
		} else if (tv1 != null && tv2 == null) {
			tmpTerm = mScript.term(operator, mScript.decimal(operand2), tv1);
		} else if (tv1 == null) {
			tmpTerm = mScript.term(operator, tv2, mScript.decimal(operand1));
		} else {
			tmpTerm = mScript.term(operator, tv2, tv1);
		}
		return tmpTerm;
	}
	
	// helper function to build terms from postfix notation
	private Term buildInitialTerm(final Term term1, final String operand2, final String operator,
			final BuildScenario scenario) {
		Term tmpTerm;
		final TermVariable tv2 = checkAndGetTermVariable(operand2, scenario, false);
		// build term
		if (tv2 == null) {
			tmpTerm = mScript.term(operator, mScript.decimal(operand2), term1);
		} else {
			tmpTerm = mScript.term(operator, tv2, term1);
		}
		return tmpTerm;
	}
	
	// helper function to get the correct termvariable for each scenario
	private TermVariable checkAndGetTermVariable(final String operand1, final BuildScenario scenario,
			final boolean isAssignedValue) {
		if (mVariableManager.getConstants().contains(operand1)) {
			return null;
		} else if (scenario == BuildScenario.INITIALLY) {
			return getInitiallyTV(operand1);
		} else if (scenario == BuildScenario.GUARD || scenario == BuildScenario.INVARIANT) {
			return getInvariantTV(operand1);
		} else {
			return getUpdateTV(operand1, isAssignedValue);
		}
	}
	
	// helper function to get TermVariable for initially Terms
	private TermVariable getInitiallyTV(final String operand1) {
		if (mVariableManager.getVar2OutVarTermVariable().containsKey(operand1)) {
			final HybridProgramVar progvar = mVariableManager.getVar2ProgramVar().get(operand1);
			final TermVariable outvar = mVariableManager.getVar2OutVarTermVariable().get(operand1);
			mOutVars.put(progvar, outvar);
			return outvar;
		} else {
			return null;
		}
	}
	
	// helper function to get TermVariable for Invariant or Guard Terms
	private TermVariable getInvariantTV(final String operand1) {
		if (mVariableManager.getVar2InVarTermVariable().containsKey(operand1)) {
			final HybridProgramVar progvar = mVariableManager.getVar2ProgramVar().get(operand1);
			final TermVariable invar = mVariableManager.getVar2InVarTermVariable().get(operand1);
			final TermVariable outvar = mVariableManager.getVar2OutVarTermVariable().get(operand1);
			mInVars.put(progvar, invar);
			mOutVars.put(progvar, outvar);
			return invar;
		} else {
			return null;
		}
	}
	
	// helper function to get TermVariable for Invariant or Update Terms
	private TermVariable getUpdateTV(final String operand1, final boolean isAssignedValue) {
		if (isAssignedValue) {
			if (mVariableManager.getVar2OutVarTermVariable().containsKey(operand1)) {
				final HybridProgramVar progvar = mVariableManager.getVar2ProgramVar().get(operand1);
				final TermVariable outvar = mVariableManager.getVar2OutVarTermVariable().get(operand1);
				mOutVars.put(progvar, outvar);
				return outvar;
			} else {
				return null;
			}
		} else {
			if (mVariableManager.getVar2InVarTermVariable().containsKey(operand1)) {
				final HybridProgramVar progvar = mVariableManager.getVar2ProgramVar().get(operand1);
				final TermVariable invar = mVariableManager.getVar2InVarTermVariable().get(operand1);
				mInVars.put(progvar, invar);
				return invar;
			} else {
				return null;
			}
		}
	}
	
	/**
	 * This function splits a given expression into an array. e.g "x == 5" will return [x,==,5].
	 *
	 * @param expression
	 * @return
	 */
	public static List<String> expressionToArray(final String expression) {
		final List<String> res = new ArrayList<>();
		final Pattern p = Pattern.compile("([&]{1,2}|>=?|<=?|<(?!=)|>(?!=)|==|\\+|-(?!\\w+)|\\*|\\||\\(|\\)| +)");
		final String s = expression.replaceAll("\\s", "");
		final Matcher m = p.matcher(s);
		int pos = 0;
		while (m.find()) {
			if (pos != m.start()) {
				res.add(s.substring(pos, m.start()));
			}
			res.add(m.group());
			pos = m.end();
		}
		if (pos != s.length()) {
			res.add(s.substring(pos));
		}
		return res;
	}
	
	private static boolean isHigherPrec(final String op, final String sub) {
		return mOperators.containsKey(sub) && mOperators.get(sub).precedence >= mOperators.get(op).precedence;
	}
	
	/**
	 * Function to convert infix to postfix (Shunting yard algorithm)
	 *
	 * @param infixArray
	 * @return
	 */
	public static List<String> postfix(final List<String> infixArray) {
		final List<String> output = new ArrayList<>();
		final Deque<String> stack = new LinkedList<>();
		
		for (final String element : infixArray) {
			// operator
			if (mOperators.containsKey(element)) {
				while (!stack.isEmpty() && isHigherPrec(element, stack.peek())) {
					output.add(stack.pop());
				}
				stack.push(element);
				// left bracket
			} else if ("(".equals(element)) {
				stack.push(element);
				
				// right bracket
			} else if (")".equals(element)) {
				while (!"(".equals(stack.peek())) {
					output.add(stack.pop());
				}
				// digit
				stack.pop();
			} else {
				output.add(element);
			}
		}
		
		while (!stack.isEmpty()) {
			output.add(stack.pop());
		}
		
		return output;
	}
	
	public static boolean isOperator(final String sign) {
		return mOperators.containsKey(sign);
	}
	
	public Map<HybridProgramVar, TermVariable> getmInVars() {
		return mInVars;
	}
	
	public Map<HybridProgramVar, TermVariable> getmOutVars() {
		return mOutVars;
	}
	
}
