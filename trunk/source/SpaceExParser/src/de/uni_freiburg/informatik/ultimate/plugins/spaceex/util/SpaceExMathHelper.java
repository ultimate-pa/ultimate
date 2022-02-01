/*
 * Copyright (C) 2016 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SpaceExMathHelper {

	// replacement map for variables of the form Literal -> real variable.. e.g
	// A0 -> x<=5
	private static final Map<String, String> mReplacement = new HashMap<>();

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

	public enum Operator {
		MULTIPLY(9), DIVIDE(9), ADD(8), SUBTRACT(8), LTEQ(7), GTEQ(7), LT(7), GT(7), EQ(7), DOUBLEEQ(7), AND(
				6), DOUBLEAND(6), ANDTEXT(6), OR(5), DOUBLEOR(5), ORTEXT(5);
		final int precedence;

		Operator(final int p) {
			precedence = p;
		}
	}

	private static boolean isHigherPrec(final String op, final String sub) {
		return mOperators.containsKey(sub) && (mOperators.get(sub).precedence >= mOperators.get(op).precedence);
	}

	// function to replace literals with their saved values
	private static List<String> replaceLiterals(final List<String> groups) {
		final List<String> res = new ArrayList<>();
		for (final String group : groups) {
			String replacement = group.replaceAll("\\s+", "");
			for (final Map.Entry<String, String> entry : mReplacement.entrySet()) {
				final String rep = entry.getKey();
				final String loc = entry.getValue();
				replacement = replacement.replaceAll("\\b" + rep + "\\b", loc);
			}
			res.add(replacement);
		}
		return res;
	}

	// helper function to replace all elements in a string of the form x==2 &
	// loc(x)==loc1, with single literals.
	// x==2 & loc(x)==loc1 & y<=4 ---> A0 & A1 & A2
	private static String replaceAllWithLiterals(final String initially) {
		mReplacement.clear();
		// regex for location assignments of the form loc( <automaton name> )==
		// <location name>
		final String locRegex = "(.*)loc\\((.*)\\)==(.*)";
		final Pattern locPattern = Pattern.compile(locRegex);
		Matcher locMatcher;
		// regex for variables of the form v1<=var<=v2 or x=v1.. etc
		final String varRegex = "(.*)(<=|<|>|>=)(.*)(<=|<|>|>=)(.*)|(.*)(<=|>=|<|>|==)(.*)";
		final Pattern varPattern = Pattern.compile(varRegex);
		Matcher varMatcher;
		final String literal = "A";
		// replace all terms by a Literal
		// the regex will split at &, | loc(xxx)==ccc, (, )
		final String[] splitted = initially.replaceAll("\\s+", "").split("(\\&)|(\\|)|(?<!loc)(\\()|(?!\\)==)(\\))");
		for (int i = 0; i < splitted.length; i++) {
			final String el = splitted[i];
			locMatcher = locPattern.matcher(el);
			varMatcher = varPattern.matcher(el);
			if (locMatcher.matches() && !mReplacement.containsValue(locMatcher.group(0))) {
				mReplacement.put(literal + i, locMatcher.group(0));
			} else if (varMatcher.matches() && !mReplacement.containsValue(varMatcher.group(0))) {
				mReplacement.put(literal + i, varMatcher.group(0));
			}
		}
		String replacement = initially.replaceAll("\\s+", "");
		for (final Map.Entry<String, String> entry : mReplacement.entrySet()) {
			final String rep = entry.getKey();
			final String loc = entry.getValue();
			replacement = replacement.replaceAll(Pattern.quote(loc), rep);
		}
		return replacement;
	}

	public static List<String> infixToGroups(final String infix) {
		final List<String> groups;
		if (!infix.contains("|")) {
			groups = new ArrayList<>();
			groups.add(infix);
			return groups;
		} else {
			final String infixWithLiterals = replaceAllWithLiterals(infix);
			final List<String> infixToArray = SpaceExMathHelper.expressionToArray(infixWithLiterals);
			final List<String> postfix = SpaceExMathHelper.postfix(infixToArray);
			groups = postfixToGroups(postfix);
			return replaceLiterals(groups);
		}
	}

	/**
	 * Function to convert a given formula postfix back notation to groups, the
	 * DNF.
	 *
	 * @param postfix
	 * @return
	 */
	public static List<String> postfixToGroups(final List<String> postfix) {
		final Deque<String> stack = new LinkedList<>();
		final List<String> openGroupstack = new ArrayList<>();
		final List<String> finishedGroups = new ArrayList<>();
		for (final String element : postfix) {
			if (isOperator(element)) {
				final String operand1 = (!stack.isEmpty()) ? stack.pop() : "";
				final String operand2 = (!stack.isEmpty()) ? stack.pop() : "";
				/*
				 * Cases: - two single operands - & is operator and no groups
				 * exist yet --> initialize groups - & is operator and groups
				 * exist -> update groups - | is operator and groups exists ->
				 * add to finished groups - | is operator and no groups exists
				 * --> add to finished groups
				 */
				if (mReplacement.containsKey(operand1)
						&& (mReplacement.containsKey(operand2) || !operand2.contains("&")) && !operand2.isEmpty()) {
					// push Two single operands to stack
					stack.push(operand2 + element + operand1);
				} else if ("&".equals(element) && openGroupstack.isEmpty()) {
					// "initialization" of the different groups
					final List<String> eval = evaluateOperands(operand1, operand2);
					openGroupstack.addAll(eval);
				} else if ("&".equals(element) && !openGroupstack.isEmpty()) {
					// after the first time, operand 2 will never contain a &
					// again.
					final List<String> removeList = new ArrayList<>();
					final List<String> newGroups = new ArrayList<>();
					// update groups
					for (final String group : openGroupstack) {
						if (operand1.contains("|")) {
							final List<String> eval = evaluateOrAndAnd(operand1, group);
							newGroups.addAll(eval);
						} else {
							final String newTerm = group + "&" + operand1;
							newGroups.add(newTerm);
						}
						removeList.add(group);
					}
					// remove old stuff
					for (final String group : removeList) {
						openGroupstack.remove(group);
					}
					openGroupstack.addAll(newGroups);
				} else if ("|".equals(element)) {
					if (openGroupstack.isEmpty() && !operand2.contains("&") && !operand1.contains("&")) {
						stack.push(operand2 + element + operand1);
					} else {
						if (!operand1.isEmpty()) {
							finishedGroups.add(operand1);
						}
						if (!operand2.isEmpty()) {
							finishedGroups.add(operand2);
						}
					}
				}
			} else {
				stack.push(element);
			}
		}
		if (!stack.isEmpty() && !stack.peek().contains("&")) {
			final String[] groups = stack.pop().replaceAll("(\\()|(\\))", "").split("\\|");
			for (final String group : groups) {
				openGroupstack.add(group);
			}
		}
		finishedGroups.addAll(openGroupstack);
		return finishedGroups;
	}

	// function that evaluates operands and sets up the different groups
	private static List<String> evaluateOperands(final String operand1, final String operand2) {
		final List<String> openGroupstack = new ArrayList<>();
		if (operand1.contains("|") && operand2.contains("|")) {
			final List<String> eval = evaluateOrAndOr(operand1, operand2);
			openGroupstack.addAll(eval);
		} else if (operand1.contains("|")) {
			final List<String> eval = evaluateOrAndAnd(operand1, operand2);
			openGroupstack.addAll(eval);

		} else if (operand2.contains("|")) {
			final List<String> eval = evaluateOrAndAnd(operand2, operand1);
			openGroupstack.addAll(eval);

		} else if (operand2.contains("&")) {
			openGroupstack.add(operand2 + "&" + operand1);
		}
		return openGroupstack;
	}

	private static List<String> evaluateOrAndOr(final String operand1, final String operand2) {
		final List<String> res = new ArrayList<>();
		final String[] splitOP1 = operand1.replaceAll("(\\()|(\\))", "").split("(\\&)|(\\|)");
		final String[] splitOP2 = operand2.replaceAll("(\\()|(\\))", "").split("(\\&)|(\\|)");
		for (final String element : splitOP2) {
			for (final String element2 : splitOP1) {
				res.add(element2 + "&" + element);
			}
		}
		return res;

	}

	private static List<String> evaluateOrAndAnd(final String operand1, final String operand2) {
		final List<String> res = new ArrayList<>();
		final String[] splitOP1 = operand1.replaceAll("(\\()|(\\))", "").split("(\\&)|(\\|)");
		for (final String el : splitOP1) {
			res.add(operand2 + "&" + el);
		}
		return res;
	}

	/**
	 * Function to split a given expression into an array. e.g "x == 5" will
	 * return [x,==,5].
	 *
	 * @param expression
	 * @return
	 */
	public static List<String> expressionToArray(final String expression) {
		final List<String> res = new ArrayList<>();
		// Regex to split a string at ">=, <= ,>, <, ==, +, -, (, ), &, |, *, /"
		// TODO: generate this regex from the operators map.
		final Pattern p = Pattern.compile("([&]{1,2}|>=?|<=?|<(?!=)|>(?!=)|==|\\+|(?<!=|&)-|/|\\*|\\||\\(|\\)| +)");
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

	/**
	 * Function to convert an expression in postfix notation to infix notation.
	 *
	 * @param List<String>
	 *            postfix - is a postfix expression in list form.
	 * @return String, the postfix converted to infix notation.
	 */
	public static String toInfix(final List<String> postfix) {
		final Deque<String> stack = new LinkedList<>();
		for (final String element : postfix) {
			if (isOperator(element)) {
				final String operand1 = stack.pop();
				final String operand2 = stack.pop();
				stack.push(operand2 + element + operand1);
			} else {
				stack.push(element);
			}
		}
		return stack.pop();
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

	/**
	 * Function that checks whether a sign is an operator. e.g. "==" would be an
	 * operator.
	 *
	 * @param String
	 *            sign
	 * @return True if input is operator (mOperators map)
	 */
	public static boolean isOperator(final String sign) {
		return mOperators.containsKey(sign);
	}

	public static boolean isEvaluation(final String operator) {
		return ("+".equals(operator) || "-".equals(operator) || "*".equals(operator) || "/".equals(operator));
	}

	public static boolean isInequality(final String operator) {
		return ">=".equals(operator) || ">".equals(operator) || "<=".equals(operator) || "<".equals(operator);
	}
}
