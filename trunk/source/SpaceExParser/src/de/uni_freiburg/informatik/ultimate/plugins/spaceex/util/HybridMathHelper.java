package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Helper class to convert math expressions to SMT stuff //TODO: not done yet, don't use
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridMathHelper {
	
	public static enum Operator {
		ADD(1, "+"), SUB(1, "-"), DIV(2, "/"), MUL(2, "*"), LT(3, "<"), GT(3, ">"), LTEQ(3, "<="), GTEQ(3, ">="),
		EQUALS(3, "=="), AND(4, "&"), OR(5, "|"), LBRACE(6, "("), RBRACE(6, ")");
		int precedence;
		String operator;
		
		Operator(int p, String op) {
			precedence = p;
			operator = op;
		}
		
	}
	
	public HybridMathHelper() {
		
	}
	
	/**
	 * This function splits a given expression into an array. e.g "x == 5" will get [x,==,5]. Operators are defined as
	 * follows: Operator(precedence, operator): ADD(1, "+"), SUB(1, "-"), DIV(2, "/"), MUL(2,"*"), LT(3, "<"), GT(3,
	 * ">"), LTEQ(3, "<="), GTEQ(3, ">="), EQUALS(3, "=="), AND(4, "&"), OR(5, "|");
	 * 
	 * Note that the expression can only contain operators from the list above.
	 * 
	 * @param operators
	 * @param expression
	 * @return
	 */
	public static String[] expressionToArray(List<Operator> operators, String expression) {
		String regex = "(?<=\\G(\\w+(?!\\w+)";
		int lbraceCount = 0;
		int rbraceCount = 0;
		// build a regex out of the operators.
		for (Iterator<Operator> iterator = operators.iterator(); iterator.hasNext();) {
			Operator op = iterator.next();
			regex += "|";
			if (op.operator == "+" || op.operator == "*" || op.operator == "/" || op.operator == "|"
					|| op.operator == "&" || op.operator == "(" || op.operator == ")") {
				regex += "\\" + op.operator;
			} else if (op.operator == "<" || op.operator == ">") {
				regex += op.operator + "(?!=)";
			} else {
				regex += op.operator;
			}
			if (op.operator == "(") {
				lbraceCount += 1;
			}
			if (op.operator == ")") {
				rbraceCount += 1;
			}
		}
		regex += "))\\s*";
		// if bracecount is equal, split and return
		if (lbraceCount == rbraceCount) {
			String[] arr = expression.split(regex);
			return arr;
		} else {
			throw new IllegalStateException(
					"input expression is invalid because it contains an inconsistent amount of braces \n"
							+ "expession: " + expression + "\n left brace count: " + lbraceCount
							+ "\n right brace count: " + rbraceCount);
		}
	}
	
	public static SyntaxTree<String> arrayToTree(List<Operator> operators, String[] expressionArray) {
		SyntaxTree<String> tree = new SyntaxTree<String>("root");
		SyntaxTreeNode<String> currentNode = tree.getRootNode();
		for (int i = 0; i < expressionArray.length; i++) {
			String sign = expressionArray[i];
			if (isOperator(operators, sign)) {
				if (sign.equals("&") || sign.equals("|")) {
					SyntaxTreeNode<String> node = currentNode;
					while (!node.getParent().isRoot()) {
						node = node.getParent();
					}
					SyntaxTreeNode<String> newNode = new SyntaxTreeNode<>(sign);
					node.getParent().addChild(newNode);
					newNode.addChild(node);
					newNode.getParent().removeChild(node);
					currentNode = newNode;
				} else {
					SyntaxTreeNode<String> newNode = new SyntaxTreeNode<>(currentNode.getData());
					currentNode.setData(sign);
					currentNode.addChild(newNode);
				}
			} else {
				SyntaxTreeNode<String> newNode = new SyntaxTreeNode<>(sign);
				currentNode.addChild(newNode);
				currentNode = newNode;
			}
		}
		return tree;
	}
	
	public static Term syntaxTreeToTerm(SyntaxTree<String> tree) {
		Term term = null;
		SyntaxTreeNode<String> root = tree.getRootNode();
		// go to the bottom of the tree
		SyntaxTreeNode<String> node = root;
		// get preorder
		List<SyntaxTreeNode<String>> preorder = preOrder(root);
		for (SyntaxTreeNode<String> n : preorder) {
			System.out.println(n.getData());
		}
		System.out.println("#######");
		// reverse the preorder
		Collections.reverse(preorder);
		for (SyntaxTreeNode<String> n : preorder) {
			System.out.println(n.getData());
		}
		return term;
	}
	
	private static List<SyntaxTreeNode<String>> preOrder(SyntaxTreeNode<String> treenode) {
		List<SyntaxTreeNode<String>> postOrder = new ArrayList<>();
		postOrder.add(treenode);
		for (SyntaxTreeNode<String> child : treenode.getChildren()) {
			postOrder.addAll(preOrder(child));
		}
		return postOrder;
	}
	
	private static boolean isOperator(List<Operator> operators, String sign) {
		for (Operator operator : operators) {
			if (sign.equals(operator.operator)) {
				return true;
			}
		}
		return false;
	}
	
	public static List<Operator> getAllAvailableOperators() {
		List<Operator> operators = new ArrayList<>();
		operators.add(Operator.ADD);
		operators.add(Operator.SUB);
		operators.add(Operator.DIV);
		operators.add(Operator.MUL);
		operators.add(Operator.AND);
		operators.add(Operator.OR);
		operators.add(Operator.LT);
		operators.add(Operator.GT);
		operators.add(Operator.LTEQ);
		operators.add(Operator.GTEQ);
		operators.add(Operator.EQUALS);
		operators.add(Operator.LBRACE);
		operators.add(Operator.RBRACE);
		return operators;
	}
	
}
