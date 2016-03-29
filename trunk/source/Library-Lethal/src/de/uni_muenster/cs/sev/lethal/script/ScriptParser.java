/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.script;

import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptParseException;

import java.util.ArrayList;
import java.util.List;

/**
 * Script Text parser
 * @author Philipp
 *
 */
public class ScriptParser {

	/**
	 * Parses the given string and returns a Script object, ready to run
	 * @param scriptString string to parse
	 * @return resulting script object
	 */
	public static Script parseScript(String scriptString){
		StringReader script = new StringReader(scriptString);
		List<Statement> statements;
		
		statements = parseStatementList(script, null);
		
		return new Script(statements);
	}
	
	/**
	 * Reads and parses statements until eof or the gieven terminator is reached
	 * @param script script string reader to read from 
	 * @param terminator regexp to terminate at.
	 * @return List of parsed statements
	 */
	private static List<Statement> parseStatementList(StringReader script, String terminator){
		List<Statement> statements = new ArrayList<Statement>();
		
		while (true){
			script.skipAll(" \t\n");
			if (script.eof()) {break;}
			if (terminator != null && script.matches(terminator)){
				if (script.lastMatch != null) script.skip(script.lastMatch.length());
				break;
			}
			Statement stmt = parseStatement(script);
			if (stmt != null) statements.add(stmt);
		}
		return statements;
	}
	
	/**
	 * Parses a single statement
	 * @param script script string reader to read from 
	 * @return Parsed statement
	 */
	private static Statement parseStatement(StringReader script){
		script.skipAll(" \t\n");
		if (script.matches("^def[ \t]")){
			script.skip(4);
			String methodName = script.readUntil("([(]|\n)");
			script.skip(methodName.length());
			Method method = parseMethod(script);
			return new ObjectMethodBinding(method, methodName.trim());
		}
		if (script.matches("^(if[ \t]+)|^(if)\\(")){
			script.skip(script.lastMatch.length());
			return parseIf(script);
		}
		if (script.matches("^(while[ \t]+)|^(while)\\(")){
			script.skip(script.lastMatch.length());
			return parseWhile(script);
		}
		if (script.matches("^(class\\s+)")){
			script.skip(script.lastMatch.length());
			return parseClass(script);
		}
		if (script.matches("^(break)")){
			script.skip(script.lastMatch.length());
			return new Break();
		}
		if (script.matches("^(return)")){
			script.skip(script.lastMatch.length());
			return new Return(parseExpression(null, script, "^\n|^(;)|^}"));
		}
		
		return parseExpression(null, script, "^\n|^(;)|^}");
	}
	
	/**
	 * Parses a single expression
	 * @param source expression evaluating to the namespace source for the following expression (e.g. in foo.bar() the expression "foo" is the namespace source for bar())
	 * @param script script string reader to read from
	 * @param terminatorRegexp regexp to terminate at.
	 * @return Parsed expression
	 */
	private static Expression parseExpression(Expression source, StringReader script, String terminatorRegexp) {
		List<Expression> expressions = new ArrayList<Expression>();
		Expression exp;
		while (true) {
			script.skipAll(" \t");
			if (script.eof()){
				break;
			} else if (terminatorRegexp != null && script.matches(terminatorRegexp) ){
				if (script.lastMatch != null) script.skip(script.lastMatch.length());
				break;
			} else if (script.startsWith("#")) {
				String comment = script.readUntil("\n");
				script.skip(comment.length());
				break;
			} else if (script.startsWith("\"")){
				script.skip(1);
				String s = script.readUntil("(\")");
				script.skip(s.length()+1);
				exp = new StringObject(s);
			} else if (script.matches("^(!)[^=]") ||  //boolean not
						(((expressions.size() == 0) || //leading - may appear at the beginning or after an Operator
						((expressions.size() > 0) && (expressions.get(expressions.size()- 1) instanceof Operator)))
								&& script.matches("^(-)")) ) {
				String op = script.lastMatch;
				exp = Operator.makeUnaryOperator(script, op);
				script.skip(op.length());
			} else if (expressions.size() > 0 && script.matches("^(\\*\\*|\\.\\.|==|!=|<=|>=|=<|=>|=|&&|\\|\\||[+-/*%><])")){
				String op = script.lastMatch;
				exp = Operator.makeBinaryOperator(script, op);
				script.skip(op.length());
			} else if (script.matches("^(proc\\{)")){
				script.skip(script.lastMatch.length());
				exp = parseBlockDefinition(script);
			} else if (script.matches("^([a-z_A-Z][a-z_A-Z0-9?]*)[\\(\\{]")){
				String name = script.lastMatch();
				script.skip(name.length());
				exp = parseMethodCall(source, name, script);
//			} else if (script.matches("^\\(.+\\.\\..+\\))")){
//				Expression leftExp = parseExpression(null, script, "^(\\.\\.)");
			} else if (script.matches("^[(]")) {
				script.skip(1); //opening bracket
				exp = parseExpression(null, script, "^\\)");
				script.skip(1); //closing bracket
			} else if (script.matches("^(true)")) {
				String match = script.lastMatch();
				script.skip(match.length());
				exp = ScriptObject.trueValue;
			} else if (script.matches("^(false)")) {
				String match = script.lastMatch();
				script.skip(match.length());
				exp = ScriptObject.falseValue;
			} else if (script.matches("^(null)")) {
				String match = script.lastMatch();
				script.skip(match.length());
				exp = ScriptObject.nullValue;
			} else if (script.matches("^([+-]?[0-9]+[.][0-9]+)")) {
				String match = script.lastMatch();
				script.skip(match.length());
				exp = ScriptObject.make(Double.parseDouble(match));
			} else if (script.matches("^([+-]?[0-9]+)")) {
				String match = script.lastMatch();
				script.skip(match.length());
				exp = ScriptObject.make(Integer.parseInt(match));
			} else if (script.matches("^([a-z_A-Z][a-z_A-Z0-9?]*)")) {
				String name = script.lastMatch();
				script.skip(name.length());
				exp = new Evaluation(source, name);
			} else {
				throw new ScriptParseException(script.getCurrentLine(), "Invalid expression");
			}
			if (!script.eof() && script.matches("^\\.[^.]")){
				script.skip(1);
				exp =  parseExpression(exp, script, terminatorRegexp);
			}
			expressions.add(exp);
			
			//if we are parsing a . expression (source != null) and no further . term is coming, we are done here.
			if (!script.eof() && script.currentChar() != '.' && source != null){
				break;
			}
				
		}

		if (expressions.size() > 1){
			bindUnaryOperators(script, expressions);
			return fuseExpressionList(script, expressions);
		} else if (expressions.size() == 1) {
			return expressions.get(0);
		} else {
			return null;
		}

	}
	
	/**
	 * Binds all unary operators in the given expression list to their right hand arguments
	 * @param script script string reader to read from
	 * @param expressions Expression list. The list is modified
	 */
	private static void bindUnaryOperators(StringReader script, List<Expression> expressions){
		for (int i = expressions.size() -1; i >= 0 ;i--){
			Expression exp = expressions.get(i);
			if (exp instanceof UnaryOperator){
				if (i == expressions.size()-1){
					throw new ScriptParseException(script.getCurrentLine(), "Unexpected end of expression");
				}
				UnaryOperator op = (UnaryOperator)exp;
				op.bind(expressions.get(i+1));
				expressions.remove(i+1);
			}
		}
		
	}
	
	/**
	 * Binds all binary operators in the given expression list
	 * @param script script string reader to read from
	 * @param expressions expression list
	 * @return single expression referencing all bound expressions 
	 */
	private static Expression fuseExpressionList(StringReader script, List<Expression> expressions){
		if (expressions.size() == 1){
			return expressions.get(0);
		} else if (expressions.size() == 2) {
			throw new ScriptParseException(script.getCurrentLine(), "Even number of expressions in list");
		} else {
			//bind unary ops
			
			boolean binOperator = false;
			int minWeight = Integer.MAX_VALUE;
			int minWeightPos = -1;
			for (int i = 0; i < expressions.size();i++){
				Expression exp = expressions.get(i);
				if (binOperator){
					if (!(exp instanceof BinaryOperator)) throw new ScriptParseException(script.getCurrentLine(), "Expected operator, got " + exp);
					Operator op = (Operator)exp;
					if (op.getBindWeight() < minWeight){
						minWeight = op.getBindWeight();
						minWeightPos = i;
					}
				} else { //no binary op expected
					if (exp instanceof BinaryOperator && !((BinaryOperator)exp).isBound()) { //bin op found, oops.
						throw new ScriptParseException(script.getCurrentLine(), "Unexpected binary operator");
					}
				}
				binOperator = !binOperator;
				
			}
			
			//Assign left and right expressions to the weakest binding operator (calculated last).
			BinaryOperator op = (BinaryOperator)expressions.get(minWeightPos);
			Expression left = fuseExpressionList(script,  expressions.subList(0, minWeightPos));
			Expression right = fuseExpressionList(script, expressions.subList(minWeightPos+1, expressions.size()));
			op.bind(left, right);
			return op;
		}
	}
		
	/**
	 * Parses a method call statement (with parameter expressions if present)
	 * @param source expression evaluating to the namespace source for the following expression (e.g. in foo.bar() the expression "foo" is the namespace source for bar())
	 * @param name name of the method to call
	 * @param script script string reader to read from
	 * @return method call expression
	 */
	private static Expression parseMethodCall(Expression source, String name, StringReader script) {
		List<Expression> arguments = new ArrayList<Expression>();
		if (script.startsWith("(")){
			script.skip(1);
			while (true){
				script.skipAll(" \t\n");
				if (script.startsWith(")")){
					script.skip(1);
					break;
				} else if (script.startsWith(",")){
					script.skip(1);
				} else if (script.eof()) {
					throw new ScriptParseException(script.getCurrentLine(), "Unexpected EOF while parsing method call");
				}
				Expression exp = parseExpression(null, script, "^[,)]");
				if (exp != null) arguments.add(exp);
			}
		}
		MethodDefinition block = null;
		script.skipAll(" \t");
		if (script.startsWith("{")){ //block appended to call
			script.skip(1);
			block = parseBlockDefinition(script);
		}
		
		return new Call(source,name,arguments, block);
	}

	/**
	 * Parses an if statement with condition, then and optional else block
	 * @param script script string reader to read from
	 * @return parsed if expression
	 */
	private static Statement parseIf(StringReader script){
		Expression condition = parseExpression(null, script, "^(then|\n)");
		List<Statement> ifStatements = parseStatementList(script, "^end|^else");
		List<Statement> elseStatements;
		if (script.startsWith("else")) {
			script.skip(4);
			elseStatements = parseStatementList(script, "^(end)");
		} else {
			script.skip(3);
			elseStatements = new ArrayList<Statement>();
		}
		return new If(condition, ifStatements, elseStatements);
	}
	
	/**
	 * Parses an if statement with condition and loop block
	 * @param script script string reader to read from
	 * @return parsed while expression
	 */
	private static Statement parseWhile(StringReader script){
		Expression condition = parseExpression(null, script, "^(do|\n)");
		List<Statement> statements = parseStatementList(script, "^(end)");
		return new While(condition, statements);
	}
	
	/**
	 * Parses a user class definition with inner definition block
	 * @param script script string reader to read from
	 * @return parsed class definition expression
	 */
	private static Statement parseClass(StringReader script){
		String className = script.readUntil("(\n)");
		script.skip(className.length());
		List<Statement> statements = parseStatementList(script, "^(end)"); 
		
		return new ClassDefinition(className,statements);
	}
	
	/**
	 * Parses a user method definition with inner definition block
	 * @param script script string reader to read from
	 * @return parsed class definition expression
	 */
	private static Method parseMethod(StringReader script){		
		List<String> argNames = parseMethodArgList(script);
		List<Statement> statements = parseStatementList(script, "^(end)"); 
		
		return new UserMethod(argNames, statements, true);
	}

	/**
	 * Parses a block definition with inner definition block
	 * @param script script string reader to read from
	 * @return parsed class definition expression
	 */
	private static MethodDefinition parseBlockDefinition(StringReader script){		
		List<String> argNames = parseMethodArgList(script);
		List<Statement> statements = parseStatementList(script, "^(})"); 
		
		return new MethodDefinition(new UserMethod( argNames, statements, false));
	}
	
	/**
	 * Reads the argument name list for a method definition
	 * @param script script string reader to read from
	 * @return List of the argument names
	 */
	private static List<String> parseMethodArgList(StringReader script){		
		List<String> argNames = new ArrayList<String>();
		boolean barSep = false;
		switch (script.currentChar()){
		case '|':
			barSep = true;
			//Fall through
		case '(':
			script.skip(1);
			String argList = script.readUntil(barSep ? "\\|" : "\\)");
			script.skip(argList.length()+1);
			argList = argList.trim();
			if (argList.length() != 0) {
				for (String argName : argList.split(",")){
					argNames.add(argName.trim());
				}
			}
			break;
		case '\n':
			break; //no args;
		}
		return argNames;
	}
	
}
