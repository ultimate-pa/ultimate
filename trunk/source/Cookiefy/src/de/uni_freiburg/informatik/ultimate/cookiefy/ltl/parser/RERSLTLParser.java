package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.parser;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model.*;

/**
 * Provides a parser for the 'properties'-files from ISOLA 2012 / RERS
 * competition. Those files contain LTL formulas, that are formatted according
 * to the following instructions:
 * 
 * In the LTL formulae, the atomic propositions correspond to input and output
 * symbols, where the prefix i is used for input and o is used for output
 * symbols, to allow a clear distinction.
 * 
 * The LTL formulae are given in a standard syntax, making use of the following
 * temporal operators:
 * 
 * X φ (next): φ has to hold after the next step
 * 
 * F φ (eventually): φ has to hold at some point in the future (or now)
 * 
 * G φ (globally): φ has to hold always (including now)
 * 
 * φ U ψ (until): φ has to hold until ψ holds (which eventually occurs)
 * 
 * φ WU ψ (weak until): φ has to hold until ψ holds (which does not necessarily
 * occur)
 * 
 * φ R ψ (release): φ has to hold until ψ held in the previous step. *
 * Additionally, the boolean operators & (conjunction), | (disjunction) and !
 * (negation) are used.
 * 
 * Ex.: 
 * 
 * (G (! ((oZ & ! oY) & (F oY)) | (! oW U oY)))
 * 
 * output W does never occur between output Z and output Y
 * 
 * ----------------------------------------
 * 
 * 
 * @author dietsch
 * 
 */
public class RERSLTLParser {

	/**
	 * Creates a list of LTL formulas from a list of strings. Each string in
	 * this list of strings is considered a formula when it starts with "(".
	 * 
	 * @param input
	 *            The list of strings.
	 * @return
	 */
	public List<Formula> parse(List<String> input) {
		ArrayList<Formula> formulas = new ArrayList<Formula>();
		for (String line : input) {
			if (line.startsWith("(")) {
				formulas.add(parseRoot(line));
			}
		}
		return formulas;
	}

	/**
	 * Creates a list of LTL formulas from a list of strings. Each string in
	 * this list of strings is considered a formula when it starts with "(".
	 * 
	 * Also compares original input and pretty printed formulas with each other
	 * to test if the parser works correctly.
	 * 
	 * @param input
	 *            The list of strings.
	 * @return
	 */
	public List<Formula> testParse(List<String> input) {
		ArrayList<Formula> formulas = new ArrayList<Formula>();
		int i = 0;
		int j = 0;
		for (String line : input) {
			if (line.startsWith("(")) {
				i++;
				Formula f = parseRoot(line);

				formulas.add(f);

				if (!f.toString().equals(line)) {
					j++;
					System.out.println("Input " + line);
					System.out.println("Final " + f);
					System.out.println();
				}
			}
		}
		System.out.println(i - j + "/" + i + " samples correct");
		return formulas;
	}

	private Formula parseRoot(String input) {

		if (!input.startsWith("(") || !input.endsWith(")")) {
			input = "(" + input + ")";
		}

		int bracketCount = 0;
		int pos = 0;

		char currentChar = ' ';

		StringBuilder subformula = new StringBuilder();
		List<String> parts = new ArrayList<String>();

		while (true) {
			while (pos < input.length()) {
				currentChar = input.charAt(pos);
				// System.out.println(subformula.toString());
				if (currentChar != '(' && currentChar != ')') {
					break;
				}

				switch (currentChar) {
				case '(':
					if (bracketCount != 0) {
						subformula.append(currentChar);
					}
					bracketCount++;
					pos++;
					break;
				case ')':
					bracketCount--;
					if (bracketCount != 0) {
						subformula.append(currentChar);
					}
					pos++;
					break;
				default:
					break;
				}

			}

			if (bracketCount == 0) {
				String s = subformula.toString().trim();
				if (!s.isEmpty()) {
					parts.add(s);
				}
				break;
			} else if (bracketCount == 1) {
				switch (currentChar) {
				case 'i':
				case 'o':
					int literalBound = input.indexOf(" ", pos);
					if (literalBound == -1) {
						literalBound = input.indexOf(")", pos);
					}
					parts.add(input.substring(pos, literalBound).trim());
					pos = literalBound;
					break;

				case 'U':
				case 'R':
				case '|':
				case '&':
					parts.add(subformula.toString().trim());
					parts.add(String.valueOf(currentChar));
					subformula = new StringBuilder();
					pos++;
					break;

				case 'W':
					if (input.charAt(pos + 1) != 'U') {
						throw new IllegalStateException();
					}
					parts.add(subformula.toString().trim());
					parts.add("WU");
					subformula = new StringBuilder();
					pos = pos + 2;
					break;

				case 'X':
				case 'F':
				case 'G':
				case '!':
					parts.add(String.valueOf(currentChar));
					pos++;
					break;
				default:
					subformula.append(currentChar);
					pos++;
					break;
				}
			} else {
				subformula.append(currentChar);
				pos++;
			}

		}

		int partSize = parts.size();
		if (partSize == 2) {
			return constructFormula(parts.get(0), parts.get(1), parts.get(1));
		} else if (partSize < 2) {
			return constructLiteral(parts.get(0));
		} else {
			int op = -1;

			for (int i = 0; i < partSize; ++i) {
				String s = parts.get(i);
				if (s.equals("U"))
				{
					op = i;
					break;
				}
				else if (s.equals("R"))
				{
					op = i;
					break;
				}
				else if (s.equals("WU"))
				{
					op = i;
					break;
				}
				else if (s.equals("|"))
				{
					op = i;
					break;
				}
				else if (s.equals("&"))
				{
					op = i;
					break;
				}
				else if (s.equals("X"))
				{
					op = i;
					break;
				}
				else if (s.equals("F"))
				{
					op = i;
					break;
				}
				else if (s.equals("G"))
				{
					op = i;
					break;
				}
				else if (s.equals("!"))
				{
					if (op == -1) {
						op = i;
					}
				}
				else 
				{
					break;
				}
			}
			String operand1 = "";
			String oeprator = "";
			String operand2 = "";
			for (int i = 0; i < partSize; ++i) {
				if (i < op) {
					operand1 = operand1 + parts.get(i);
				} else if (i == op) {
					oeprator = parts.get(i);
				} else {
					operand2 = operand2 + parts.get(i);
				}
			}

			operand1 = operand1.trim();
			operand2 = operand2.trim();

			return constructFormula(oeprator, operand1, operand2);

		}
	}

	private Formula constructFormula(String operator, String operand1,
			String operand2) {

		if (operand1.isEmpty()) {
			operand1 = operand2;
		}
		if (operand2.isEmpty()) {
			operand2 = operand1;
		}
		if (operator.equals("U"))
				return new Until(parseRoot(operand1), parseRoot(operand2));
		else if (operator.equals("R"))
				return new Release(parseRoot(operand1), parseRoot(operand2));
		else if (operator.equals("WU"))
				return new WeakUntil(parseRoot(operand1), parseRoot(operand2));
		else if (operator.equals("|"))
				return new Or(parseRoot(operand1), parseRoot(operand2));
		else if (operator.equals("&"))
				return new And(parseRoot(operand1), parseRoot(operand2));
		else if (operator.equals("X"))
				return new Next(parseRoot(operand2));
		else if (operator.equals("F"))
				return new Finally(parseRoot(operand2));
		else if (operator.equals("G"))
				return new Globally(parseRoot(operand2));
		else if (operator.equals("!"))
				return new Not(parseRoot(operand2));
		else 
			throw new IllegalArgumentException();
	}

	private Formula constructLiteral(String literal) {
		if (literal.isEmpty()) {
			return null;
		}

		if (literal.indexOf('!') != -1) {
			literal = literal.replace('!', ' ');
			literal = literal.trim();
			if (literal.startsWith("i")) {
				return new Not(new Literal(literal.substring(1),
						LiteralType.INPUT));
			} else {
				return new Not(new Literal(literal.substring(1),
						LiteralType.OUTPUT));
			}
		} else {
			literal = literal.trim();
			if (literal.startsWith("i")) {
				return new Literal(literal.substring(1), LiteralType.INPUT);
			} else {
				return new Literal(literal.substring(1), LiteralType.OUTPUT);
			}
		}
	}

}
