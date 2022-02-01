/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ASTBuilder plug-in.
 *
 * The ULTIMATE ASTBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ASTBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ASTBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ASTBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ASTBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.astbuilder;

import java.io.FileReader;

/**
 * Runs the AST builder.
 */
@SuppressWarnings("squid:S106")
public final class Main {

	private static final String PARSE_ERROR_IN_FILE = "Parse Error in file: ";

	private Main() {
		// prevent instantiation of the main class
	}

	/**
	 * Main method.
	 *
	 * @param param
	 *            parameters
	 */
	@SuppressWarnings("checkstyle:com.puppycrawl.tools.checkstyle.checks.coding.IllegalCatchCheck")
	public static void main(final String[] param) {
		if (param.length == 0) {
			usage();
			System.exit(1);
			return;
		}
		Emit emitter = null;
		boolean debug = false;
		int idx = 0;
		while (idx < param.length) {
			if ("-debug".equals(param[idx])) {
				idx++;
				debug = true;
			} else if ("-crocotta".equals(param[idx])) {
				idx++;
				emitter = new CrocottaEmit();
			} else if ("-ultimatenew".equals(param[idx])) {
				idx++;
				emitter = new NewUltimateEmit();
			} else if ("-acsl".equals(param[idx])) {
				idx++;
				emitter = new ACSLEmit();
			} else {
				break;
			}
		}

		if (emitter == null) {
			emitter = new Emit();
		}

		for (; idx < param.length; idx++) {
			final Grammar grammar;
			try {
				grammar = parseParam(param[idx], debug);
				if (grammar == null) {
					System.err.println(PARSE_ERROR_IN_FILE + param[idx]);
					System.exit(1);
				}
				emitter.setGrammar(grammar);
				emitter.emitClasses();
			} catch (final Exception e) {
				System.err.println(PARSE_ERROR_IN_FILE + param[idx] + ": " + e.getMessage());
				if (debug) {
					System.err.println(e);
				}
				System.exit(1);
				return;
			}
		}
	}

	private static Grammar parseParam(final String param, final boolean debug) throws Exception {
		final Lexer lexer = new Lexer(new FileReader(param));
		final parser parser = new parser(lexer);
		parser.setFileName(param);
		if (debug) {
			return (Grammar) parser.debug_parse().value;
		}
		return (Grammar) parser.parse().value;
	}

	private static void usage() {
		System.err.println("java TreeBuilder.Main <options> <filename>");
		System.err.println("<options>:  -debug");
		System.err.println("            -ultimate");
		System.err.println("            -acsl");
	}
}
