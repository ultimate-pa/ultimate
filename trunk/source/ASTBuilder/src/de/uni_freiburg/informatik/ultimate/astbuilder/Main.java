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

@SuppressWarnings("squid:S106")
public final class Main {

	private Main() {
		// prevent instantiation of the main class
	}

	public static void main(final String[] param) {
		if (param.length == 0) {
			usage();
			System.exit(1);
			return;
		}
		Emit emitter = null;
		boolean debug = false;
		int i = 0;
		while (i < param.length) {
			if ("-debug".equals(param[i])) {
				i++;
				debug = true;
			} else if ("-ultimatenew".equals(param[i])) {
				i++;
				emitter = new NewUltimateEmit();
			} else if ("-acsl".equals(param[i])) {
				i++;
				emitter = new ACSLEmit();
			} else {
				break;
			}
		}

		if (emitter == null) {
			emitter = new Emit();
		}

		for (; i < param.length; i++) {
			final Grammar grammar;
			try {
				grammar = parseParam(param, debug, i);
				if (grammar == null) {
					System.err.println("Parse Error in file: " + param[i]);
					System.exit(1);
				}
				emitter.setGrammar(grammar);
				emitter.emitClasses();
			} catch (final Exception e) {
				System.err.println("Parse Error in file: " + param[i] + ": " + e.getMessage());
				if (debug) {
					System.err.println(e);
				}
				System.exit(1);
				return;
			}
		}
	}

	private static Grammar parseParam(final String[] param, final boolean debug, final int i) throws Exception {
		final Lexer lexer = new Lexer(new FileReader(param[i]));
		final parser p = new parser(lexer);
		p.setFileName(param[i]);
		if (debug) {
			return (Grammar) p.debug_parse().value;
		} else {
			return (Grammar) p.parse().value;
		}
	}

	private static void usage() {
		System.err.println("java TreeBuilder.Main <options> <filename>");
		System.err.println("<options>:  -debug");
		System.err.println("            -ultimate");
		System.err.println("            -acsl");
	}
}
