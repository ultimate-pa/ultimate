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

import java.io.*;

public class Main {
	public void usage() {
		System.err.println("java TreeBuilder.Main <options> <filename>");
		System.err.println("<options>:  -debug");
		System.err.println("            -ultimate");
		System.err.println("            -acsl");
	}

	public Main(String[] param) throws Exception {
		if (param.length == 0) {
			usage();
			System.exit(1);
			return;
		}
		Emit emitter = null;
		boolean debug = false;
		int i = 0;
		while (i < param.length) {
			if (param[i].equals("-debug")) {
				i++;
				debug = true;
			} else if (param[i].equals("-ultimate")) {
				i++;
				emitter = new UltimateEmit();
			} else if (param[i].equals("-ultimatenew")) {
				i++;
				emitter = new NewUltimateEmit();
			} else if (param[i].equals("-acsl")) {
				i++;
				emitter = new ACSLEmit();
			} else {
				break;
			}
		}
		
		if(emitter == null){
			emitter = new Emit();
		}
		
		for (; i < param.length; i++) {
			Lexer lexer = new Lexer(new FileReader(param[i]));
			parser p = new parser(lexer);
			p.setFileName(param[i]);
			Grammar grammar;
			if (debug)
				grammar = (Grammar) p.debug_parse().value;
			else
				grammar = (Grammar) p.parse().value;
			if (grammar == null) {
				System.err.println("Parse Error in file: " + param[i]);
				System.exit(1);
			}
			emitter.setGrammar(grammar);
			emitter.emitClasses();
		}
	}

	public static void main(String[] param) throws Exception {
		new Main(param);
	}

}
