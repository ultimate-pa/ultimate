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
		Emit emitter = new Emit();
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
