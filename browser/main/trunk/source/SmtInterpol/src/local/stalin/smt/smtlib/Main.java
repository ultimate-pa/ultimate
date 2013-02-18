package local.stalin.smt.smtlib;

import java.io.FileReader;
import java.io.InputStreamReader;
import java.io.Reader;

import org.apache.log4j.ConsoleAppender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.SimpleLayout;


import local.stalin.logic.Formula;
import local.stalin.smt.convert.ConvertFormula;
import local.stalin.smt.dpll.DPLLEngine;

public class Main {
	private static void usage() {
		System.err.println("USAGE smtinterpol [-q] [-v] [file.smt]");
	}
	
	public static void main(String[] param) throws Exception {
		Logger logger = Logger.getRootLogger();
		SimpleLayout layout = new SimpleLayout();
        logger.addAppender(new ConsoleAppender(layout));
        // ALL | DEBUG | INFO | WARN | ERROR | FATAL | OFF:
        Level logLevel = Level.INFO;
        int paramctr = 0;
        while (paramctr < param.length
        		&& param[paramctr].startsWith("-")) {
        	if (param[paramctr].equals("--")) {
        		paramctr++;
        		break;
        	} else if (param[paramctr].equals("-v")) {
        		logLevel = Level.DEBUG;
        		paramctr++;
        	} else if (param[paramctr].equals("-q")) {
        		logLevel = Level.WARN;
        		paramctr++;
        	} else {
        		usage();
        		return;
        	}
        }
        logger.setLevel(logLevel);
		MySymbolFactory symfactory = new MySymbolFactory();
		Reader reader;
		String filename;
		if (paramctr < param.length) {
			filename = param[paramctr++];
			reader = new FileReader(filename);
		} else {
			filename = "<stdin>";
			reader = new InputStreamReader(System.in);
		}
		if (paramctr != param.length) {
			usage();
			return;
		}
		Lexer lexer = new Lexer(reader);
		lexer.setSymbolFactory(symfactory);
		Parser parser = new Parser(lexer, symfactory);
		parser.setFileName(filename);
		Benchmark b = (Benchmark) parser.parse().value;

		DPLLEngine engine = new DPLLEngine(b.getTheory(),logger);
		ConvertFormula converter = new ConvertFormula(engine);
		for (Formula f : b.getFormulae())
			converter.addFormula(f);
		converter.close();
		//engine.dumpClausesSMTLIB();
		if (engine.solve()) {
			System.out.println("sat");
		} else {
			System.out.println("unsat");
			Formula[] interpolants = engine.getInterpolants();
			for (int i = 0; i < interpolants.length; i++) {
				System.out.println("Interpolant "+i+": "+interpolants[i]);
			}
		}
	}
}
