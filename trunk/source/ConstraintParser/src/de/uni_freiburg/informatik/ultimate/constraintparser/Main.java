package de.uni_freiburg.informatik.ultimate.constraintparser;

import java.io.FileReader;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.Reader;

import org.apache.log4j.ConsoleAppender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.SimpleLayout;


import de.uni_freiburg.informatik.ultimate.logic.Term;

public class Main {
	private static void usage() {
		System.err.println("USAGE constraintparser [-q] [-v] [file.txt]");
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
		PrintWriter writer;
		String filename;
		if (paramctr < param.length) {
			filename = param[paramctr++];
			reader = new FileReader(filename);
			writer = new PrintWriter(new FileWriter(filename+".smt"));
		} else {
			filename = "<stdin>";
			reader = new InputStreamReader(System.in);
			writer = new PrintWriter(System.out);
		}
		if (paramctr != param.length) {
			usage();
			return;
		}
		Lexer lexer = new Lexer(reader);
		lexer.setSymbolFactory(symfactory);
		Parser parser = new Parser(lexer, symfactory);
		parser.setFileName(filename);
		Term f = (Term) parser.parse().value;
		writer.println(f);
		writer.close();
	}
}
