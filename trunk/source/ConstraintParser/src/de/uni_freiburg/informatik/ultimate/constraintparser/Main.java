/*
 * Copyright (C) 2012-2015 Sergiy Bogomolov
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ConstraintParser plug-in.
 * 
 * The ULTIMATE ConstraintParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ConstraintParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ConstraintParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ConstraintParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ConstraintParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
