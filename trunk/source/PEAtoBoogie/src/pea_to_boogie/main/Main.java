/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package pea_to_boogie.main;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogieOutput;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import pea.PhaseEventAutomata;
import pea.modelchecking.PEAXML2JConverter;
import pea_to_boogie.translator.Translator;
import req_to_pea.ReqToPEA;
import srParse.srParsePattern;

public class Main {

	public static void main(final String args[]) {
		if (args.length < 2) {
			System.err.println("USAGE: pea_to_boogie.main file.req {file.bpl combinationNumber | file.xml}");
			return;
		}

		final Translator translator = new Translator(ILogger.getLogger(""));

		if (args[0].endsWith(".req") && args[1].endsWith(".bpl") && args.length == 3) {
			final String reqFilePath = args[0];
			final String boogieFilePath = args[1];
			final int combinationNum = Integer.parseInt(args[2]);
			final srParsePattern[] patterns = new ReqToPEA(ILogger.getLogger("")).genPatterns(reqFilePath);
			if (!(1 <= combinationNum & combinationNum <= patterns.length)) {
				throw new IllegalArgumentException("The valid range of combinationNum is integers in [1, pea.length].");
			}
			translator.setCombinationNum(combinationNum);
			final Unit unit = translator.genBoogie(patterns);
			try {
				final PrintWriter pWriter = new PrintWriter(new FileWriter(boogieFilePath));
				final BoogieOutput boogie_out = new BoogieOutput(pWriter);
				boogie_out.printBoogieProgram(unit);
				System.out.println("==================================================");
				System.out.println("Translation to Boogie code in " + args[1] + " is done!");
				System.out.println("==================================================");
			} catch (final IOException ex) {
				ex.printStackTrace();
			}
		} else if (args[0].endsWith(".req") && args[1].endsWith(".xml")) {
			final String reqFilePath = args[0];
			final String xmlFilePath = args[1];
			final srParsePattern[] patterns = new ReqToPEA(ILogger.getLogger("")).genPatterns(reqFilePath);
			new ReqToPEA(ILogger.getLogger("")).genPEAforUPPAAL(patterns, xmlFilePath);
			System.out.println("==================================================");
			System.out.println("Translation to Uppaal xml in " + args[1] + " is done!");
			System.out.println("==================================================");
		} else if (args[0].endsWith(".xml") && args[1].endsWith(".bpl") && args.length == 3) {
			final String peaFilePath = args[0];
			final int combinationNum = Integer.parseInt(args[2]);
			try {
				final PEAXML2JConverter xml2jconverter = new PEAXML2JConverter(false);
				final PhaseEventAutomata[] pea = xml2jconverter.convert(peaFilePath);
				if (!(1 <= combinationNum & combinationNum <= pea.length)) {
					throw new IllegalArgumentException(
							"The valid range of combinationNum is integers in [1, pea.length].");
				}
				translator.setCombinationNum(combinationNum);
				translator.genBoogie(pea);
			} catch (final Exception e) {
				e.printStackTrace();
			}
		} else {
			System.err.println("USAGE: pea_to_boogie.main file.req {file.bpl combinationNumber | file.xml}");
		}

	}
}
