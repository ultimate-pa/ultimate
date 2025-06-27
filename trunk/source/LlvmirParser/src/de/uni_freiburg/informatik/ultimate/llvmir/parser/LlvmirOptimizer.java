/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirParser plug-in.
 * It is used to optimize LLVM IR files to simplify the parsing process.
 *
 * The ULTIMATE LlvmirParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.llvmir.parser;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;

import de.uni_freiburg.informatik.ultimate.llvmir.parser.preferences.UltimateLlvmirParserPreferenceInitializer;

public class LlvmirOptimizer {
	protected static File optLlFile(final File file) throws IOException, InterruptedException {
		// clean the .ll file by removing "optnone" attributes
		final ByteArrayOutputStream cleanedLl = new ByteArrayOutputStream();
		try (BufferedReader reader = new BufferedReader(new FileReader(file));
				BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(cleanedLl))) {
			String line;
			while ((line = reader.readLine()) != null) {
				writer.write(line.replace("optnone", ""));
				writer.newLine();
			}
			writer.flush();
		}

		// create temporary output file for opt process
		final File outputFile = File.createTempFile("opt_output", ".ll");
		outputFile.deleteOnExit();

		// start opt process
		final ProcessBuilder opt = new ProcessBuilder(UltimateLlvmirParserPreferenceInitializer.DEF_OPT_PATH, "-S",
				"-passes=sroa,mem2reg,simplifycfg", "-o", outputFile.getAbsolutePath(), "-");
		final Process optProc = opt.start();

		// write cleaned .ll content to opt process
		try (OutputStream out = optProc.getOutputStream()) {
			cleanedLl.writeTo(out);
		}

		// wait for opt process to finish
		optProc.waitFor();

		return outputFile;
	}
}
