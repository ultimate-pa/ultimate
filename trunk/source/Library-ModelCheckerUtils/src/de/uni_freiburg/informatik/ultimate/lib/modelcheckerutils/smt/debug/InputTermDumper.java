/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.debug;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.TimerTask;
import java.util.zip.GZIPOutputStream;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * {@link InputTermDumper} is a {@link TimerTask} that can be used to dump a
 * term together with its assertion stack, theory and definitions.
 * 
 * For each dump, this class will create a file in the temp directory of your
 * system named <prefix><somerandomsymbols>.smt2.gz which can be decompressed by
 * using gunzip -d <filename>.
 * 
 * Use it together with {@link java.util.Timer} like this: <code>
 * 	Timer t = new Timer();
	t.schedule(new InputTermDumper(inputTerm, assertions, tempFilePrefix), timeInMilliSeconds);
 * </code>
 * 
 * Do not forget to call <code>t.cancel()</code> if you finish the original task
 * and no file should be dumped.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class InputTermDumper extends TimerTask {
	private final Term mInputTerm;
	private final Term[] mAssertions;
	private final String mPrefix;

	/**
	 * Create an {@link InputTermDumper}.
	 * 
	 * @param inputTerm
	 *            is the term you want to write to a file.
	 * @param assertions
	 *            is the current assertion stack. This may be null if you do not
	 *            want to print the assertion stack. Get it from
	 *            {@link Script#getAssertions()}.
	 * @param tempFilePrefix
	 *            is the prefix of the temporary file.
	 */
	public InputTermDumper(final Term inputTerm, final Term[] assertions, final String tempFilePrefix) {
		mInputTerm = inputTerm;
		mAssertions = assertions;
		mPrefix = tempFilePrefix;
	}

	@Override
	public void run() {

		try {
			final File file = File.createTempFile(mPrefix, ".smt2.gz");
			final PrintWriter printWriter = new PrintWriter(new GZIPOutputStream(new FileOutputStream(file)));
			final DeclarationAdder declAdder = new DeclarationAdder(printWriter);

			printWriter.append("(set-logic ").append(mInputTerm.getTheory().getLogic().toString()).append(")")
					.println();

			if (mAssertions != null && mAssertions.length > 0) {
				for (final Term assertion : mAssertions) {
					declAdder.transform(assertion);
					printWriter.append("(assert ").append(assertion.toString()).append(")").println();
				}
			}
			declAdder.transform(mInputTerm);
			printWriter.append("(simplify ").append(mInputTerm.toString()).append(")").println();

			printWriter.flush();
			printWriter.close();

		} catch (final IOException e) {
			e.printStackTrace();
		}
	}
}
