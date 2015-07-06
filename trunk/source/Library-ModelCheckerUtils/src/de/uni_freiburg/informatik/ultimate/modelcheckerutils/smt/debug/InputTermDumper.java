/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.debug;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.TimerTask;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class InputTermDumper extends TimerTask {
	private final Term mInputTerm;
	private final Term[] mAssertions;

	public InputTermDumper(final Term inputTerm, final Term[] assertions) {
		mInputTerm = inputTerm;
		mAssertions = assertions;
	}

	@Override
	public void run() {

		try {
			final File file = File.createTempFile("simplifiedTerm", "smt2");
			final PrintWriter printWriter = new PrintWriter(file);
			final DeclarationAdder declAdder = new DeclarationAdder(printWriter);

			printWriter.append("(set-logic ").append(mInputTerm.getTheory().getLogic().toString()).append(")")
					.println();

			for (final Term assertion : mAssertions) {
				declAdder.transform(assertion);
				printWriter.append("(assert ").append(assertion.toString()).append(")").println();
			}
			declAdder.transform(mInputTerm);
			printWriter.append("(simplify ").append(mInputTerm.toString()).append(")").println();

			printWriter.flush();
			printWriter.close();

		} catch (IOException e) {
			e.printStackTrace();
		}

	}
}