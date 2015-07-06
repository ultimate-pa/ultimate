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