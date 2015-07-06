package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.debug;

import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public final class DeclarationAdder extends TermTransformer {
	private final Set<FunctionSymbol> mFuncSymbols;
	private final PrintWriter mWriter;

	public DeclarationAdder(final PrintWriter pw) {
		super();
		mWriter = pw;
		mFuncSymbols = new HashSet<>();
	}

	@Override
	protected void convert(Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol symbol = ((ApplicationTerm) term).getFunction();

			if (!symbol.isIntern() && mFuncSymbols.add(symbol)) {
				mWriter.append("(declare-fun ").append(symbol.getName()).append(" () ")
						.append(symbol.getReturnSort().toString()).append(")").println();
			}
		}
		super.convert(term);
	}
}