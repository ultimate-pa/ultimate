/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE SMTSolverBridge.
 *
 * The ULTIMATE SMTSolverBridge is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SMTSolverBridge is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SMTSolverBridge. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SMTSolverBridge, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SMTSolverBridge grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.io.IOException;
import java.io.StringReader;
import java.util.List;

import com.github.jhoenicke.javacup.runtime.SimpleSymbolFactory;
import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ConstantTermNormalizer;

/**
 * Class that provides auxiliary methods for transforming Strings into SMT- {@link Term}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class TermParseUtils {

	private TermParseUtils() {
		// do not instantiate
	}

	/**
	 * Takes an SMT-Term given as a string and transforms it into our {@link Term} data structure. Each identifier in
	 * this term will be translated to a function symbol (or constant symbol) that is known to script (the first
	 * parameter). If no symbol with this name is known an {@link SMTLIBException} is thrown. This means especially that
	 * we cannot produce a {@link Term} that contains a free {@link TermVariable}. WARNING: This implementation is not
	 * very robust with respect to invalid input.
	 */
	public static Term parseTerm(final Script script, final String string) {

		final SimpleSymbolFactory symfactory = new SimpleSymbolFactory();
		final Lexer lexer = new Lexer(new StringReader(string));
		lexer.setSymbolFactory(symfactory);

		// Workaround1: split input manually into s-expressions
		final List<Symbol> sexpr;
		try {
			sexpr = Executor.parseSexpr(lexer);
		} catch (final IOException e) {
			throw new AssertionError("IOException but there is neither input nor output");
		}

		final Parser parser = new Parser();
		parser.setScript(script);
		// Workaround2: add special symbol which says that we want to read a term
		sexpr.add(0, new Symbol(LexerSymbols.GETTERM));
		parser.setAnswer(sexpr);
		try {
			final Symbol resultSymbol = parser.parse();
			final Term resultTerm = (Term) resultSymbol.value;
			return new ConstantTermNormalizer().transform(resultTerm);
		} catch (final SMTLIBException ex) {
			throw ex;
		} catch (final UnsupportedOperationException ex) {
			throw ex;
		} catch (final Exception ex) {
			throw new SMTLIBException("wrapping Exception", ex);
		}
	}

}
