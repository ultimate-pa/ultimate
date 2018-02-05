/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Abstract superclass for automaton printers.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
@SuppressWarnings("squid:S1694")
public abstract class GeneralAutomatonPrinter {
	public static final char QUOTE = '\"';
	public static final String NEW_LINE = System.lineSeparator();

	private final PrintWriter mPrintWriter;
	private StringBuilder mStringBuilder;

	/**
	 * @param printWriter
	 *            Print writer to write to.
	 */
	protected GeneralAutomatonPrinter(final PrintWriter printWriter) {
		mPrintWriter = printWriter;
		mStringBuilder = new StringBuilder();
	}

	protected void finish() {
		final BufferedWriter bw = new BufferedWriter(mPrintWriter);
		try {
			bw.write(mStringBuilder.toString());
			bw.flush();
			mStringBuilder = new StringBuilder();
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}

	protected final void println(final String string) {
		mStringBuilder.append(string).append(CoreUtil.getPlatformLineSeparator());
	}

	protected final void println(final char character) {
		mStringBuilder.append(character).append(CoreUtil.getPlatformLineSeparator());
	}

	protected final void print(final String string) {
		mStringBuilder.append(string);
	}

	protected final void printElement(final String elem) {
		mStringBuilder.append(elem).append(' ');
	}

	protected final void print(final char character) {
		mStringBuilder.append(character);
	}

	protected final void print(final StringBuilder builder) {
		mStringBuilder.append(builder);
	}

	protected final void printAutomatonPrefix() {
		println(" = (");
	}

	protected final void printAutomatonSuffix() {
		println(");");
	}

	protected final void printValues(final Map<?, String> alphabet) {
		printCollection(alphabet.values());
	}

	private void printCollection(final Collection<String> collection) {
		for (final String string : collection) {
			printElement(string);
		}
	}

	private static String getCollectionPrefix(final String string) {
		return String.format("\t%s = {", string);
	}

	protected final void printCollectionPrefix(final String string) {
		print(getCollectionPrefix(string));
	}

	protected final void printlnCollectionPrefix(final String string) {
		println(getCollectionPrefix(string));
	}

	private static String replaceBackslashes(final Object input) {
		return input.toString().replaceAll("\"", "\\\"");
	}

	protected static final String quoteAndReplaceBackslashes(final Object input) {
		return QUOTE + replaceBackslashes(input) + QUOTE;
	}

	protected static final String quoteAndReplaceBackslashes(final Object input, final String suffix) {
		return QUOTE + replaceBackslashes(input) + suffix + QUOTE;
	}

	protected final void printCollectionSuffix() {
		println("},");
	}

	protected final void printOneTransitionPrefix() {
		print("\t\t(");
	}

	protected final void printOneTransitionSuffix() {
		println(')');
	}

	protected final void printTransitionsSuffix() {
		print("\t}");
	}

	protected final void printTransitionListSeparator() {
		println(",");
	}

	protected final void printLastTransitionLineSeparator() {
		println("");
	}

}
