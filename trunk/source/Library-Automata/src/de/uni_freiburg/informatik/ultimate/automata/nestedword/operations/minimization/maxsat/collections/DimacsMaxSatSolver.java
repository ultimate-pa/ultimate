/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;

/**
 * Partial MAX-SAT solver bridge to an external solver.
 * <p>
 * Communication happens via a DIMACS file of the following format (description inspired by the <a
 * href=http://www.maxsat.udl.cat/16/index.html>Max-SAT 2016 web page</a>):
 * <p>
 * <ol>
 * <li>The file can start with comments( lines beginning with the character 'c').</li>
 * <li>The parameters line is "p wcnf <i>V C W</i>" where <i>V</i> is the number of variables, <i>C</i> is the number of
 * clauses, and <i>W</i> is the maximum weight.</li>
 * <li>A clause with <i>n</i> variables is a one-line sequence "<i>w v1 ... vn</i> 0" where <i>w</i> is the weight
 * (which is 1 for soft clauses and <i>&gt;=W</i> for hard clauses) and the <i>vi</i> are distinct non-zero integers
 * between -<i>V</i> and <i>V</i>. A positive number denotes the corresponding variable, and a negative number denotes
 * the negation of the corresponding variable.</li>
 * </ol>
 * The weight of a clause (the first integer in the clause) must be positive and the sum of all soft clauses must be
 * smaller than 2^63. Hard clauses have weight greater or equal to <i>W</i> and soft clauses have weight 1. <i>W</i> is
 * always greater than the sum of the weights of violated soft clauses in the solution.
 * <p>
 * Note that the solver is hard-coded and must reside in the home folder.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <V>
 *            variable type
 */
public class DimacsMaxSatSolver<V> extends AbstractMaxSatSolver<V> {
	// flag for not actually using the solver but only producing an output file
	public static final boolean ONLY_PRODUCE_OUTPUT_FILE = false;

	private static final String LINE_SEPARATOR = System.lineSeparator();
	private static final String FILE_NAME_TMP = "dimacs.wcnf.tmp";
	private static final String EXTENSION = ".wcnf";
	private static final String PREFIX = "UAutomizer_";
	private static final String FILE_NAME_DEFAULT = "dimacs";
	private static final String ENCODING = "UTF-8";
	private static final boolean WRITE_TO_STD_OUT = false;

	private static final String AHMAXSAT_COMMAND = "./ahmaxsat-ls-1.68";

	private static final String RESULT_OUTPUT_BEGINNING = "s OPTIMUM FOUND";

	private static final String HEADER = getHeader(ONLY_PRODUCE_OUTPUT_FILE);
	private static final char BLANK = ' ';
	private static final char NEG = '-';
	private static final String END_LINE = " 0" + LINE_SEPARATOR;
	private static final String BLANK_STRING = " ";
	private static final CharSequence SOFT_CLAUSE_WEIGHT = "1 ";

	private static final Object[] EMPTY_ARRAY = new Object[0];

	private final String mFilename;
	private final Appendable mWriter;
	private final Map<V, String> mVar2NumberString;
	private final ArrayList<V> mNumber2Var;
	private Map<V, Boolean> mVar2Assignment;

	/**
	 * @param services
	 *            Ultimate services.
	 */
	public DimacsMaxSatSolver(final AutomataLibraryServices services) {
		this(services, FILE_NAME_DEFAULT);
	}

	/**
	 * @param services
	 *            Ultimate services.
	 * @param filename
	 *            file name
	 */
	public DimacsMaxSatSolver(final AutomataLibraryServices services, final String filename) {
		super(services);
		mFilename = PREFIX + filename + EXTENSION;
		mWriter = createWriter();
		mVar2NumberString = new HashMap<>();
		mNumber2Var = new ArrayList<>();
	}

	@Override
	public void addVariable(final V var) {
		mVar2NumberString.put(var, Integer.toString(getNumberOfVariables() + 1));
		mNumber2Var.add(var);
	}

	@SuppressWarnings("unchecked")
	@Override
	public void addHornClause(final V[] negativeAtoms, final V positiveAtom) {
		final V[] positiveAtoms;
		if (positiveAtom == null) {
			positiveAtoms = (V[]) EMPTY_ARRAY;
		} else {
			positiveAtoms = (V[]) new Object[] { positiveAtom };
		}
		addClause(negativeAtoms, positiveAtoms);
	}

	@Override
	public void addClause(final V[] negativeAtoms, final V[] positiveAtoms) {
		++mClauses;
		try {
			// do not add the weight here, this will be done in a later stage

			for (final V var : negativeAtoms) {
				mWriter.append(BLANK).append(NEG).append(mVar2NumberString.get(var));
			}
			for (final V var : positiveAtoms) {
				mWriter.append(BLANK).append(mVar2NumberString.get(var));
			}
			mWriter.append(END_LINE);
		} catch (final IOException e) {
			throw new AssertionError(e);
		}
	}

	@Override
	public boolean solve() throws AutomataOperationCanceledException {
		try {
			((Writer) mWriter).close();
		} catch (final IOException e) {
			throw new AssertionError(e);
		}

		fixFile();

		if (ONLY_PRODUCE_OUTPUT_FILE) {
			return true;
		}
		// run external Max-SAT solver
		final ArrayList<String> commands = new ArrayList<>(1);
		commands.add(AHMAXSAT_COMMAND);
		commands.add(mFilename);
		final ProcessBuilder pb = new ProcessBuilder(commands);
		/* we could set the path via "pb.directory(...)" */
		// run solver
		final Process p;
		try {
			p = pb.start();
		} catch (final IOException e) {
			throw new AssertionError(e);
		}

		return parseResult(p.getInputStream());
	}

	private static Writer createWriter() {
		if (WRITE_TO_STD_OUT) {
			return new BufferedWriter(new OutputStreamWriter(System.out));
		}

		try {
			return new OutputStreamWriter(new FileOutputStream(FILE_NAME_TMP), ENCODING);
		} catch (final IOException e) {
			throw new AssertionError(e);
		}
	}

	@SuppressWarnings("squid:S1141")
	private void fixFile() {
		// new, final file
		final String hardClauseWeight = Integer.toString(getNumberOfVariables() + 1);
		try (Writer writer = new OutputStreamWriter(new FileOutputStream(mFilename), ENCODING)) {
			// add header
			// @formatter:off
			writer.append(HEADER)
					.append(Integer.toString(getNumberOfVariables()))
					.append(BLANK)
					.append(Integer.toString(mClauses))
					.append(BLANK)
					.append(hardClauseWeight)
					.append(LINE_SEPARATOR);
			// @formatter:on

			// copy hard clauses
			try (Scanner scanner = new Scanner(new File(FILE_NAME_TMP), ENCODING)) {
				scanner.useDelimiter(LINE_SEPARATOR);
				while (scanner.hasNext()) {
					final String line = scanner.next();
					writer.append(hardClauseWeight).append(line).append(LINE_SEPARATOR);
				}
			} catch (final FileNotFoundException e) {
				throw new AssertionError(e);
			}

			// add soft clauses
			addSoftClauses(writer);
		} catch (final IOException e) {
			throw new AssertionError(e);
		}
	}

	private void addSoftClauses(final Writer writer) throws IOException {
		for (final String var : mVar2NumberString.values()) {
			writer.append(SOFT_CLAUSE_WEIGHT).append(var).append(END_LINE);
		}
	}

	private boolean parseResult(final InputStream inputStream) {
		mVar2Assignment = new HashMap<>(mVar2NumberString.size());

		try (Scanner scanner = new Scanner(inputStream, ENCODING)) {
			// find beginning of result output
			scanner.useDelimiter(LINE_SEPARATOR);
			while (scanner.hasNext()) {
				final String line = scanner.next();
				if (line.startsWith(RESULT_OUTPUT_BEGINNING)) {
					break;
				}
			}

			// parse result output
			scanner.useDelimiter(BLANK_STRING);
			if (scanner.hasNext()) {
				// ignore line beginning "v "
				scanner.next();
			}
			while (scanner.hasNext()) {
				final String literal = scanner.next();
				if (literal.startsWith(LINE_SEPARATOR)) {
					break;
				}
				int num = Integer.parseInt(literal);
				final Boolean isPositive;
				if (num < 0) {
					num = -num;
					isPositive = Boolean.FALSE;
				} else {
					isPositive = Boolean.TRUE;
				}
				// our numbers start at zero
				num--;
				final V var = mNumber2Var.get(num);
				mVar2Assignment.put(var, isPositive);
			}
		}

		return true;
	}

	@Override
	public Map<V, Boolean> getValues() {
		return mVar2Assignment;
	}

	@Override
	public VariableStatus getValue(final V var) {
		return VariableStatus.UNSET;
	}

	@Override
	public int getNumberOfVariables() {
		return mVar2NumberString.size();
	}

	@Override
	public int getNumberOfClauses() {
		return mClauses;
	}

	@Override
	protected Boolean getPersistentAssignment(final V var) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected void log() {
		throw new UnsupportedOperationException();
	}

	@Override
	protected VariableStatus getTemporaryAssignment(final V var) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected void backtrack(final V var) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected void makeAssignmentPersistent() {
		throw new UnsupportedOperationException();
	}

	@Override
	protected void setVariable(final V var, final boolean newStatus) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected void decideOne() {
		throw new UnsupportedOperationException();
	}

	private static String getHeader(final boolean onlyProduceOutputFile) {
		final String header;
		if (onlyProduceOutputFile) {
			// add benchmark header
			header = "c This file belongs to a set of benchmarks that was produced by a minimization \n"
					+ "c of visibly pushdown automata [1, 2]. This minimization encodes the existence \n"
					+ "c of an equivalence relation that is suitable for quotienting. The more soft \n"
					+ "c clauses can be set to true, the more pairs of states can be merged. The \n"
					+ "c input automata were produced by applying the interprocedural analysis [3] \n"
					+ "c of the software verifier Ultimate Automizer [4, 5] to C programs from \n"
					+ "c the SV-COMP 2016 [6].\n" + "c\n"
					+ "c License \"https://creativecommons.org/licenses/by/4.0/\"\n" + "c\n" + "c 2017-05-22, \n"
					+ "c Matthias Heizmann (heizmann@informatik.uni-freiburg.de)\n"
					+ "c Christian Schilling (schillic@informatik.uni-freiburg.de)\n" + "c\n"
					+ "c [1] Matthias Heizmann, Christian Schilling, Daniel Tischner:\n"
					+ "c Minimization of Visibly Pushdown Automata Using Partial Max-SAT.\n"
					+ "c TACAS (1) 2017: 461-478\n"
					+ "c [2] https://ultimate.informatik.uni-freiburg.de/automata_library\n"
					+ "c [3] Matthias Heizmann, Jochen Hoenicke, Andreas Podelski:\n"
					+ "c Nested interpolants. POPL 2010: 471-482\n"
					+ "c [4] Matthias Heizmann, Jochen Hoenicke, Andreas Podelski:\n"
					+ "c Software Model Checking for People Who Love Automata.\n" + "c CAV 2013: 36-52\n"
					+ "c [5] Matthias Heizmann, Yu-Fang Chen, Daniel Dietsch, Marius Greitschus,\n"
					+ "c Jochen Hoenicke, Yong Li, Alexander Nutz, Betim Musa, Christian Schilling,\n"
					+ "c Tanja Schindler, Andreas Podelski:\n"
					+ "c Ultimate Automizer and the Search for Perfect Interpolants - (Competition\n"
					+ "c Contribution).\n"
					+ "c TACAS (II) 2018: 447-451\n"
					+ "c [6] Dirk Beyer: Reliable and Reproducible Competition Results with \n"
					+ "c BenchExec and Witnesses (Report on SV-COMP 2016).\n" + "c TACAS 2016: 887-904\n"
					+ "p wcnf ";
		} else {
			header = "p wcnf ";
		}
		return header;
	}
}
