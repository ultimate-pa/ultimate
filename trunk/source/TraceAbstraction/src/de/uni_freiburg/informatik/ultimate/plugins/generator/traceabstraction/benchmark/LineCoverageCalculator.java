/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * Calculates "line coverage", i.e. the number of lines that are contained in an automaton.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class LineCoverageCalculator<LETTER extends IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final LineCoverageCalculator<LETTER> mRelative;
	private final ILogger mLogger;
	private final Set<Integer> mLinenumbers;

	public LineCoverageCalculator(final IUltimateServiceProvider services,
			final IAutomaton<LETTER, IPredicate> automaton) {
		this(services, automaton, null);
	}

	public LineCoverageCalculator(final IUltimateServiceProvider services,
			final IAutomaton<LETTER, IPredicate> automaton, final LineCoverageCalculator<LETTER> relative) {
		mServices = services;
		mRelative = relative;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLinenumbers = calculateLineNumbers(automaton);
	}

	public void reportCoverage(final String description) {
		final int linecount = getLineCount();
		final String desc = "Line coverage for " + description;
		if (mRelative == null) {
			if (linecount == 0) {
				return;
			}
			reportResult(linecount, linecount, desc);
		} else {
			final int total = mRelative.getLineCount();
			if (total == 0) {
				return;
			}
			reportResult(linecount, total, desc);
		}
	}

	private void reportResult(final int current, final int total, final String description) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new StatisticsResult<>(Activator.PLUGIN_ID, description, new LineCoverageResult(total, current)));
	}

	private int getLineCount() {
		return mLinenumbers.size();
	}

	private Set<Integer> calculateLineNumbers(final IAutomaton<LETTER, IPredicate> automaton) {
		final Set<Integer> rtr = new HashSet<>();
		if (automaton == null) {
			mLogger.warn("NULL automaton has no lines");
			return rtr;
		}

		final Set<LETTER> edges = getCodeblocks(automaton);

		for (final LETTER edge : edges) {
			if ("ULTIMATE.start".equals(edge.getPrecedingProcedure())) {
				continue;
			}
			if (!(edge instanceof CodeBlock)) {
				throw new UnsupportedOperationException("Cannot work with edges that do not provide Boogie code");
			}
			rtr.addAll(calculateLineNumbers((CodeBlock) edge));
		}
		return rtr;
	}

	private Set<Integer> calculateLineNumbers(final CodeBlock cb) {
		final LineCoverageOfEdges stmtExtr = new LineCoverageOfEdges(mLogger);
		stmtExtr.process(cb);
		return stmtExtr.mLineNumbers;
	}

	private Set<LETTER> getCodeblocks(final IAutomaton<LETTER, IPredicate> automaton) {
		final Set<LETTER> rtr = new HashSet<>();
		if (automaton instanceof INestedWordAutomaton<?, ?>) {
			final INestedWordAutomaton<LETTER, IPredicate> nwa = (INestedWordAutomaton<LETTER, IPredicate>) automaton;
			final Deque<IPredicate> open = new ArrayDeque<>();
			open.addAll(nwa.getInitialStates());
			while (!open.isEmpty()) {
				final IPredicate current = open.removeFirst();
				addCodeblock(rtr, open, nwa.callSuccessors(current));
				addCodeblock(rtr, open, nwa.internalSuccessors(current));
				addCodeblock(rtr, open, nwa.returnSuccessors(current));
				addCodeblock(rtr, open, nwa.summarySuccessors(current));
			}
		}
		return rtr;
	}

	private <T extends IOutgoingTransitionlet<LETTER, IPredicate>> void addCodeblock(final Set<LETTER> rtr,
			final Deque<IPredicate> open, final Iterable<T> iter) {
		for (final IOutgoingTransitionlet<LETTER, IPredicate> trans : iter) {
			if (rtr.add(trans.getLetter())) {
				open.addFirst(trans.getSucc());
			}
		}
	}

	private static final class LineCoverageOfEdges extends RCFGEdgeVisitor {

		private final Set<Integer> mLineNumbers;
		private final ILogger mLogger;

		private LineCoverageOfEdges(final ILogger logger) {
			mLineNumbers = new HashSet<>();
			mLogger = logger;
		}

		private static ILocation getLocation(final Statement stmt) {
			if (stmt instanceof AssumeStatement) {
				return ((AssumeStatement) stmt).getFormula().getLocation();
			} else if (stmt instanceof CallStatement) {
				final CallStatement call = (CallStatement) stmt;
				if (call.getLocation().getStartLine() == call.getLocation().getEndLine()) {
					return call.getLocation();
				}
				return null;
			}
			return stmt.getLocation();
		}

		private void addLines(final Statement stmt) {
			final ILocation location = getLocation(stmt);
			if (location == null) {
				mLogger.warn("Skipping empty location or multi-line location for statement "
						+ BoogiePrettyPrinter.print(stmt));
				return;
			}

			final int start = location.getStartLine();
			final int end = location.getEndLine();

			if (start == end) {
				mLineNumbers.add(start);
			}
		}

		public void process(final IcfgEdge edge) {
			visit(edge);
		}

		@Override
		protected void visit(final ParallelComposition c) {
			for (final CodeBlock cb : c.getCodeBlocks()) {
				visit(cb);
			}
		}

		@Override
		protected void visit(final StatementSequence c) {
			for (final Statement stmt : c.getStatements()) {
				addLines(stmt);
			}
		}

		@Override
		protected void visit(final Call c) {
			addLines(c.getCallStatement());
		}

		@Override
		protected void visit(final Return c) {
			addLines(c.getCallStatement());
		}
	}

	private static final class LineCoverageResult implements ICsvProviderProvider<String> {

		private final int mMax;
		private final int mCurrent;

		private LineCoverageResult(final int max, final int current) {
			mMax = max;
			mCurrent = current;
		}

		@Override
		public ICsvProvider<String> createCsvProvider() {
			final SimpleCsvProvider<String> provider = new SimpleCsvProvider<>(
					Arrays.asList(new String[] { "Covered lines", "Total lines", "Line coverage", }));

			final List<String> values = new ArrayList<>();
			values.add(String.valueOf(mCurrent));
			values.add(String.valueOf(mMax));
			values.add(String.valueOf(getCoverage()));
			provider.addRow(values);

			return provider;
		}

		private double getCoverage() {
			return (double) mCurrent / (double) mMax * 1000;
		}

		@Override
		public String toString() {
			return new StringBuilder().append("Covered ").append(mCurrent).append(" Total ").append(mMax)
					.append(" Coverage ").append(getCoverage()).toString();
		}

	}

}
