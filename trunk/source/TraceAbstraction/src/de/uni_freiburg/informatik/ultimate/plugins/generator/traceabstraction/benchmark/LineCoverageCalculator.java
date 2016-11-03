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
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
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
 * Calculates "line coverage", i.e. the number of lines that are contained in an
 * automaton.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class LineCoverageCalculator {

	private final IUltimateServiceProvider mServices;
	private final LineCoverageCalculator mRelative;
	private final ILogger mLogger;
	private final Set<Integer> mLinenumbers;

	public LineCoverageCalculator(IUltimateServiceProvider services, IAutomaton<CodeBlock, IPredicate> automaton) {
		this(services, automaton, null);
	}

	public LineCoverageCalculator(IUltimateServiceProvider services, IAutomaton<CodeBlock, IPredicate> automaton,
			LineCoverageCalculator relative) {
		mServices = services;
		mRelative = relative;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);

		mLinenumbers = calculateLineNumbers(automaton);
	}

	public void reportCoverage(String description) {
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

	private void reportResult(int current, int total, String description) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new BenchmarkResult<>(Activator.PLUGIN_ID, description, new LineCoverageResult(total, current)));
	}

	private int getLineCount() {
		return mLinenumbers.size();
	}

	private Set<Integer> calculateLineNumbers(IAutomaton<CodeBlock, IPredicate> automaton) {
		final Set<Integer> rtr = new HashSet<>();
		if (automaton == null) {
			mLogger.warn("NULL automaton has no lines");
			return rtr;
		}

		final Set<CodeBlock> edges = getCodeblocks(automaton);

		for (final CodeBlock edge : edges) {
			if ("ULTIMATE.start".equals(edge.getPrecedingProcedure())) {
				continue;
			}
			final List<Statement> statements = getStatements(edge);
			for (final Statement stmt : statements) {
				final ILocation location = getLocation(stmt);
				if (location == null) {
					mLogger.warn("Skipping empty location or mult-line location for statement " + BoogiePrettyPrinter.print(stmt));
					continue;
				}
				addLines(rtr, location);
			}
		}
		return rtr;
	}

	private ILocation getLocation(Statement stmt) {
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

	private List<Statement> getStatements(CodeBlock edge) {
		return new StatementExtractor().process(edge);
	}

	private void addLines(Set<Integer> rtr, ILocation location) {
		final int start = location.getStartLine();
		final int end = location.getEndLine();

		if (start == end) {
			rtr.add(start);
		}
	}

	private Set<CodeBlock> getCodeblocks(IAutomaton<CodeBlock, IPredicate> automaton) {
		final Set<CodeBlock> rtr = new HashSet<>();
		if (automaton instanceof INestedWordAutomaton<?, ?>) {
			final INestedWordAutomaton<CodeBlock, IPredicate> nwa = ((INestedWordAutomaton<CodeBlock, IPredicate>) automaton);
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

	private <T extends IOutgoingTransitionlet<CodeBlock, IPredicate>> void addCodeblock(Set<CodeBlock> rtr,
			Deque<IPredicate> open, Iterable<T> iter) {
		for (final IOutgoingTransitionlet<CodeBlock, IPredicate> trans : iter) {
			if (rtr.add(trans.getLetter())) {
				open.addFirst(trans.getSucc());
			}
		}
	}

	private static final class StatementExtractor extends RCFGEdgeVisitor {

		private List<Statement> mStatements;

		private StatementExtractor() {
		}

		public List<Statement> process(IcfgEdge edge) {
			mStatements = new ArrayList<>();
			visit(edge);
			return mStatements;
		}

		@Override
		protected void visit(ParallelComposition c) {
			throw new UnsupportedOperationException("Cannot merge ParallelComposition");
		}

		@Override
		protected void visit(StatementSequence c) {
			mStatements.addAll(c.getStatements());
			super.visit(c);
		}

		@Override
		protected void visit(Call c) {
			mStatements.add(c.getCallStatement());
			super.visit(c);
		}

		@Override
		protected void visit(Return c) {
			mStatements.add(c.getCallStatement());
			super.visit(c);
		}
	}

	private static final class LineCoverageResult implements ICsvProviderProvider<String> {

		private final int mMax;
		private final int mCurrent;

		private LineCoverageResult(int max, int current) {
			mMax = max;
			mCurrent = current;
		}

		@Override
		public ICsvProvider<String> createCvsProvider() {
			final SimpleCsvProvider<String> provider = new SimpleCsvProvider<String>(Arrays.asList(new String[] {
					"Covered lines", "Total lines", "Line coverage", }));

			final List<String> values = new ArrayList<>();
			values.add(String.valueOf(mCurrent));
			values.add(String.valueOf(mMax));
			values.add(String.valueOf(getCoverage()));
			provider.addRow(values);

			return provider;
		}

		private double getCoverage() {
			return ((double) mCurrent) / ((double) mMax) * 1000;
		}

		@Override
		public String toString() {
			return new StringBuilder().append("Covered ").append(mCurrent).append(" Total ").append(mMax)
					.append(" Coverage ").append(getCoverage()).toString();
		}

	}

}
