package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark;

//import java.io.IOException;
//import java.nio.charset.Charset;
//import java.nio.file.Files;
//import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
//import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
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
	private final Logger mLogger;
	private final Set<Integer> mLinenumbers;
//	private final Set<Integer> mForbiddenLines;

//	private int mActualFileLength;

	public LineCoverageCalculator(IUltimateServiceProvider services, IAutomaton<CodeBlock, IPredicate> automaton) {
		this(services, automaton, null);
	}

	public LineCoverageCalculator(IUltimateServiceProvider services, IAutomaton<CodeBlock, IPredicate> automaton,
			LineCoverageCalculator relative) {
		mServices = services;
		mRelative = relative;
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
//		mForbiddenLines = new HashSet<>();
//		mActualFileLength = -1;

		mLinenumbers = calculateLineNumbers2(automaton);
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
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID,
				new BenchmarkResult<>(Activator.s_PLUGIN_ID, description, new LineCoverageResult(total, current)));
	}

	private int getLineCount() {
		return mLinenumbers.size();
	}

//	private Set<Integer> calculateLineNumbers(IAutomaton<CodeBlock, IPredicate> automaton) {
//		final Set<Integer> rtr = new HashSet<>();
//		if (automaton == null) {
//			mLogger.warn("NULL automaton has no lines");
//			return rtr;
//		}
//
//		final Set<IPredicate> states = getStates(automaton);
//
//		for (final IPredicate state : states) {
//			final ProgramPoint[] points = getPoints(state);
//			for (final ProgramPoint point : points) {
//				final ILocation location = point.getBoogieASTNode().getLocation();
//				if (location == null) {
//					mLogger.warn("Skipping empty location for program point " + point);
//					continue;
//				}
//
//				addLines(rtr, location);
//			}
//		}
//		return rtr;
//	}

	private Set<Integer> calculateLineNumbers2(IAutomaton<CodeBlock, IPredicate> automaton) {
		final Set<Integer> rtr = new HashSet<>();
		if (automaton == null) {
			mLogger.warn("NULL automaton has no lines");
			return rtr;
		}

		final Set<CodeBlock> edges = getCodeblocks(automaton);

		for (final CodeBlock edge : edges) {
			if ("ULTIMATE.start".equals(edge.getPreceedingProcedure())) {
				continue;
			}
			final List<Statement> statements = getStatements(edge);
			for (final Statement stmt : statements) {
				final ILocation location = getLocation(stmt);
				if (location == null) {
					mLogger.warn("Skipping empty location for statement " + BoogiePrettyPrinter.print(stmt));
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
			CallStatement call = (CallStatement) stmt;
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

//	private boolean isValid(ILocation location) {
//		final int start = location.getStartLine();
//		final int end = location.getEndLine();
//		final int max = getActualFileLength(location);
//		if (start == 1 && end == max) {
//			// all locations that range over the whole file are invalid
//			return false;
//		}
//		return true;
//	}

//	private int getActualFileLength(ILocation location) {
//		if (mActualFileLength == -1) {
//			try {
//				List<String> content = Files.readAllLines(Paths.get(location.getFileName()), Charset.defaultCharset());
//				determineForbiddenLines(content);
//				mActualFileLength = determineActualFileLength(content.size());
//			} catch (IOException e) {
//				mActualFileLength = 0;
//			}
//		}
//		return mActualFileLength;
//	}

//	private int determineActualFileLength(int max) {
//		int largestBlankLine = Integer.MIN_VALUE;
//		for (final int line : mForbiddenLines) {
//			if (line > largestBlankLine) {
//				largestBlankLine = line;
//			}
//		}
//
//		if (largestBlankLine < max) {
//			largestBlankLine = max;
//		}
//
//		for (; largestBlankLine >= 0; largestBlankLine--) {
//			if (!mForbiddenLines.contains(largestBlankLine)) {
//				return largestBlankLine;
//			}
//		}
//
//		throw new UnsupportedOperationException();
//	}

//	private void determineForbiddenLines(List<String> content) {
//		int currentLine = 1;
//		for (String line : content) {
//			if (line.trim().isEmpty()) {
//				mForbiddenLines.add(currentLine);
//			}
//			++currentLine;
//		}
//	}

	private void addLines(Set<Integer> rtr, ILocation location) {
		final int start = location.getStartLine();
		final int end = location.getEndLine();

		if (start == end) {
			rtr.add(start);
		} else {
//			if (!isValid(location)) {
//				return;
//			}
//
//			for (int i = start; i <= end; i++) {
//				if (!mForbiddenLines.contains(i)) {
//					rtr.add(i);
//				}
//			}
		}
	}

//	private ProgramPoint[] getPoints(IPredicate state) {
//		if (state instanceof IMLPredicate) {
//			return ((IMLPredicate) state).getProgramPoints();
//		}
//
//		if (state instanceof ISLPredicate) {
//			return new ProgramPoint[] { ((ISLPredicate) state).getProgramPoint() };
//		}
//
//		mLogger.warn("Cannot calculate coverage for automaton containing predicates of type "
//				+ state.getClass().getSimpleName());
//
//		return new ProgramPoint[0];
//	}

//	private Set<IPredicate> getStates(IAutomaton<CodeBlock, IPredicate> automaton) {
//		if (automaton instanceof INestedWordAutomaton<?, ?>) {
//			return ((INestedWordAutomaton<CodeBlock, IPredicate>) automaton).getStates();
//		}
//
//		mLogger.warn("Cannot calculate coverage for unknown automaton of type " + automaton.getClass().getSimpleName());
//		return Collections.emptySet();
//	}

	private Set<CodeBlock> getCodeblocks(IAutomaton<CodeBlock, IPredicate> automaton) {
		Set<CodeBlock> rtr = new HashSet<>();
		if (automaton instanceof INestedWordAutomaton<?, ?>) {
			INestedWordAutomaton<CodeBlock, IPredicate> nwa = ((INestedWordAutomaton<CodeBlock, IPredicate>) automaton);
			Deque<IPredicate> open = new ArrayDeque<>();
			open.addAll(nwa.getInitialStates());
			while (!open.isEmpty()) {
				IPredicate current = open.removeFirst();
				addCodeblock(rtr, open, nwa.callSuccessors(current));
				addCodeblock(rtr, open, nwa.internalSuccessors(current));
				addCodeblock(rtr, open, nwa.returnSuccessors(current));
				addCodeblock(rtr, open, nwa.returnSummarySuccessor(current));
			}
		}
		return rtr;
	}

	private <T extends OutgoingTransitionlet<CodeBlock, IPredicate>> void addCodeblock(Set<CodeBlock> rtr,
			Deque<IPredicate> open, Iterable<T> iter) {
		for (OutgoingTransitionlet<CodeBlock, IPredicate> trans : iter) {
			if (rtr.add(trans.getLetter())) {
				open.addFirst(trans.getSucc());
			}
		}
	}

	private static final class StatementExtractor extends RCFGEdgeVisitor {

		private List<Statement> mStatements;

		private StatementExtractor() {
		}

		public List<Statement> process(RCFGEdge edge) {
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
			return ((double) mCurrent) / ((double) mMax);
		}

		@Override
		public String toString() {
			return new StringBuilder().append("Covered ").append(mCurrent).append(" Total ").append(mMax)
					.append(" Coverage ").append(getCoverage()).toString();
		}

	}

}
