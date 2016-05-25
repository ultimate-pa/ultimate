/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IndexedStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.DataflowDAG;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.TraceCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

public class ReachDefTrace {

	private final ILogger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final BoogieSymbolTable mSymbolTable;

	public ReachDefTrace(IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider,
			IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider, ILogger logger, BoogieSymbolTable symboltable) {
		mLogger = logger;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
		mSymbolTable = symboltable;
	}

	public List<DataflowDAG<TraceCodeBlock>> process(List<CodeBlock> trace) throws Throwable {

		final List<CodeBlock> traceCopy = new ArrayList<>(trace);

		annotateReachingDefinitions(traceCopy);
		final List<BlockAndAssumes> assumes = findAssumes(traceCopy);
		final List<DataflowDAG<TraceCodeBlock>> rtr = buildDAG(traceCopy, assumes);

		//TODO: Optimize by checking the DAGs for uniqueness 
		
		if (mLogger.isDebugEnabled()) {
			final StringBuilder sb = new StringBuilder();
			for (final CodeBlock letter : traceCopy) {
				sb.append("[").append(letter).append("] ");
			}
			mLogger.debug("RD DAGs for " + sb);
			mLogger.debug("#" + rtr.size() + " DAGs constructed");
			printDebugForest(rtr);
		}

		return rtr;

	}

	private List<DataflowDAG<TraceCodeBlock>> buildDAG(List<CodeBlock> trace, List<BlockAndAssumes> assumeContainers) {
		final List<DataflowDAG<TraceCodeBlock>> rtr = new ArrayList<>();
		for (final BlockAndAssumes assumeContainer : assumeContainers) {
			for (final AssumeStatement stmt : assumeContainer.getAssumes()) {
				rtr.add(buildDAG(trace, assumeContainer, stmt));
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Finished " + BoogiePrettyPrinter.print(stmt));
				}
			}
		}
		return rtr;
	}

	/**
	 * Construct a {@link DataflowDAG} from the uses of a trace. The root node
	 * is
	 * 
	 * @param trace
	 * @param assumeContainer
	 * @param assume
	 * @return
	 */
	private DataflowDAG<TraceCodeBlock> buildDAG(List<CodeBlock> trace, BlockAndAssumes assumeContainer,
			AssumeStatement assume) {
		final LinkedList<DataflowDAG<TraceCodeBlock>> store = new LinkedList<>();

		DataflowDAG<TraceCodeBlock> current = new DataflowDAG<TraceCodeBlock>(new TraceCodeBlock(trace,
				assumeContainer.getBlock(), assumeContainer.getIndex()));
		final DataflowDAG<TraceCodeBlock> root = current;
		store.add(current);

		while (!store.isEmpty()) {

			current = store.removeFirst();
			mLogger.debug("Current: " + current.toString());

			final Set<Entry<ScopedBoogieVar, HashSet<IndexedStatement>>> uses = getUse(current);
			if (uses.isEmpty()) {
				mLogger.debug("Uses are empty");
			}
			for (final Entry<ScopedBoogieVar, HashSet<IndexedStatement>> use : uses) {
				for (final IndexedStatement stmt : use.getValue()) {
					final TraceCodeBlock nextBlock = getBlockContainingStatement(trace, stmt);
					assert nextBlock != null;
					assert nextBlock.getBlock() != null;
					final DataflowDAG<TraceCodeBlock> next = new DataflowDAG<TraceCodeBlock>(nextBlock);

					if (current.getNodeLabel().equals(next.getNodeLabel())) {
						mLogger.debug("Staying in the same block; no need to add dependency");
						continue;
					}
					current.connectOutgoing(next, use.getKey());
					store.addFirst(next); // use last for BFS
					mLogger.debug("Adding: " + next.toString());
				}
			}
		}
		return root;
	}

	private TraceCodeBlock getBlockContainingStatement(List<CodeBlock> trace, final IndexedStatement stmt) {
		final StatementFinder finder = new StatementFinder();
		final ISearchPredicate<Statement> predicate = new ISearchPredicate<Statement>() {
			@Override
			public boolean is(Statement object) {
				return object.equals(stmt.getStatement());
			}
		};

		final int pos = Integer.valueOf(stmt.getKey());
		final CodeBlock current = trace.get(pos);
		final List<Statement> lil = finder.start(current, predicate);
		if (!lil.isEmpty()) {
			return new TraceCodeBlock(trace, current, pos);
		}
		return null;
	}

	private Set<Entry<ScopedBoogieVar, HashSet<IndexedStatement>>> getUse(DataflowDAG<TraceCodeBlock> current) {
		final String key = String.valueOf(current.getNodeLabel().getIndex());
		final CodeBlock block = current.getNodeLabel().getBlock();
		final ReachDefEdgeAnnotation annot = mEdgeProvider.getAnnotation(block, key);
		assert annot != null;
		assert annot.getKey().equals(key);
		final HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> use = annot.getUse();
		assert use != null;
		return use.entrySet();
	}

	private void annotateReachingDefinitions(List<CodeBlock> trace) {
		final ScopedBoogieVarBuilder builder = new ScopedBoogieVarBuilder(mSymbolTable);
		for (int i = 0; i < trace.size(); i++) {
			CodeBlock predecessor = null;
			final CodeBlock current = trace.get(i);
			if (i != 0) {
				predecessor = trace.get(i - 1);
			}
			assert checkElement(current);
			new ReachDefTraceVisitor(mStatementProvider, mEdgeProvider, predecessor, mLogger, builder, i)
					.process(current);
		}
	}

	private boolean checkElement(CodeBlock current) {
		if (current instanceof StatementSequence) {
			final StatementSequence ss = (StatementSequence) current;
			return ss.getStatements().size() < 2;
		} else if (current instanceof Call) {
			return true;
		} else if (current instanceof Return) {
			return true;
		} else if (current instanceof SequentialComposition) {
			final SequentialComposition sc = (SequentialComposition) current;
			for (final CodeBlock cb : sc.getCodeBlocks()) {
				if (!checkElement(cb)) {
					return false;
				}
			}
			return true;
		}
		// everything else is not supported
		return false;
	}

	private List<BlockAndAssumes> findAssumes(List<CodeBlock> trace) {
		final List<BlockAndAssumes> rtr = new ArrayList<>();
		final StatementFinder visitor = new StatementFinder();
		final ISearchPredicate<Statement> predicate = new ISearchPredicate<Statement>() {
			@Override
			public boolean is(Statement object) {
				return object instanceof AssumeStatement;
			}
		};

		int i = 0;
		for (final CodeBlock block : trace) {
			final List<AssumeStatement> assumes = new ArrayList<>();
			for (final Statement stmt : visitor.start(block, predicate)) {
				assumes.add((AssumeStatement) stmt);
			}

			if (!assumes.isEmpty()) {
				rtr.add(new BlockAndAssumes(assumes, i, block));
			}
			++i;
		}
		return rtr;
	}

	private void printDebugForest(List<DataflowDAG<TraceCodeBlock>> forest) {
		if (forest == null) {
			return;
		}

		for (final DataflowDAG<TraceCodeBlock> dag : forest) {
			dag.printGraphDebug(mLogger);
		}
	}

	/**
	 * Container class holding a codeblock, all the assume statements contained
	 * in it and the index of the codeblock in the currently processed trace.
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 *
	 */
	private class BlockAndAssumes {

		private final List<AssumeStatement> mAssumes;
		private final int mIndex;
		private final CodeBlock mBlock;

		public BlockAndAssumes(List<AssumeStatement> assumes, int index, CodeBlock block) {
			mAssumes = assumes;
			mIndex = index;
			mBlock = block;
		}

		public List<AssumeStatement> getAssumes() {
			return mAssumes;
		}

		public int getIndex() {
			return mIndex;
		}

		public CodeBlock getBlock() {
			return mBlock;
		}

	}

	private class StatementFinder extends RCFGEdgeVisitor {
		private List<Statement> mStatements;
		private ISearchPredicate<Statement> mPredicate;

		@Override
		protected void visit(StatementSequence c) {
			for (final Statement stmt : c.getStatements()) {
				if (mPredicate.is(stmt)) {
					mStatements.add(stmt);
				}
			}
			super.visit(c);
		}

		public List<Statement> start(CodeBlock block, ISearchPredicate<Statement> predicate) {
			mStatements = new ArrayList<>();
			mPredicate = predicate;
			visit(block);
			return mStatements;
		}
	}

	public interface ISearchPredicate<T> {
		boolean is(T object);
	}

}
