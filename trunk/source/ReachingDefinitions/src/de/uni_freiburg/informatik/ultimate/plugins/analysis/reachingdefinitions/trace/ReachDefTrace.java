package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
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

	private final Logger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final BoogieSymbolTable mSymbolTable;

	public ReachDefTrace(IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider,
			IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider, Logger logger, BoogieSymbolTable symboltable) {
		mLogger = logger;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
		mSymbolTable = symboltable;
	}

	public List<DataflowDAG<TraceCodeBlock>> process(List<CodeBlock> trace) throws Throwable {

		List<CodeBlock> traceCopy = new ArrayList<>(trace);

		annotateReachingDefinitions(traceCopy);
		List<BlockAndAssumes> assumes = findAssumes(traceCopy);
		List<DataflowDAG<TraceCodeBlock>> rtr = buildDAG(traceCopy, assumes);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("#" + rtr.size() + " dataflow DAGs constructed");
			printDebugForest(rtr);
		}

		return rtr;

	}

	private List<DataflowDAG<TraceCodeBlock>> buildDAG(List<CodeBlock> trace, List<BlockAndAssumes> assumeContainers) {
		List<DataflowDAG<TraceCodeBlock>> rtr = new ArrayList<>();
		for (BlockAndAssumes assumeContainer : assumeContainers) {
			for (AssumeStatement stmt : assumeContainer.getAssumes()) {
				rtr.add(buildDAG(trace, assumeContainer, stmt));
			}
		}
		return rtr;
	}

	private DataflowDAG<TraceCodeBlock> buildDAG(List<CodeBlock> trace, BlockAndAssumes assumeContainer,
			AssumeStatement assume) {
		LinkedList<DataflowDAG<TraceCodeBlock>> store = new LinkedList<>();

		DataflowDAG<TraceCodeBlock> current = new DataflowDAG<TraceCodeBlock>(new TraceCodeBlock(trace,
				assumeContainer.getBlock(), assumeContainer.getIndex()));
		DataflowDAG<TraceCodeBlock> root = current;
		store.add(current);

		while (!store.isEmpty()) {

			current = store.removeFirst();
			mLogger.debug("Current: " + current.toString());

			Set<Entry<ScopedBoogieVar, HashSet<IndexedStatement>>> uses = getUse(current);
			if (uses.isEmpty()) {
				mLogger.debug("Uses are empty");
			}
			for (Entry<ScopedBoogieVar, HashSet<IndexedStatement>> use : uses) {
				for (IndexedStatement stmt : use.getValue()) {
					TraceCodeBlock nextBlock = getBlockContainingStatement(trace, stmt);
					assert nextBlock != null;
					assert nextBlock.getBlock() != null;
					DataflowDAG<TraceCodeBlock> next = new DataflowDAG<TraceCodeBlock>(nextBlock);

					if (current.getNodeLabel().equals(next.getNodeLabel())) {
						mLogger.debug("Samn");
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
		StatementFinder finder = new StatementFinder();
		ISearchPredicate<Statement> predicate = new ISearchPredicate<Statement>() {
			@Override
			public boolean is(Statement object) {
				return object.equals(stmt.getStatement());
			}
		};

		int pos = Integer.valueOf(stmt.getKey());
		CodeBlock current = trace.get(pos);
		List<Statement> lil = finder.start(current, predicate);
		if (!lil.isEmpty()) {
			return new TraceCodeBlock(trace, current, pos);
		}
		return null;
	}

	private Set<Entry<ScopedBoogieVar, HashSet<IndexedStatement>>> getUse(DataflowDAG<TraceCodeBlock> current) {
		String key = String.valueOf(current.getNodeLabel().getIndex());
		CodeBlock block = current.getNodeLabel().getBlock();
		ReachDefEdgeAnnotation annot = mEdgeProvider.getAnnotation(block, key);
		assert annot != null;
		assert annot.getKey().equals(key);
		HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> use = annot.getUse();
		assert use != null;
		return use.entrySet();
	}

	private void annotateReachingDefinitions(List<CodeBlock> trace) {
		ScopedBoogieVarBuilder builder = new ScopedBoogieVarBuilder(mSymbolTable);
		for (int i = 0; i < trace.size(); i++) {
			CodeBlock predecessor = null;
			CodeBlock current = trace.get(i);
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
			StatementSequence ss = (StatementSequence) current;
			return ss.getStatements().size() < 2;
		} else if (current instanceof Call) {
			return true;
		} else if (current instanceof Return) {
			return true;
		} else if (current instanceof SequentialComposition) {
			SequentialComposition sc = (SequentialComposition) current;
			for(CodeBlock cb : sc.getCodeBlocks()){
				if(!checkElement(cb)){
					return false;
				}
			}
			return true;
		}
		// everything else is not supported
		return false;
	}

	private List<BlockAndAssumes> findAssumes(List<CodeBlock> trace) {
		List<BlockAndAssumes> rtr = new ArrayList<>();
		StatementFinder visitor = new StatementFinder();
		ISearchPredicate<Statement> predicate = new ISearchPredicate<Statement>() {
			@Override
			public boolean is(Statement object) {
				return object instanceof AssumeStatement;
			}
		};

		int i = 0;
		for (CodeBlock block : trace) {
			List<AssumeStatement> assumes = new ArrayList<>();
			for (Statement stmt : visitor.start(block, predicate)) {
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

		for (DataflowDAG<TraceCodeBlock> dag : forest) {
			dag.printGraphDebug(mLogger);
		}
	}

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
			for (Statement stmt : c.getStatements()) {
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
