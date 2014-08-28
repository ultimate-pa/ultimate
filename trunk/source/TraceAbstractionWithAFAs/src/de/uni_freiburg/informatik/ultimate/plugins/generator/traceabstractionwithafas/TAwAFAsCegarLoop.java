package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.ReachingDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.DataflowDAG;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag.TraceCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.CegarLoopConcurrentAutomata;

/*
 * plan:
 * - von CegarLoopConcurrent erben
 *  --> Produktautomat aus einem parallelen Programm wird automatisch gebaut
 * - computeInterpolantAutomaton �berschreiben
 * - "Powerset" einstellung f�r refineAbstraction w�hlen
 */
//

public class TAwAFAsCegarLoop extends CegarLoopConcurrentAutomata {

	private final BoogieSymbolTable mSymbolTable;

	public TAwAFAsCegarLoop(String name, RootNode rootNode, SmtManager smtManager,
			TraceAbstractionBenchmarks traceAbstractionBenchmarks, TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs, INTERPOLATION interpolation, boolean computeHoareAnnotation,
			IUltimateServiceProvider services, BoogieSymbolTable table) {
		super(name, rootNode, smtManager, traceAbstractionBenchmarks, taPrefs, errorLocs, services);
		assert table != null;
		mSymbolTable = table;
	}

	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {

		Word<CodeBlock> trace = m_TraceChecker.getTrace();

		List<DataflowDAG<TraceCodeBlock>> dags = null;
		try {
			dags = ReachingDefinitions.computeRDForTrace(trace.asList(), mLogger,
					mSymbolTable);
		} catch (Throwable e) {
			mLogger.fatal("DataflowDAG generation threw an exception.", e);
		}

		mLogger.debug("Ich bin ein Breakpoint");

		// for (int i = 0; i < trace.length(); i++) {
		// CodeBlock cb = trace.getSymbol(i);
		// RDCodeBlockWrapper rdcbw = new RDCodeBlockWrapper(cb);
		// int j = 0;
		// j++;
		// }
		//
		// // super.constructInterpolantAutomaton();
		// int i = 0;
	}

}
