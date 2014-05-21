package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
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
 * - computeInterpolantAutomaton überschreiben
 * - "Powerset" einstellung für refineAbstraction wählen
 */
//


public class TAwAFAsCegarLoop extends CegarLoopConcurrentAutomata {

	public TAwAFAsCegarLoop(String name, RootNode rootNode,
			SmtManager smtManager,
			TraceAbstractionBenchmarks traceAbstractionBenchmarks,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs,
			INTERPOLATION interpolation, boolean computeHoareAnnotation) {
		super(name, rootNode, smtManager, traceAbstractionBenchmarks, taPrefs,
				errorLocs);
		// TODO Auto-generated constructor stub
	}

	@Override
	protected void constructInterpolantAutomaton()
			throws OperationCanceledException {

		Word<CodeBlock> trace = m_TraceChecker.getTrace();
		for (int i = 0; i < trace.length(); i++) {
			CodeBlock cb = trace.getSymbol(i);
			RDCodeBlockWrapper rdcbw = new RDCodeBlockWrapper(cb);
			int j = 0;
			j++;
		}
		
//		super.constructInterpolantAutomaton();
		int i = 0;
	}

	
	
}
